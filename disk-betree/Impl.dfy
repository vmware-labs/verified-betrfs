include "Main.dfy"
include "../lib/Sets.dfy"
include "BetreeBlockCache.dfy"
include "BetreeBlockCacheSystem.dfy"
include "Marshalling.dfy"

module {:extern} Impl refines Main { 
  import BC = BetreeGraphBlockCache
  import BT = PivotBetreeSpec`Internal
  import DAM = BetreeBlockCacheSystem
  import Marshalling
  import Messages = ValueMessage
  import Pivots = PivotsLib
  import SSTable = SSTable
  import opened Sets
  import IS = ImplState

  import opened Maps
  import opened Sequences

  type Key = MS.Key
  type Message = Messages.Message

  type Constants = DAM.M.Constants
  type Variables = IS.Variables

  type HeapState = IS.ImplHeapState
  function HeapSet(hs: HeapState) : set<object> { IS.ImplHeapSet(hs) }

  function Ik(k: Constants) : DAM.M.Constants { k }
  function I(k: Constants, hs: HeapState) : DAM.M.Variables { IS.IVars(hs.s) }

  predicate ValidSector(sector: Sector)
  {
    && Marshalling.parseSector(sector).Some?
  }

  function ISector(sector: Sector) : DAM.M.Sector
  {
    IS.ISector(Marshalling.parseSector(sector).value)
  }

  function ILBA(lba: LBA) : DAM.M.LBA { lba }

  predicate Inv(k: Constants, hs: HeapState)
  {
    && IS.WFVars(hs.s)
    && DAM.M.Inv(k, IS.IVars(hs.s))
  }

  method InitState() returns (k: Constants, hs: HeapState)
  {
    k := BC.Constants();
    hs := new IS.ImplHeapState();

    DAM.M.InitImpliesInv(k, IS.IVars(hs.s));
  }

  predicate WFSector(sector: DAM.M.Sector)
  {
    match sector {
      case SectorSuperblock(superblock) => BC.WFPersistentSuperblock(superblock)
      case SectorBlock(node) => BT.WFNode(node)
    }
  }

  method ReadSector(io: DiskIOHandler, lba: DAM.M.LBA)
  returns (sector: IS.Sector)
  requires io.initialized()
  modifies io
  ensures IS.WFSector(sector)
  ensures IDiskOp(io.diskOp()) == D.ReadOp(lba, IS.ISector(sector))
  {
    var bytes := io.read(lba);
    var sectorOpt := Marshalling.ParseSector(bytes);
    sector := sectorOpt.value;
  }

  method WriteSector(io: DiskIOHandler, lba: DAM.M.LBA, sector: IS.Sector)
  returns (success: bool)
  requires IS.WFSector(sector)
  requires sector.SectorBlock? ==> BT.WFNode(IS.INode(sector.block))
  requires sector.SectorBlock? ==> Marshalling.CappedNode(sector.block)
  requires io.initialized()
  modifies io
  ensures success ==> IDiskOp(io.diskOp()) == D.WriteOp(lba, IS.ISector(sector))
  ensures !success ==> IDiskOp(io.diskOp()) == D.NoDiskOp
  {
    var bytes := Marshalling.MarshallSector(sector);
    if (bytes == null) {
      return false;
    } else {
      io.write(lba, bytes);
      return true;
    }
  }

  method PageInSuperblock(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
  requires IS.WFVars(s)
  requires io.initialized();
  requires s.Unready?
  modifies io
  ensures IS.WFVars(s')
  ensures DAM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()))
  {
    var sector := ReadSector(io, BC.SuperblockLBA());
    if (sector.SectorSuperblock?) {
      s' := IS.Ready(sector.superblock, sector.superblock, map[]);
      assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.PageInSuperblockStep));
    } else {
      s' := s;
      assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; did not get superblock when reading\n";
    }
  }

  method PageIn(k: Constants, s: Variables, io: DiskIOHandler, ref: BC.Reference)
  returns (s': Variables)
  requires io.initialized();
  requires s.Ready?
  requires IS.WFVars(s)
  requires DAM.M.Inv(k, IS.IVars(s))
  requires ref in s.ephemeralSuperblock.lbas
  requires ref !in s.cache
  modifies io
  ensures IS.WFVars(s')
  ensures DAM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()))
  {
    var lba := s.ephemeralSuperblock.lbas[ref];
    var sector := ReadSector(io, lba);
    if (sector.SectorBlock?) {
      var node := sector.block;
      if (s.ephemeralSuperblock.graph[ref] == (if node.children.Some? then node.children.value else [])) {
        s' := s.(cache := s.cache[ref := sector.block]);
        assert BC.PageIn(k, IS.IVars(s), IS.IVars(s'), IDiskOp(io.diskOp()), ref);
        assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.PageInStep(ref)));
      } else {
        s' := s;
        assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
        print "giving up; block does not match graph\n";
      }
    } else {
      s' := s;
      assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; block read in was not block\n";
    }
  }

  method write(k: Constants, s: Variables, ref: BT.G.Reference, node: IS.Node)
  returns (s': Variables)
  requires s.Ready?
  requires IS.WFVars(s)
  requires ref in s.cache
  requires IS.WFNode(node)
  requires BC.BlockPointsToValidReferences(IS.INode(node), s.ephemeralSuperblock.graph)
  ensures IS.WFVars(s')
  ensures BC.Dirty(k, IS.IVars(s), IS.IVars(s'), ref, IS.INode(node))
  {
    s' := IS.Ready(
      s.persistentSuperblock,
      BC.Superblock(
        MapRemove(s.ephemeralSuperblock.lbas, {ref}),
        s.ephemeralSuperblock.graph[ref := if node.children.Some? then node.children.value else []]
      ),
      s.cache[ref := node]
    );
  }

  method alloc(k: Constants, s: Variables, node: IS.Node)
  returns (s': Variables, ref: Option<BT.G.Reference>)
  requires IS.WFVars(s)
  requires IS.WFNode(node)
  requires BC.Inv(k, IS.IVars(s));
  requires s.Ready?
  requires BC.BlockPointsToValidReferences(IS.INode(node), s.ephemeralSuperblock.graph)
  ensures IS.WFVars(s')
  ensures ref.Some? ==> BC.Alloc(k, IS.IVars(s), IS.IVars(s'), ref.value, IS.INode(node))
  ensures ref.None? ==> s' == s
  {
    ref := getFreeRef(s);
    if (ref.Some?) {
      s' := IS.Ready(
        s.persistentSuperblock,
        BC.Superblock(
          s.ephemeralSuperblock.lbas,
          s.ephemeralSuperblock.graph[ref.value := if node.children.Some? then node.children.value else []]
        ),
        s.cache[ref.value := node]
      );
    } else {
      s' := s;
    }
  }

  method InsertKeyValue(k: Constants, s: Variables, key: MS.Key, value: MS.Value)
  returns (s': Variables, success: bool)
  requires IS.WFVars(s)
  requires DAM.M.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires BT.G.Root() in s.cache
  ensures IS.WFVars(s')
  ensures DAM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), if success then UI.PutOp(key, value) else UI.NoOp, D.NoDiskOp)
  {
    var oldroot := s.cache[BT.G.Root()];
    var msg := Messages.Define(value);

    var bucket := oldroot.buckets[Pivots.Route(oldroot.pivotTable, key)];

    if (!(|bucket.strings| < 0x800_0000_0000_0000 && |bucket.starts| < 0x800_0000_0000_0000
        && |key| < 0x400_0000_0000_0000 && |value| < 0x400_0000_0000_0000)) {
      s' := s;
      success := false;
      assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, D.NoDiskOp, DAM.M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; data is impossibly big\n";
      return;
    }

    var newbucket := SSTable.Insert(bucket, key, msg);
    var newroot := oldroot.(buckets := oldroot.buckets[Pivots.Route(oldroot.pivotTable, key) := newbucket]);

    assert BC.BlockPointsToValidReferences(IS.INode(oldroot), s.ephemeralSuperblock.graph);
    //assert IS.INode(oldroot).children == IS.INode(newroot).children;
    //assert BC.BlockPointsToValidReferences(IS.INode(newroot), s.ephemeralSuperblock.graph);

    assert IS.INode(newroot) == BT.AddMessageToNode(IS.INode(oldroot), key, msg);

    s' := write(k, s, BT.G.Root(), newroot);
    success := true;

    assert BC.Dirty(Ik(k), IS.IVars(s), IS.IVars(s'), BT.G.Root(), IS.INode(newroot));
    assert BC.OpStep(Ik(k), IS.IVars(s), IS.IVars(s'), BT.G.WriteOp(BT.G.Root(), IS.INode(newroot)));
    assert BC.OpStep(Ik(k), IS.IVars(s), IS.IVars(s'), BT.BetreeStepOps(BT.BetreeInsert(BT.MessageInsertion(key, msg, IS.INode(oldroot))))[0]);
    assert BC.OpTransaction(Ik(k), IS.IVars(s), IS.IVars(s'), BT.BetreeStepOps(BT.BetreeInsert(BT.MessageInsertion(key, msg, IS.INode(oldroot)))));
    assert DAM.M.BetreeMove(Ik(k), IS.IVars(s), IS.IVars(s'), UI.PutOp(key, value), D.NoDiskOp, BT.BetreeInsert(BT.MessageInsertion(key, msg, IS.INode(oldroot))));
    assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.PutOp(key, value), D.NoDiskOp, DAM.M.BetreeMoveStep(BT.BetreeInsert(BT.MessageInsertion(key, msg, IS.INode(oldroot)))));
  }

  // note: I split this out because of sequence-related trigger loop problems
  ghost method AugmentLookup(lookup: seq<BT.G.ReadOp>, ref: BT.G.Reference, node: BT.G.Node, key: MS.Key, cache: map<BT.G.Reference, BT.G.Node>)
  returns (lookup' : seq<BT.G.ReadOp>)
  requires |lookup| > 0 ==> BT.WFLookupForKey(lookup, key)
  requires forall i | 0 <= i < |lookup| :: MapsTo(cache, lookup[i].ref, lookup[i].node)
  requires |lookup| == 0 ==> ref == BT.G.Root()
  requires |lookup| > 0 ==> Last(lookup).node.children.Some?
  requires |lookup| > 0 ==> Last(lookup).node.children.value[Pivots.Route(Last(lookup).node.pivotTable, key)] == ref
  requires BT.WFNode(node)
  requires MapsTo(cache, ref, node);
  ensures BT.WFLookupForKey(lookup', key)
  ensures Last(lookup').node == node
  ensures BT.InterpretLookup(lookup', key) == Messages.Merge(BT.InterpretLookup(lookup, key), BT.NodeLookup(node, key))
  ensures forall i | 0 <= i < |lookup'| :: MapsTo(cache, lookup'[i].ref, lookup'[i].node)
  {
    lookup' := lookup + [BT.G.ReadOp(ref, node)];

    forall idx | BT.ValidLayerIndex(lookup', idx) && idx < |lookup'| - 1
    ensures BT.LookupFollowsChildRefAtLayer(key, lookup', idx)
    {
      if idx == |lookup'| - 2 {
        assert BT.LookupFollowsChildRefAtLayer(key, lookup', idx);
      } else {
        assert BT.LookupFollowsChildRefAtLayer(key, lookup, idx);
        assert BT.LookupFollowsChildRefAtLayer(key, lookup', idx);
      }
    }
    assert BT.LookupFollowsChildRefs(key, lookup');
  }

  method query(k: Constants, s: Variables, io: DiskIOHandler, key: MS.Key)
  returns (s': Variables, res: Option<MS.Value>)
  requires io.initialized()
  requires IS.WFVars(s)
  requires DAM.M.Inv(k, IS.IVars(s))
  modifies io
  ensures IS.WFVars(s')
  ensures DAM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'),
    if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
    IDiskOp(io.diskOp()))
  {
    if (s.Unready?) {
      s' := PageInSuperblock(k, s, io);
      res := None;
    } else {
      var ref := BT.G.Root();
      var msg := Messages.IdentityMessage();
      ghost var lookup := [];

      // TODO if we have the acyclicity invariant, we can prove
      // termination without a bound like this.
      var loopBound := 40;
      ghost var exiting := false;

      while !msg.Define? && loopBound > 0
      invariant |lookup| == 0 ==> ref == BT.G.Root()
      invariant msg.Define? ==> |lookup| > 0
      invariant |lookup| > 0 ==> BT.WFLookupForKey(lookup, key)
      invariant !exiting && !msg.Define? ==> |lookup| > 0 ==> Last(lookup).node.children.Some?
      invariant !exiting && !msg.Define? ==> |lookup| > 0 ==> Last(lookup).node.children.value[Pivots.Route(Last(lookup).node.pivotTable, key)] == ref
      invariant forall i | 0 <= i < |lookup| :: MapsTo(IS.ICache(s.cache), lookup[i].ref, lookup[i].node)
      invariant ref in s.ephemeralSuperblock.graph
      invariant !exiting ==> msg == BT.InterpretLookup(lookup, key)
      invariant io.initialized()
      {
        assert !exiting;
        loopBound := loopBound - 1;

        if (ref !in s.cache) {
          s' := PageIn(k, s, io, ref);
          res := None;

          exiting := true;
          return;
        } else {
          var node := s.cache[ref];
          lookup := AugmentLookup(lookup, ref, IS.INode(node), key, IS.ICache(s.cache)); // ghost-y

          var sstMsg := SSTable.Query(node.buckets[Pivots.Route(node.pivotTable, key)], key);
          var lookupMsg := if sstMsg.Some? then sstMsg.value else Messages.IdentityMessage();
          msg := Messages.Merge(msg, lookupMsg);

          if (node.children.Some?) {
            ref := node.children.value[Pivots.Route(node.pivotTable, key)];
            assert ref in BT.G.Successors(IS.INode(node));
            assert ref in s.ephemeralSuperblock.graph;
          } else {
            if !msg.Define? {
              // Case where we reach leaf and find nothing
              s' := s;
              res := Some(MS.V.DefaultValue());

              assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'),
                if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
                IDiskOp(io.diskOp()),
                DAM.M.BetreeMoveStep(BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup))));

              exiting := true;
              return;
            }
          }
        }
      }

      if msg.Define? {
        s' := s;
        res := Some(msg.value);

        assert BT.ValidQuery(BT.LookupQuery(key, res.value, lookup));
        assert DAM.M.BetreeMove(Ik(k), IS.IVars(s), IS.IVars(s'),
          UI.GetOp(key, res.value),
          IDiskOp(io.diskOp()),
          BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup)));
        assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'),
          if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
          IDiskOp(io.diskOp()),
          DAM.M.BetreeMoveStep(BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup))));
      } else {
        // loop bound exceeded; do nothing :/
        s' := s;
        res := None;

        assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
        print "giving up; did not reach Leaf or a Define\n";
      }
    }
  }

  method insert(k: Constants, s: Variables, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (s': Variables, success: bool)
  requires io.initialized()
  modifies io
  requires IS.WFVars(s)
  requires DAM.M.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures DAM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'),
    if success then UI.PutOp(key, value) else UI.NoOp,
    IDiskOp(io.diskOp()))
  {
    if (s.Unready?) {
      s' := PageInSuperblock(k, s, io);
      success := false;
      return;
    }

    if (BT.G.Root() !in s.cache) {
      s' := PageIn(k, s, io, BT.G.Root());
      success := false;
      return;
    }

    s', success := InsertKeyValue(k, s, key, value);
  }

  method getFreeRef(s: Variables)
  returns (ref : Option<BT.G.Reference>)
  requires s.Ready?
  ensures ref.Some? ==> ref.value !in s.ephemeralSuperblock.graph
  {
    var v := s.ephemeralSuperblock.graph.Keys;

    var m;
    if |v| >= 1 {
      m := maximum(v);
    } else {
      m := 0;
    }

    if (m < 0xffff_ffff_ffff_ffff) {
      ref := Some(m + 1);
    } else {
      ref := None;
    }
  }

  method getFreeLba(s: Variables)
  returns (lba : Option<LBA>)
  requires s.Ready?
  ensures lba.Some? ==> lba.value !in s.persistentSuperblock.lbas.Values
  ensures lba.Some? ==> lba.value !in s.ephemeralSuperblock.lbas.Values
  ensures lba.Some? ==> lba.value != BC.SuperblockLBA()
  {
    var v1 := s.persistentSuperblock.lbas.Values;
    var v2 := s.ephemeralSuperblock.lbas.Values;

    var m1;
    var m2;

    if |v1| >= 1 {
      m1 := maximum(v1);
    } else {
      m1 := 0;
    }

    if |v2| >= 1 {
      m2 := maximum(v2);
    } else {
      m2 := 0;
    }

    var m := if m1 > m2 then m1 else m2;
    if (m < 0xffff_ffff_ffff_ffff) {
      lba := Some(m + 1);
    } else {
      lba := None;
    }
  }

  predicate method deallocable(s: Variables, ref: BT.G.Reference) {
    && s.Ready?
    && ref in s.cache
    && ref != BT.G.Root()
    && forall r | r in s.ephemeralSuperblock.graph :: ref !in s.ephemeralSuperblock.graph[r]
  }

  method dealloc(k: Constants, s: Variables, io: DiskIOHandler, ref: BT.G.Reference)
  returns (s': Variables)
  requires IS.WFVars(s)
  requires io.initialized()
  requires deallocable(s, ref)
  modifies io
  requires DAM.M.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures DAM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()))
  {
    s' := IS.Ready(
        s.persistentSuperblock,
        BC.Superblock(
          MapRemove(s.ephemeralSuperblock.lbas, {ref}),
          MapRemove(s.ephemeralSuperblock.graph, {ref})
        ),
        MapRemove(s.cache, {ref})
      );
    assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.UnallocStep(ref)));
  }

  method fixBigRoot(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
  requires IS.WFVars(s)
  requires s.Ready?
  requires io.initialized()
  modifies io
  requires DAM.M.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures DAM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()))
  {
    if (BT.G.Root() !in s.cache) {
      s' := PageIn(k, s, io, BT.G.Root());
      return;
    }

    var oldroot := s.cache[BT.G.Root()];
    var s1, newref := alloc(k, s, oldroot);
    match newref {
      case None => {
        s' := s;
        assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
        print "giving up; could not allocate ref\n";
      }
      case Some(newref) => {
        var newroot := IS.Node([], Some([newref]), [SSTable.Empty()]);

        assert BT.G.Root() in s.cache;
        assert BT.G.Root() in IS.ICache(s.cache);
        assert BT.G.Root() in IS.ICache(s1.cache);
        assert BT.G.Root() in s1.cache;

        s' := write(k, s1, BT.G.Root(), newroot);

        ghost var growth := BT.RootGrowth(IS.INode(oldroot), newref);
        assert IS.INode(newroot) == BT.G.Node([], Some([growth.newchildref]), [map[]]);
        ghost var step := BT.BetreeGrow(growth);
        BC.MakeTransaction2(k, IS.IVars(s), IS.IVars(s1), IS.IVars(s'), BT.BetreeStepOps(step));
        //assert DAM.M.BetreeMove(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), step);
        assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BetreeMoveStep(step));
      }
    }
  }

  method GetNewPivots(bucket: SSTable.SSTable)
  returns (pivots : seq<MS.Key>)
  requires SSTable.WFSSTableMap(bucket)
  ensures Pivots.WFPivots(pivots)
  {
    // try to split the keys evenly, but don't let any bucket
    // be larger than the cap

    var n := SSTable.Size(bucket) as int;

    var m := (n + Marshalling.CapNumBuckets() as int) / Marshalling.CapNumBuckets() as int;
    if m > Marshalling.CapBucketSize() as int / 2 {
      m := Marshalling.CapBucketSize() as int / 2;
    }
    if m < 1 {
      m := 1;
    }

    MS.Keyspace.reveal_IsStrictlySorted();
    SSTable.reveal_KeysStrictlySorted();
    var r := [];
    var i := m;
    while i < n
    invariant MS.Keyspace.IsStrictlySorted(r);
    invariant |r| > 0 ==> 0 <= i-m < n && r[|r|-1] == SSTable.KeyAtIndex(bucket, i - m);
    invariant |r| > 0 ==> MS.Keyspace.NotMinimum(r[0]);
    invariant i > 0
    {
      MS.Keyspace.IsNotMinimum(SSTable.KeyAtIndex(bucket, 0), SSTable.KeyAtIndex(bucket, i));

      r := r + [SSTable.KeyAtIndex(bucket, i)];
      i := i + m;
    }

    pivots := r;
  }

  method CutoffNodeAndKeepLeft(node: IS.Node, pivot: Key)
  returns (node': IS.Node)
  requires IS.WFNode(node)
  requires BT.WFNode(IS.INode(node))
  ensures IS.WFNode(node')
  ensures IS.INode(node') == BT.CutoffNodeAndKeepLeft(IS.INode(node), pivot)
  {
    BT.reveal_CutoffNodeAndKeepLeft();
    var cLeft := Pivots.CutoffForLeft(node.pivotTable, pivot);
    var leftPivots := node.pivotTable[.. cLeft];
    var leftChildren := if node.children.Some? then Some(node.children.value[.. cLeft + 1]) else None;
    var splitBucket := SSTable.SplitLeft(node.buckets[cLeft], pivot);
    var leftBuckets := node.buckets[.. cLeft] + [splitBucket];
    node' := IS.Node(leftPivots, leftChildren, leftBuckets);
  }

  method CutoffNodeAndKeepRight(node: IS.Node, pivot: Key)
  returns (node': IS.Node)
  requires IS.WFNode(node)
  requires BT.WFNode(IS.INode(node))
  ensures IS.WFNode(node')
  ensures IS.INode(node') == BT.CutoffNodeAndKeepRight(IS.INode(node), pivot)
  {
    BT.reveal_CutoffNodeAndKeepRight();
    var cRight := Pivots.CutoffForRight(node.pivotTable, pivot);
    var rightPivots := node.pivotTable[cRight ..];
    var rightChildren := if node.children.Some? then Some(node.children.value[cRight ..]) else None;
    var splitBucket := SSTable.SplitRight(node.buckets[cRight], pivot);
    var rightBuckets := [splitBucket] + node.buckets[cRight + 1 ..];
    node' := IS.Node(rightPivots, rightChildren, rightBuckets);
  }

  method CutoffNode(node: IS.Node, lbound: Option<Key>, rbound: Option<Key>)
  returns (node' : IS.Node)
  requires IS.WFNode(node)
  requires BT.WFNode(IS.INode(node))
  ensures IS.WFNode(node')
  ensures IS.INode(node') == BT.CutoffNode(IS.INode(node), lbound, rbound)
  {
    BT.reveal_CutoffNode();

    match lbound {
      case None => {
        match rbound {
          case None => {
            node' := node;
          }
          case Some(rbound) => {
            node' := CutoffNodeAndKeepLeft(node, rbound);
          }
        }
      }
      case Some(lbound) => {
        match rbound {
          case None => {
            node' := CutoffNodeAndKeepRight(node, lbound);
          }
          case Some(rbound) => {
            var node1 := CutoffNodeAndKeepLeft(node, rbound);
            node' := CutoffNodeAndKeepRight(node1, lbound);
          }
        }
      }
    }
  }

  method doSplit(k: Constants, s: Variables, io: DiskIOHandler, parentref: BT.G.Reference, ref: BT.G.Reference, slot: int)
  returns (s': Variables)
  requires s.Ready?
  requires IS.WFVars(s)
  requires DAM.M.Inv(k, IS.IVars(s))
  requires ref in s.cache
  requires parentref in s.cache
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires s.cache[parentref].children.value[slot] == ref
  requires io.initialized()
  modifies io
  ensures IS.WFVars(s')
  ensures DAM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()))
  {
    var fused_parent := s.cache[parentref];
    var fused_child := s.cache[ref];

    assert BT.WFNode(IS.ICache(s.cache)[parentref]);
    assert BT.WFNode(IS.ICache(s.cache)[ref]);

    var lbound := (if slot > 0 then Some(fused_parent.pivotTable[slot - 1]) else None);
    var ubound := (if slot < |fused_parent.pivotTable| then Some(fused_parent.pivotTable[slot]) else None);
    var child := CutoffNode(fused_child, lbound, ubound);

    if !SSTable.IsEmpty(fused_parent.buckets[slot]) {
      s' := s;
      assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; trying to split but parent has non-empty buffer";
      return;
    }

    if (|child.pivotTable| == 0) {
      // TODO there should be an operation which just
      // cuts off the node and doesn't split it.
      s' := s;
      assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; child.pivots == 0\n";
      return;
    }

    var num_children_left := |child.buckets| / 2;
    var pivot := child.pivotTable[num_children_left - 1];

    var left_child := IS.Node(
      child.pivotTable[ .. num_children_left - 1 ],
      if child.children.Some? then Some(child.children.value[ .. num_children_left ]) else None,
      child.buckets[ .. num_children_left ]
    );

    var right_child := IS.Node(
      child.pivotTable[ num_children_left .. ],
      if child.children.Some? then Some(child.children.value[ num_children_left .. ]) else None,
      child.buckets[ num_children_left .. ]
    );

    SSTable.Islice(child.buckets, 0, num_children_left);
    SSTable.Isuffix(child.buckets, num_children_left);

    forall r | r in BT.G.Successors(IS.INode(child))
    ensures r in s.ephemeralSuperblock.graph
    {
      assert BC.BlockPointsToValidReferences(IS.INode(fused_child), s.ephemeralSuperblock.graph);
      assert r in BT.G.Successors(IS.INode(fused_child));
    }
    assert BC.BlockPointsToValidReferences(IS.INode(child), s.ephemeralSuperblock.graph);

    // TODO can we get BetreeBlockCache to ensure that will be true generally whenever taking a betree step?
    // This sort of proof logic shouldn't have to be in the implementation.
    assert BC.BlockPointsToValidReferences(IS.INode(left_child), s.ephemeralSuperblock.graph);
    assert BC.BlockPointsToValidReferences(IS.INode(right_child), s.ephemeralSuperblock.graph);

    var s1, left_childref := alloc(k, s, left_child);
    if left_childref.None? {
      s' := s;
      assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; could not get ref\n";
      return;
    }

    var s2, right_childref := alloc(k, s1, right_child);
    if right_childref.None? {
      s' := s;
      assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; could not get ref\n";
      return;
    }

    var split_parent_pivots := Sequences.insert(fused_parent.pivotTable, pivot, slot);
    var split_parent_children := replace1with2(fused_parent.children.value, left_childref.value, right_childref.value, slot);
    var split_parent_buckets := replace1with2(fused_parent.buckets, SSTable.Empty(), SSTable.Empty(), slot);
    var split_parent := IS.Node(
      split_parent_pivots,
      Some(split_parent_children),
      split_parent_buckets
    );

    SSTable.Ireplace1with2(fused_parent.buckets, SSTable.Empty(), SSTable.Empty(), slot);

    assert IS.WFNode(split_parent);

    forall r | r in BT.G.Successors(IS.INode(split_parent))
    ensures r in s2.ephemeralSuperblock.graph
    {
      assert BC.BlockPointsToValidReferences(IS.INode(fused_parent), s2.ephemeralSuperblock.graph);
      var idx :| 0 <= idx < |split_parent_children| && split_parent_children[idx] == r;
      if (idx < slot) {
        assert r == fused_parent.children.value[idx];
        assert r in s2.ephemeralSuperblock.graph;
      } else if (idx == slot) {
        assert r == left_childref.value;
        assert r in s2.ephemeralSuperblock.graph;
      } else if (idx == slot + 1) {
        assert r == right_childref.value;
        assert r in s2.ephemeralSuperblock.graph;
      } else {
        assert r == fused_parent.children.value[idx-1];
        assert r in s2.ephemeralSuperblock.graph;
      }
    }
    assert BC.BlockPointsToValidReferences(IS.INode(split_parent), s2.ephemeralSuperblock.graph);

    assert parentref in s.cache;
    assert parentref in IS.ICache(s.cache);
    assert parentref in IS.ICache(s1.cache);
    assert parentref in IS.ICache(s2.cache);
    assert parentref in s2.cache;

    s' := write(k, s2, parentref, split_parent);

    ghost var splitStep := BT.NodeFusion(
      parentref,
      ref,
      left_childref.value,
      right_childref.value,
      IS.INode(fused_parent),
      IS.INode(split_parent),
      IS.INode(fused_child),
      IS.INode(left_child),
      IS.INode(right_child),
      slot,
      num_children_left,
      pivot
    );
    assert BT.ValidSplit(splitStep);
    ghost var step := BT.BetreeSplit(splitStep);
    BC.MakeTransaction3(k, IS.IVars(s), IS.IVars(s1), IS.IVars(s2), IS.IVars(s'), BT.BetreeStepOps(step));
    assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BetreeMoveStep(step));
  }

  lemma ChildCanBePagedIn(k: Constants, s: Variables, ref: BT.G.Reference, childref: BT.G.Reference)
  requires IS.WFVars(s)
  requires DAM.M.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires childref !in s.cache
  requires ref in s.cache
  requires childref in BT.G.Successors(IS.INode(s.cache[ref]))
  ensures childref in s.ephemeralSuperblock.lbas
  {
    assert childref in BT.G.Successors(IS.ICache(s.cache)[ref]);
    assert childref in IS.IVars(s).ephemeralSuperblock.lbas;
  }

  method flush(k: Constants, s: Variables, io: DiskIOHandler, ref: BT.G.Reference, slot: int)
  returns (s': Variables)
  requires IS.WFVars(s)
  requires s.Ready?
  requires ref in s.cache
  requires s.cache[ref].children.Some?
  requires 0 <= slot < |s.cache[ref].buckets|
  requires io.initialized()
  modifies io
  requires DAM.M.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures DAM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()))
  {
    var node := s.cache[ref];

    assert IS.INode(node) == IS.ICache(s.cache)[ref];
    assert BT.WFNode(IS.INode(node));

    var childref := node.children.value[slot];

    if (childref !in s.cache) {
      ChildCanBePagedIn(k, s, ref, childref);
      s' := PageIn(k, s, io, childref);
      return;
    }

    var child := s.cache[childref];

    assert IS.INode(child) == IS.ICache(s.cache)[childref];
    assert BT.WFNode(IS.INode(child));

    if (!(
        && |node.buckets[slot].strings| < 0x800_0000_0000_0000
        && |node.buckets[slot].starts| < 0x800_0000_0000_0000
        && (forall i | 0 <= i < |child.buckets| :: |child.buckets[i].strings| < 0x800_0000_0000_0000)
        && (forall i | 0 <= i < |child.buckets| :: |child.buckets[i].starts| < 0x800_0000_0000_0000)
    )) {
      s' := s;
      assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; data is 2 big\n";
      return;
    }

    forall i, key | 0 <= i < |child.buckets| && key in SSTable.I(child.buckets[i]) ensures Pivots.Route(child.pivotTable, key) == i
    {
      assert BT.NodeHasWFBucketAt(IS.INode(child), i);
    }

    var newbuckets := SSTable.DoFlush(node.buckets[slot], child.buckets, child.pivotTable);
    var newchild := child.(buckets := newbuckets);

    assert BT.G.Successors(IS.INode(newchild)) == BT.G.Successors(IS.INode(child));
    assert BC.BlockPointsToValidReferences(IS.INode(newchild), s.ephemeralSuperblock.graph);

    var s1, newchildref := alloc(k, s, newchild);
    if newchildref.None? {
      s' := s;
      assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; could not get ref\n";
      return;
    }

    var newparent := IS.Node(
        node.pivotTable,
        Some(node.children.value[slot := newchildref.value]),
        node.buckets[slot := SSTable.Empty()]
      );

    assert BC.BlockPointsToValidReferences(IS.INode(node), s1.ephemeralSuperblock.graph);
    forall ref | ref in BT.G.Successors(IS.INode(newparent)) ensures ref in s1.ephemeralSuperblock.graph {
      if (ref == newchildref.value) {
      } else {
        assert ref in BT.G.Successors(IS.INode(node));
      }
    }
    assert BC.BlockPointsToValidReferences(IS.INode(newparent), s1.ephemeralSuperblock.graph);

    assert ref in s.cache;
    assert ref in IS.ICache(s.cache);
    assert ref in IS.ICache(s1.cache);
    assert ref in s1.cache;

    s' := write(k, s1, ref, newparent);

    ghost var flushStep := BT.NodeFlush(ref, IS.INode(node), childref, IS.INode(child), newchildref.value, IS.INode(newchild), slot);
    assert BT.ValidFlush(flushStep);
    ghost var step := BT.BetreeFlush(flushStep);
    assert IS.INode(newparent) == BT.FlushOps(flushStep)[1].node;
    BC.MakeTransaction2(k, IS.IVars(s), IS.IVars(s1), IS.IVars(s'), BT.BetreeStepOps(step));
    assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BetreeMoveStep(step));
  }

  method {:fuel BT.JoinBuckets,0} fixBigNode(k: Constants, s: Variables, io: DiskIOHandler, ref: BT.G.Reference, parentref: BT.G.Reference)
  returns (s': Variables)
  requires IS.WFVars(s)
  requires DAM.M.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires ref in s.cache
  requires parentref in s.ephemeralSuperblock.graph
  requires ref in s.ephemeralSuperblock.graph[parentref]
  requires io.initialized()
  modifies io
  ensures IS.WFVars(s')
  ensures DAM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()))
  {
    if (ref !in s.cache) {
      s' := PageIn(k, s, io, ref);
      return;
    }

    var node := s.cache[ref];

    if i :| 0 <= i < |node.buckets| && SSTable.Size(node.buckets[i]) > Marshalling.CapBucketSize() {
      if (node.children.Some?) {
        // internal node case: flush
        s' := flush(k, s, io, ref, i);
      } else {
        // leaf case

        if (!(
          && |node.buckets| < 0x100
          && forall i | 0 <= i < |node.buckets| :: |node.buckets[i].strings| < 0x10_0000_0000_0000
          && forall i | 0 <= i < |node.buckets| :: |node.buckets[i].starts| < 0x10_0000_0000_0000
        )) {
          s' := s;
          assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
          print "giving up; stuff too big to call Join\n";
          return;
        }

        forall i, j, key1, key2 | 0 <= i < j < |node.buckets| && key1 in SSTable.I(node.buckets[i]) && key2 in SSTable.I(node.buckets[j])
        ensures MS.Keyspace.lt(key1, key2)
        {
          assert BT.NodeHasWFBucketAt(IS.INode(node), i);
          assert BT.NodeHasWFBucketAt(IS.INode(node), j);
          assert Pivots.Route(node.pivotTable, key1) == i;
          assert Pivots.Route(node.pivotTable, key2) == j;
          MS.Keyspace.IsStrictlySortedImpliesLte(node.pivotTable, i, j-1);
        }

        var joined := SSTable.DoJoin(node.buckets);
        var pivots := GetNewPivots(joined);

        if (!(
          && |joined.strings| < 0x800_0000_0000_0000
          && |joined.starts| < 0x800_0000_0000_0000
        )) {
          s' := s;
          assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
          print "giving up; stuff too big to call Split\n";
          return;
        }

        var buckets' := SSTable.SplitOnPivots(joined, pivots);
        var newnode := IS.Node(pivots, None, buckets');

        s' := write(k, s, ref, newnode);

        //assert BT.ValidRepivot(BT.Repivot(ref, node, pivots));
        ghost var step := BT.BetreeRepivot(BT.Repivot(ref, IS.INode(node), pivots));
        BC.MakeTransaction1(k, IS.IVars(s), IS.IVars(s'), BT.BetreeStepOps(step));
        assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BetreeMoveStep(step));
      }
    } else if |node.buckets| > Marshalling.CapNumBuckets() as int {
      if (parentref !in s.cache) {
        s' := PageIn(k, s, io, parentref);
        return;
      }

      var parent := s.cache[parentref];

      assert ref in BT.G.Successors(IS.INode(parent));
      var i :| 0 <= i < |parent.children.value| && parent.children.value[i] == ref;

      s' := doSplit(k, s, io, parentref, ref, i);
    } else {
      s' := s;
      assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; fixBigNode\n";
    }
  }

  method sync(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables, success: bool)
  requires io.initialized()
  modifies io
  requires IS.WFVars(s)
  requires DAM.M.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures DAM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'),
    if success then UI.SyncOp else UI.NoOp,
    IDiskOp(io.diskOp()))
  {
    if (s.Unready?) {
      // TODO we could just do nothing here instead
      s' := PageInSuperblock(k, s, io);
      success := false;
      return;
    }

    if ref :| ref in s.cache && deallocable(s, ref) {
      success := false;
      s' := dealloc(k, s, io, ref);
    } else if ref :| ref in s.cache && !Marshalling.CappedNode(s.cache[ref]) {
      success := false;
      if (ref == BT.G.Root()) {
        s' := fixBigRoot(k, s, io);
      } else {
        assert !deallocable(s, ref);
        assert !(forall r | r in s.ephemeralSuperblock.graph :: ref !in s.ephemeralSuperblock.graph[r]);
        assert !(forall r :: r in s.ephemeralSuperblock.graph ==> ref !in s.ephemeralSuperblock.graph[r]);
        assert (exists r :: !(r in s.ephemeralSuperblock.graph ==> ref !in s.ephemeralSuperblock.graph[r]));
        var r :| !(r in s.ephemeralSuperblock.graph ==> ref !in s.ephemeralSuperblock.graph[r]);
        s' := fixBigNode(k, s, io, ref, r);
      }
    } else if ref :| ref in s.ephemeralSuperblock.graph && ref !in s.ephemeralSuperblock.lbas {
      var lba := getFreeLba(s);
      match lba {
        case Some(lba) => {
          var succ := WriteSector(io, lba, IS.SectorBlock(s.cache[ref]));
          if (succ) {
            success := false;
            s' := s.(ephemeralSuperblock := s.ephemeralSuperblock.(lbas := s.ephemeralSuperblock.lbas[ref := lba]));
            assert BC.WriteBack(Ik(k), IS.IVars(s), IS.IVars(s'), IDiskOp(io.diskOp()), ref);
            assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.WriteBackStep(ref)));
          } else {
            success := false;
            s' := s;
            assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
            print "giving up; sync could not write\n";
          }
        }
        case None => {
          success := false;
          s' := s;
          assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
          print "giving up; could not get lba\n";
        }
      }
    } else {
      var succ := WriteSector(io, BC.SuperblockLBA(), IS.SectorSuperblock(s.ephemeralSuperblock));
      if (succ) {
        success := true;
        s' := s.(persistentSuperblock := s.ephemeralSuperblock);
        assert BC.WriteBackSuperblock(Ik(k), IS.IVars(s), IS.IVars(s'), IDiskOp(io.diskOp()));
        assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.SyncOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.WriteBackSuperblockStep));
      } else {
        success := false;
        s' := s;
        assert DAM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, IDiskOp(io.diskOp()), DAM.M.BlockCacheMoveStep(BC.NoOpStep));
        print "giving up; could not write superblock\n";
      }
    }
  }

  ////////// Top-level handlers

  method handleSync(k: Constants, hs: HeapState, io: DiskIOHandler)
  returns (success: bool)
  {
    var s := hs.s;
    var s', succ := sync(k, s, io);
    var uiop := if succ then UI.SyncOp else UI.NoOp;
    DAM.M.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, IDiskOp(io.diskOp()));
    hs.s := s';
    success := succ;
  }

  method handleQuery(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key)
  returns (v: Option<MS.Value>)
  {
    var s := hs.s;
    var s', value := query(k, s, io, key);
    var uiop := if value.Some? then UI.GetOp(key, value.value) else UI.NoOp;
    DAM.M.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, IDiskOp(io.diskOp()));
    hs.s := s';
    v := value;
  }

  method handleInsert(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (success: bool)
  {
    var s := hs.s;
    var s', succ := insert(k, s, io, key, value);
    var uiop := if succ then UI.PutOp(key, value) else UI.NoOp;
    DAM.M.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, IDiskOp(io.diskOp()));
    hs.s := s';
    success := succ;
  }
}
