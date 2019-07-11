include "Main.dfy"
include "../lib/Sets.dfy"
include "BetreeBlockCache.dfy"
include "ByteBetree.dfy"

module {:extern} Impl refines Main { 
  import BC = BetreeGraphBlockCache
  import BT = PivotBetreeSpec`Internal
  import M = BetreeBlockCache
  import Marshalling
  import Messages = ValueMessage
  import Pivots = PivotsLib
  import opened Sets

  import opened Maps
  import opened Sequences

  type Variables = M.Variables
  type Constants = M.Constants

  class ImplHeapState {
    var s: Variables
    constructor()
    ensures M.Init(BC.Constants(), s);
    {
      s := BC.Unready;
    }
  }
  type HeapState = ImplHeapState
  function HeapSet(hs: HeapState) : set<object> { {hs} }

  function Ik(k: Constants) : M.Constants { k }
  function I(k: Constants, hs: HeapState) : M.Variables { hs.s }

  predicate ValidSector(sector: Sector)
  {
    && Marshalling.parseSector(sector).Some?
  }

  function ISector(sector: Sector) : M.Sector
  {
    Marshalling.parseSector(sector).value
  }

  function ILBA(lba: LBA) : M.LBA { lba }

  predicate Inv(k: Constants, hs: HeapState)
  {
    M.Inv(k, hs.s)
  }

  method InitState() returns (k: Constants, hs: HeapState)
  {
    k := BC.Constants();
    hs := new ImplHeapState();

    M.InitImpliesInv(k, hs.s);
  }

  predicate WFSector(sector: M.Sector)
  {
    match sector {
      case SectorSuperblock(superblock) => BC.WFPersistentSuperblock(superblock)
      case SectorBlock(node) => BT.WFNode(node)
    }
  }

  method ReadSector(io: DiskIOHandler, lba: M.LBA)
  returns (sector: M.Sector)
  requires io.initialized()
  modifies io
  ensures IDiskOp(io.diskOp()) == D.ReadOp(lba, sector)
  ensures WFSector(sector)
  {
    var bytes := io.read(lba);
    var sectorOpt := Marshalling.ParseSector(bytes);
    sector := sectorOpt.value;
  }

  method WriteSector(io: DiskIOHandler, lba: M.LBA, sector: M.Sector)
  returns (success: bool)
  requires WFSector(sector)
  requires io.initialized()
  requires sector.SectorBlock? ==> Marshalling.CappedNode(sector.block)
  modifies io
  ensures success ==> IDiskOp(io.diskOp()) == D.WriteOp(lba, sector)
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
  requires io.initialized();
  requires s.Unready?
  modifies io
  ensures M.Next(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()))
  {
    var sector := ReadSector(io, BC.SuperblockLBA());
    if (sector.SectorSuperblock?) {
      s' := BC.Ready(sector.superblock, sector.superblock, map[]);
      assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.PageInSuperblockStep));
    } else {
      s' := s;
      assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; did not get superblock when reading\n";
    }
  }

  method PageIn(k: Constants, s: Variables, io: DiskIOHandler, ref: BC.Reference)
  returns (s': Variables)
  requires io.initialized();
  requires s.Ready?
  requires M.Inv(k, s)
  requires ref in s.ephemeralSuperblock.lbas
  requires ref !in s.cache
  modifies io
  ensures M.Next(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()))
  {
    var lba := s.ephemeralSuperblock.lbas[ref];
    var sector := ReadSector(io, lba);
    if (sector.SectorBlock?) {
      var node := sector.block;
      if (s.ephemeralSuperblock.graph[ref] == (if node.children.Some? then node.children.value else [])) {
        s' := s.(cache := s.cache[ref := sector.block]);
        assert BC.PageIn(k, s, s', IDiskOp(io.diskOp()), ref);
        assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.PageInStep(ref)));
      } else {
        s' := s;
        assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.NoOpStep));
        print "giving up; block does not match graph\n";
      }
    } else {
      s' := s;
      assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; block read in was not block\n";
    }
  }

  method InsertKeyValue(k: Constants, s: Variables, key: MS.Key, value: MS.Value)
  returns (s': Variables)
  requires M.Inv(k, s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  ensures M.Next(Ik(k), s, s', UI.PutOp(key, value), D.NoDiskOp)
  {
    var oldroot := s.cache[BT.G.Root()];
    var msg := Messages.Define(value);
    var newroot := BT.AddMessageToNode(oldroot, key, msg);
    s' := s.(cache := s.cache[BT.G.Root() := newroot])
           .(ephemeralSuperblock := s.ephemeralSuperblock.(lbas := MapRemove(s.ephemeralSuperblock.lbas, {BT.G.Root()})));

    assert s'.ephemeralSuperblock.graph[BT.G.Root()] == s.ephemeralSuperblock.graph[BT.G.Root()];
    assert BC.G.Successors(oldroot) == BC.G.Successors(oldroot);
    assert BC.BlockPointsToValidReferences(oldroot, s.ephemeralSuperblock.graph);
    assert BC.BlockPointsToValidReferences(newroot, s.ephemeralSuperblock.graph);
    assert (iset r | r in s.ephemeralSuperblock.graph[BC.G.Root()]) == BC.G.Successors(oldroot);
    assert (iset r | r in s'.ephemeralSuperblock.graph[BC.G.Root()])
        == (iset r | r in s.ephemeralSuperblock.graph[BC.G.Root()])
        == BC.G.Successors(oldroot)
        == BC.G.Successors(newroot);
    //assert BT.G.Successors(newroot) == BT.G.Successors(oldroot);
    //assert BC.BlockPointsToValidReferences(newroot, s.ephemeralSuperblock.refcounts);
    assert BC.Dirty(Ik(k), s, s', BT.G.Root(), newroot);
    assert BC.OpStep(Ik(k), s, s', BT.G.WriteOp(BT.G.Root(), newroot));
    assert BC.OpStep(Ik(k), s, s', BT.BetreeStepOps(BT.BetreeInsert(BT.MessageInsertion(key, msg, oldroot)))[0]);
    assert BC.OpTransaction(Ik(k), s, s', BT.BetreeStepOps(BT.BetreeInsert(BT.MessageInsertion(key, msg, oldroot))));
    assert M.BetreeMove(Ik(k), s, s', UI.PutOp(key, value), D.NoDiskOp, BT.BetreeInsert(BT.MessageInsertion(key, msg, oldroot)));
    assert M.NextStep(Ik(k), s, s', UI.PutOp(key, value), D.NoDiskOp, M.BetreeMoveStep(BT.BetreeInsert(BT.MessageInsertion(key, msg, oldroot))));
  }

  method write(k: Constants, s: Variables, ref: BT.G.Reference, node: BT.G.Node)
  returns (s': Variables)
  requires s.Ready?
  requires ref in s.cache
  requires BC.BlockPointsToValidReferences(node, s.ephemeralSuperblock.graph)
  ensures BC.Dirty(k, s, s', ref, node)
  {
    s' := BC.Ready(
      s.persistentSuperblock,
      BC.Superblock(
        MapRemove(s.ephemeralSuperblock.lbas, {ref}),
        s.ephemeralSuperblock.graph[ref := if node.children.Some? then node.children.value else []]
      ),
      s.cache[ref := node]
    );
  }


  method alloc(k: Constants, s: Variables, node: BT.G.Node)
  returns (s': Variables, ref: Option<BT.G.Reference>)
  requires BC.Inv(k, s);
  requires s.Ready?
  requires BC.BlockPointsToValidReferences(node, s.ephemeralSuperblock.graph)
  ensures ref.Some? ==> BC.Alloc(k, s, s', ref.value, node)
  ensures ref.None? ==> s' == s
  {
    ref := getFreeRef(s);
    if (ref.Some?) {
      s' := BC.Ready(
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

  /*
  method doStuff(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
  requires io.initialized()
  modifies io
  ensures M.Next(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()))
  {
    if (s.Unready?) {
      s' := PageInSuperblock(k, s, io);
      assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.PageInSuperblockStep));
    } else {
      assume false;
    }
  }
  */

  // note: I split this out because of sequence-related trigger loop problems
  ghost method AugmentLookup(lookup: seq<BT.G.ReadOp>, ref: BT.G.Reference, node: BT.G.Node, key: MS.Key, s: Variables)
  returns (lookup' : seq<BT.G.ReadOp>)
  requires s.Ready?
  requires |lookup| > 0 ==> BT.WFLookupForKey(lookup, key)
  requires forall i | 0 <= i < |lookup| :: MapsTo(s.cache, lookup[i].ref, lookup[i].node)
  requires |lookup| == 0 ==> ref == BT.G.Root()
  requires |lookup| > 0 ==> Last(lookup).node.children.Some?
  requires |lookup| > 0 ==> Last(lookup).node.children.value[Pivots.Route(Last(lookup).node.pivotTable, key)] == ref
  requires BT.WFNode(node)
  requires MapsTo(s.cache, ref, node);
  ensures BT.WFLookupForKey(lookup', key)
  ensures Last(lookup').node == node
  ensures BT.InterpretLookup(lookup', key) == Messages.Merge(BT.InterpretLookup(lookup, key), BT.NodeLookup(node, key))
  ensures forall i | 0 <= i < |lookup'| :: MapsTo(s.cache, lookup'[i].ref, lookup'[i].node)
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
  requires M.Inv(k, s)
  modifies io
  ensures M.Next(Ik(k), s, s',
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
      invariant forall i | 0 <= i < |lookup| :: MapsTo(s.cache, lookup[i].ref, lookup[i].node)
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
          lookup := AugmentLookup(lookup, ref, node, key, s); // ghost-y
          msg := Messages.Merge(msg, BT.NodeLookup(node, key));

          if (node.children.Some?) {
            ref := node.children.value[Pivots.Route(node.pivotTable, key)];
            assert ref in BT.G.Successors(node);
            assert ref in s.ephemeralSuperblock.graph;
          } else {
            if !msg.Define? {
              // Case where we reach leaf and find nothing
              s' := s;
              res := Some(MS.V.DefaultValue());

              assert M.NextStep(Ik(k), s, s',
                if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
                IDiskOp(io.diskOp()),
                M.BetreeMoveStep(BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup))));

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
        assert M.BetreeMove(Ik(k), s, s',
          UI.GetOp(key, res.value),
          IDiskOp(io.diskOp()),
          BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup)));
        assert M.NextStep(Ik(k), s, s',
          if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
          IDiskOp(io.diskOp()),
          M.BetreeMoveStep(BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup))));
      } else {
        // loop bound exceeded; do nothing :/
        s' := s;
        res := None;

        assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.NoOpStep));
        print "giving up; did not reach Leaf or a Define\n";
      }
    }
  }

  method insert(k: Constants, s: Variables, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (s': Variables, success: bool)
  requires io.initialized()
  modifies io
  requires M.Inv(k, s)
  ensures M.Next(Ik(k), s, s',
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

    s' := InsertKeyValue(k, s, key, value);
    success := true;
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
  requires io.initialized()
  requires deallocable(s, ref)
  modifies io
  requires M.Inv(k, s)
  ensures M.Next(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()))
  {
    s' := BC.Ready(
        s.persistentSuperblock,
        BC.Superblock(
          MapRemove(s.ephemeralSuperblock.lbas, {ref}),
          MapRemove(s.ephemeralSuperblock.graph, {ref})
        ),
        MapRemove(s.cache, {ref})
      );
    assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.UnallocStep(ref)));
  }

  method fixBigRoot(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
  requires s.Ready?
  requires io.initialized()
  modifies io
  requires M.Inv(k, s)
  ensures M.Next(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()))
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
        assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.NoOpStep));
        print "giving up; could not allocate ref\n";
      }
      case Some(newref) => {
        var newroot := BT.G.Node([], Some([newref]), [map[]]);
        s' := write(k, s1, BT.G.Root(), newroot);

        ghost var step := BT.BetreeGrow(BT.RootGrowth(oldroot, newref));
        BC.MakeTransaction2(k, s, s1, s', BT.BetreeStepOps(step));
        //assert M.BetreeMove(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), step);
        assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BetreeMoveStep(step));
      }
    }
  }

  method GetNewPivots(bucket: map<MS.Key, Messages.Message>)
  returns (pivots : seq<MS.Key>)
  ensures Pivots.WFPivots(pivots)
  {
    // try to split the keys evenly, but don't let any bucket
    // be larger than the cap

    var allKeys := MS.Keyspace.SortedSeqOfSet(bucket.Keys);

    var m := (|allKeys| + Marshalling.CapNumBuckets() as int) / Marshalling.CapNumBuckets() as int;
    if m > Marshalling.CapBucketSize() as int / 2 {
      m := Marshalling.CapBucketSize() as int / 2;
    }
    if m < 1 {
      m := 1;
    }

    MS.Keyspace.reveal_IsStrictlySorted();
    var r := [];
    var i := m;
    while i < |allKeys|
    invariant MS.Keyspace.IsStrictlySorted(r);
    invariant |r| > 0 ==> 0 <= i-m < |allKeys| && r[|r|-1] == allKeys[i - m];
    invariant |r| > 0 ==> MS.Keyspace.NotMinimum(r[0]);
    invariant i > 0
    {
      MS.Keyspace.IsNotMinimum(allKeys[0], allKeys[i]);

      r := r + [allKeys[i]];
      i := i + m;
    }

    pivots := r;
  }

  method doSplit(k: Constants, s: Variables, io: DiskIOHandler, parentref: BT.G.Reference, ref: BT.G.Reference, slot: int)
  returns (s': Variables)
  requires s.Ready?
  requires ref in s.cache
  requires parentref in s.cache
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires s.cache[parentref].children.value[slot] == ref
  requires io.initialized()
  modifies io
  requires M.Inv(k, s)
  ensures M.Next(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()))
  {
    var fused_parent := s.cache[parentref];
    var fused_child := s.cache[ref];

    var lbound := (if slot > 0 then Some(fused_parent.pivotTable[slot - 1]) else None);
    var ubound := (if slot < |fused_parent.pivotTable| then Some(fused_parent.pivotTable[slot]) else None);
    var child := BT.CutoffNode(fused_child, lbound, ubound);

    if fused_parent.buckets[slot] != map[] {
      s' := s;
      assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; trying to split but parent has non-empty buffer";
      return;
    }

    if (|child.pivotTable| == 0) {
      // TODO there should be an operation which just
      // cuts off the node and doesn't split it.
      s' := s;
      assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; child.pivots == 0\n";
      return;
    }

    var num_children_left := |child.buckets| / 2;
    var pivot := child.pivotTable[num_children_left - 1];

    var left_child := BT.G.Node(
      child.pivotTable[ .. num_children_left - 1 ],
      if child.children.Some? then Some(child.children.value[ .. num_children_left ]) else None,
      child.buckets[ .. num_children_left ]
    );

    var right_child := BT.G.Node(
      child.pivotTable[ num_children_left .. ],
      if child.children.Some? then Some(child.children.value[ num_children_left .. ]) else None,
      child.buckets[ num_children_left .. ]
    );

    forall r | r in BT.G.Successors(child)
    ensures r in s.ephemeralSuperblock.graph
    {
      assert BC.BlockPointsToValidReferences(fused_child, s.ephemeralSuperblock.graph);
      assert r in BT.G.Successors(fused_child);
    }
    assert BC.BlockPointsToValidReferences(child, s.ephemeralSuperblock.graph);

    // TODO can we get BetreeBlockCache to ensure that will be true generally whenever taking a betree step?
    // This sort of proof logic shouldn't have to be in the implementation.
    assert BC.BlockPointsToValidReferences(left_child, s.ephemeralSuperblock.graph);
    assert BC.BlockPointsToValidReferences(right_child, s.ephemeralSuperblock.graph);

    var s1, left_childref := alloc(k, s, left_child);
    if left_childref.None? {
      s' := s;
      assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; could not get ref\n";
      return;
    }

    var s2, right_childref := alloc(k, s1, right_child);
    if right_childref.None? {
      s' := s;
      assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; could not get ref\n";
      return;
    }

    var split_parent_pivots := Sequences.insert(fused_parent.pivotTable, pivot, slot);
    var split_parent_children := replace1with2(fused_parent.children.value, left_childref.value, right_childref.value, slot);
    var split_parent_buckets := replace1with2(fused_parent.buckets, map[], map[], slot);
    var split_parent := BT.G.Node(
      split_parent_pivots,
      Some(split_parent_children),
      split_parent_buckets
    );

    forall r | r in BT.G.Successors(split_parent)
    ensures r in s2.ephemeralSuperblock.graph
    {
      assert BC.BlockPointsToValidReferences(fused_parent, s2.ephemeralSuperblock.graph);
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
    assert BC.BlockPointsToValidReferences(split_parent, s2.ephemeralSuperblock.graph);

    s' := write(k, s2, parentref, split_parent);

    ghost var splitStep := BT.NodeFusion(
      parentref,
      ref,
      left_childref.value,
      right_childref.value,
      fused_parent,
      split_parent,
      fused_child,
      left_child,
      right_child,
      slot,
      num_children_left,
      pivot
    );
    assert BT.ValidSplit(splitStep);
    ghost var step := BT.BetreeSplit(splitStep);
    BC.MakeTransaction3(k, s, s1, s2, s', BT.BetreeStepOps(step));
    assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BetreeMoveStep(step));
  }

  lemma ChildCanBePagedIn(k: Constants, s: Variables, ref: BT.G.Reference, childref: BT.G.Reference)
  requires M.Inv(k, s)
  requires s.Ready?
  requires childref !in s.cache
  requires ref in s.cache
  requires childref in BT.G.Successors(s.cache[ref])
  ensures childref in s.ephemeralSuperblock.lbas
  {
  }

  method flush(k: Constants, s: Variables, io: DiskIOHandler, ref: BT.G.Reference, slot: int)
  returns (s': Variables)
  requires s.Ready?
  requires ref in s.cache
  requires s.cache[ref].children.Some?
  requires 0 <= slot < |s.cache[ref].buckets|
  requires io.initialized()
  modifies io
  requires M.Inv(k, s)
  ensures M.Next(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()))
  {
    var node := s.cache[ref];
    var childref := node.children.value[slot];

    if (childref !in s.cache) {
      ChildCanBePagedIn(k, s, ref, childref);
      s' := PageIn(k, s, io, childref);
      return;
    }

    var child := s.cache[childref];

    var newchild := BT.AddMessagesToNode(child, node.buckets[slot]);

    assert BT.G.Successors(newchild) == BT.G.Successors(child);
    assert BC.BlockPointsToValidReferences(newchild, s.ephemeralSuperblock.graph);

    var s1, newchildref := alloc(k, s, newchild);
    if newchildref.None? {
      s' := s;
      assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; could not get ref\n";
      return;
    }

    var newparent := BT.G.Node(
        node.pivotTable,
        Some(node.children.value[slot := newchildref.value]),
        node.buckets[slot := map[]]
      );

    assert BC.BlockPointsToValidReferences(node, s1.ephemeralSuperblock.graph);
    forall ref | ref in BT.G.Successors(newparent) ensures ref in s1.ephemeralSuperblock.graph {
      if (ref == newchildref.value) {
      } else {
        assert ref in BT.G.Successors(node);
      }
    }
    assert BC.BlockPointsToValidReferences(newparent, s1.ephemeralSuperblock.graph);

    s' := write(k, s1, ref, newparent);

    ghost var flushStep := BT.NodeFlush(ref, node, childref, child, newchildref.value, newchild, slot);
    assert BT.ValidFlush(flushStep);
    ghost var step := BT.BetreeFlush(flushStep);
    BC.MakeTransaction2(k, s, s1, s', BT.BetreeStepOps(step));
    assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BetreeMoveStep(step));
  }

  method fixBigNode(k: Constants, s: Variables, io: DiskIOHandler, ref: BT.G.Reference, parentref: BT.G.Reference)
  returns (s': Variables)
  requires s.Ready?
  requires ref in s.cache
  requires parentref in s.ephemeralSuperblock.graph
  requires ref in s.ephemeralSuperblock.graph[parentref]
  requires io.initialized()
  modifies io
  requires M.Inv(k, s)
  ensures M.Next(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()))
  {
    if (ref !in s.cache) {
      s' := PageIn(k, s, io, ref);
      return;
    }

    var node := s.cache[ref];

    if i :| 0 <= i < |node.buckets| && |node.buckets[i]| > Marshalling.CapBucketSize() as int {
      if (node.children.Some?) {
        // internal node case: flush
        s' := flush(k, s, io, ref, i);
      } else {
        // leaf case
        var joined := BT.JoinBuckets(node.buckets);
        var pivots := GetNewPivots(joined);
        var buckets' := BT.SplitBucketOnPivots(pivots, joined);
        var newnode := BT.G.Node(pivots, None, buckets');

        s' := write(k, s, ref, newnode);

        //assert BT.ValidRepivot(BT.Repivot(ref, node, pivots));
        ghost var step := BT.BetreeRepivot(BT.Repivot(ref, node, pivots));
        BC.MakeTransaction1(k, s, s', BT.BetreeStepOps(step));
        assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BetreeMoveStep(step));
      }
    } else if |node.buckets| > Marshalling.CapNumBuckets() as int {
      if (parentref !in s.cache) {
        s' := PageIn(k, s, io, parentref);
        return;
      }

      var parent := s.cache[parentref];

      assert ref in BT.G.Successors(parent);
      var i :| 0 <= i < |parent.children.value| && parent.children.value[i] == ref;

      s' := doSplit(k, s, io, parentref, ref, i);
    } else {
      s' := s;
      assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.NoOpStep));
      print "giving up; fixBigNode\n";
    }
  }

  method sync(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables, success: bool)
  requires io.initialized()
  modifies io
  requires M.Inv(k, s)
  ensures M.Next(Ik(k), s, s',
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
          var succ := WriteSector(io, lba, BC.SectorBlock(s.cache[ref]));
          if (succ) {
            success := false;
            s' := s.(ephemeralSuperblock := s.ephemeralSuperblock.(lbas := s.ephemeralSuperblock.lbas[ref := lba]));
            assert BC.WriteBack(Ik(k), s, s', IDiskOp(io.diskOp()), ref);
            assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.WriteBackStep(ref)));
          } else {
            success := false;
            s' := s;
            assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.NoOpStep));
            print "giving up; sync could not write\n";
          }
        }
        case None => {
          success := false;
          s' := s;
          assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.NoOpStep));
          print "giving up; could not get lba\n";
        }
      }
    } else {
      var succ := WriteSector(io, BC.SuperblockLBA(), BC.SectorSuperblock(s.ephemeralSuperblock));
      if (succ) {
        success := true;
        s' := s.(persistentSuperblock := s.ephemeralSuperblock);
        assert BC.WriteBackSuperblock(Ik(k), s, s', IDiskOp(io.diskOp()));
        assert M.NextStep(Ik(k), s, s', UI.SyncOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.WriteBackSuperblockStep));
      } else {
        success := false;
        s' := s;
        assert M.NextStep(Ik(k), s, s', UI.NoOp, IDiskOp(io.diskOp()), M.BlockCacheMoveStep(BC.NoOpStep));
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
    M.NextPreservesInv(k, s, s', uiop, IDiskOp(io.diskOp()));
    hs.s := s';
    success := succ;
  }

  method handleQuery(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key)
  returns (v: Option<MS.Value>)
  {
    var s := hs.s;
    var s', value := query(k, s, io, key);
    var uiop := if value.Some? then UI.GetOp(key, value.value) else UI.NoOp;
    M.NextPreservesInv(k, s, s', uiop, IDiskOp(io.diskOp()));
    hs.s := s';
    v := value;
  }

  method handleInsert(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (success: bool)
  {
    var s := hs.s;
    var s', succ := insert(k, s, io, key, value);
    var uiop := if succ then UI.PutOp(key, value) else UI.NoOp;
    M.NextPreservesInv(k, s, s', uiop, IDiskOp(io.diskOp()));
    hs.s := s';
    success := succ;
  }

}
