include "Main.dfy"

include "../lib/Sets.dfy"
include "ByteBetreeBlockCacheSystem.dfy"
include "Marshalling.dfy"

module {:extern} Impl refines Main { 
  import ADM = ByteBetreeBlockCacheSystem

  import TTT = TwoThreeTree
  import BBC = BetreeBlockCache
  import BC = BetreeGraphBlockCache
  import BT = PivotBetreeSpec`Internal
  import Marshalling
  import Messages = ValueMessage
  import Pivots = PivotsLib
  import SSTable = SSTable
  import LBAType = LBAType`Internal
  import opened Sets
  import IS = ImplState
  import SD = AsyncSectorDisk

  import opened Maps
  import opened Sequences

  type Key = MS.Key
  type Message = Messages.Message

  type Constants = ADM.M.Constants
  type Variables = IS.Variables

  type HeapState = IS.ImplHeapState
  function HeapSet(hs: HeapState) : set<object> { IS.ImplHeapSet(hs) }

  function Ik(k: Constants) : ADM.M.Constants { k }
  function I(k: Constants, hs: HeapState) : ADM.M.Variables { IS.IVars(hs.s) }

  predicate Inv(k: Constants, hs: HeapState)
  {
    && IS.WFVars(hs.s)
    && BBC.Inv(k, IS.IVars(hs.s))
  }

  method InitState() returns (k: Constants, hs: HeapState)
  {
    k := BC.Constants();
    hs := new IS.ImplHeapState();

    BBC.InitImpliesInv(k, IS.IVars(hs.s));
  }

  predicate WFSector(sector: BC.Sector)
  {
    match sector {
      case SectorIndirectionTable(indirectionTable) => BC.WFCompleteIndirectionTable(indirectionTable)
      case SectorBlock(node) => BT.WFNode(node)
    }
  }

  method RequestRead(io: DiskIOHandler, addr: uint64)
  returns (id: D.ReqId)
  requires io.initialized()
  requires ADM.M.ValidAddr(addr)
  modifies io
  ensures ADM.M.ValidDiskOp(io.diskOp())
  ensures ADM.M.IDiskOp(io.diskOp()) == SD.ReqReadOp(id, SD.ReqRead(addr))
  {
    id := io.read(addr, ADM.M.BlockSize() as uint64);
  }

  function ISectorOpt(sector: Option<IS.Sector>) : Option<BC.Sector>
  requires sector.Some? ==> IS.WFSector(sector.value)
  {
    match sector {
      case None => None
      case Some(sector) => Some(IS.ISector(sector))
    }
  }

  method ReadSector(io: DiskIOHandler)
  returns (id: D.ReqId, sector: Option<IS.Sector>)
  requires io.diskOp().RespReadOp?
  ensures sector.Some? ==> IS.WFSector(sector.value)
  ensures ADM.M.IDiskOp(io.diskOp()) == SD.RespReadOp(id, SD.RespRead(ISectorOpt(sector)))
  {
    var id1, bytes := io.getReadResult();
    id := id1;
    if bytes.Length == ADM.M.BlockSize() {
      var sectorOpt := Marshalling.ParseSector(bytes);
      sector := sectorOpt;
    } else {
      sector := None;
    }
  }

  method RequestWrite(io: DiskIOHandler, addr: uint64, sector: IS.Sector)
  returns (id: Option<D.ReqId>)
  requires IS.WFSector(sector)
  requires sector.SectorBlock? ==> BT.WFNode(IS.INode(sector.block))
  requires sector.SectorBlock? ==> Marshalling.CappedNode(sector.block)
  requires io.initialized()
  requires ADM.M.ValidAddr(addr)
  modifies io
  ensures ADM.M.ValidDiskOp(io.diskOp())
  ensures id.Some? ==> ADM.M.IDiskOp(io.diskOp()) == SD.ReqWriteOp(id.value, SD.ReqWrite(addr, IS.ISector(sector)))
  ensures id.None? ==> ADM.M.IDiskOp(io.diskOp()) == SD.NoDiskOp
  {
    var bytes := Marshalling.MarshallSector(sector);
    if (bytes == null) {
      id := None;
    } else {
      var i := io.write(addr, bytes);
      id := Some(i);
    }
  }

  predicate stepsBetree(k: Constants, s: Variables, s': Variables, uiop: UI.Op, step: BT.BetreeStep)
  requires IS.WFVars(s)
  requires IS.WFVars(s')
  {
    ADM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), uiop, D.NoDiskOp, ADM.M.Step(BBC.BetreeMoveStep(step)))
  }

  predicate stepsBC(k: Constants, s: Variables, s': Variables, uiop: UI.Op, io: DiskIOHandler, step: BC.Step)
  requires IS.WFVars(s)
  requires IS.WFVars(s')
  reads io
  {
    ADM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), uiop, io.diskOp(), ADM.M.Step(BBC.BlockCacheMoveStep(step)))
  }

  predicate noop(k: Constants, s: Variables, s': Variables)
  requires IS.WFVars(s)
  requires IS.WFVars(s')
  {
    ADM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, D.NoDiskOp, ADM.M.Step(BBC.BlockCacheMoveStep(BC.NoOpStep)))
  }

  lemma LemmaIndirectionTableLBAValid()
  ensures ADM.M.ValidAddr(BC.IndirectionTableLBA())
  {
    LBAType.reveal_ValidAddr();
    assert BC.IndirectionTableLBA() as int == 0 * ADM.M.BlockSize();
  }

  method PageInIndirectionTableReq(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
  requires IS.WFVars(s)
  requires io.initialized();
  requires s.Unready?
  modifies io
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    if (s.outstandingIndirectionTableRead.None?) {
      LemmaIndirectionTableLBAValid();
      var id := RequestRead(io, BC.IndirectionTableLBA());
      s' := IS.Unready(Some(id), s.syncReqs);

      assert stepsBC(k, s, s', UI.NoOp, io, BC.PageInIndirectionTableReqStep);
    } else {
      s' := s;
      assert noop(k, s, s');
      print "PageInIndirectionTableReq: request already out\n";
    }
  }

  method PageInIndirectionTableResp(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
  requires IS.WFVars(s)
  requires io.diskOp().RespReadOp?
  requires s.Unready?
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    var id, sector := ReadSector(io);
    if (Some(id) == s.outstandingIndirectionTableRead && sector.Some? && sector.value.SectorIndirectionTable?) {
      s' := IS.Ready(sector.value.indirectionTable, None, sector.value.indirectionTable, None, map[], map[], s.syncReqs, map[], TTT.EmptyTree);
      assert stepsBC(k, s, s', UI.NoOp, io, BC.PageInIndirectionTableRespStep);
  assert ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp());
    } else {
      s' := s;
      assert stepsBC(k, s, s', UI.NoOp, io, BC.NoOpStep);
      print "giving up; did not get indirectionTable when reading\n";
    }
  }

  method PageInReq(k: Constants, s: Variables, io: DiskIOHandler, ref: BC.Reference)
  returns (s': Variables)
  requires io.initialized();
  requires s.Ready?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires ref in s.ephemeralIndirectionTable.lbas
  requires ref !in s.cache
  modifies io
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    if (BC.OutstandingRead(ref) in s.outstandingBlockReads.Values) {
      s' := s;
      assert noop(k, s, s');
      print "giving up; already an outstanding read for this ref\n";
    } else {
      var lba := s.ephemeralIndirectionTable.lbas[ref];
      assert BC.ValidLBAForNode(lba);
      var id := RequestRead(io, lba);
      s' := s.(outstandingBlockReads := s.outstandingBlockReads[id := BC.OutstandingRead(ref)]);

      assert BC.PageInReq(k, IS.IVars(s), IS.IVars(s'), ADM.M.IDiskOp(io.diskOp()), ref);
      assert stepsBC(k, s, s', UI.NoOp, io, BC.PageInReqStep(ref));
    }
  }

  lemma INodeRootEqINodeForEmptyRootBucket(node: IS.Node)
  requires IS.WFNode(node)
  ensures IS.INodeRoot(node, TTT.EmptyTree) == IS.INode(node);
  /*{
    assert BT.AddMessagesToBuckets(node.pivotTable, |node.buckets|, SSTable.ISeq(node.buckets),
          map[]) == SSTable.ISeq(node.buckets);
  }*/

  /*lemma LemmaPageInBlockCacheSet(s: Variables, ref: BT.G.Reference, node: IS.Node)
  requires IS.WFVars(s)
  requires s.Ready?
  requires ref !in s.cache
  requires IS.WFNode(node)
  ensures IS.ICache(s.cache, s.rootBucket)[ref := IS.INode(node)]
       == IS.ICache(s.cache[ref := node], s.rootBucket);
  {
    if (ref == BT.G.Root()) {
      //assert TTT.I(rootBucket) == map[];
      //assert BT.AddMessagesToBuckets(node.pivotTable, |node.buckets|, SSTable.ISeq(node.buckets),
      //    map[]) == IS.INode(node).buckets;
      INodeRootEqINodeForEmptyRootBucket(node);
      assert IS.INodeRoot(node, s.rootBucket) == IS.INode(node);
    }
    assert IS.INodeForRef(s.cache[ref := node], ref, s.rootBucket) == IS.INode(node);
    assert IS.ICache(s.cache[ref := node], s.rootBucket)[ref] == IS.INode(node);
  }*/

  method PageInResp(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
  requires io.diskOp().RespReadOp?
  requires s.Ready?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    var id, sector := ReadSector(io);

    if (id !in s.outstandingBlockReads) {
      s' := s;
      assert stepsBC(k, s, s', UI.NoOp, io, BC.NoOpStep);
      print "PageInResp: unrecognized id from Read\n";
      return;
    }

    // TODO we should probably remove the id from outstandingBlockReads
    // even in the case we don't do anything with it

    var ref := s.outstandingBlockReads[id].ref;
    
    if (ref !in s.ephemeralIndirectionTable.lbas || ref in s.cache) {
      s' := s;
      assert stepsBC(k, s, s', UI.NoOp, io, BC.NoOpStep);
      print "PageInResp: ref !in lbas or ref in s.cache\n";
      return;
    }

    var lba := s.ephemeralIndirectionTable.lbas[ref];

    if (sector.Some? && sector.value.SectorBlock?) {
      var node := sector.value.block;
      if (s.ephemeralIndirectionTable.graph[ref] == (if node.children.Some? then node.children.value else [])) {
        s' := s.(cache := s.cache[ref := sector.value.block])
               .(outstandingBlockReads := MapRemove1(s.outstandingBlockReads, id));

        INodeRootEqINodeForEmptyRootBucket(node);

        assert BC.PageInResp(k, IS.IVars(s), IS.IVars(s'), ADM.M.IDiskOp(io.diskOp()));
        assert stepsBC(k, s, s', UI.NoOp, io, BC.PageInRespStep);
      } else {
        s' := s;
        assert stepsBC(k, s, s', UI.NoOp, io, BC.NoOpStep);
        print "giving up; block does not match graph\n";
      }
    } else {
      s' := s;
      assert stepsBC(k, s, s', UI.NoOp, io, BC.NoOpStep);
      print "giving up; block read in was not block\n";
    }
  }

  method getFreeRef(s: Variables)
  returns (ref : Option<BT.G.Reference>)
  requires s.Ready?
  ensures ref.Some? ==> ref.value !in s.ephemeralIndirectionTable.graph
  ensures ref.Some? ==> ref.value !in s.cache
  {
    if r :| r !in s.ephemeralIndirectionTable.graph && r !in s.cache {
      ref := Some(r);
    } else {
      ref := None;
    }
    /*var v := s.ephemeralIndirectionTable.graph.Keys;

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
    }*/
  }

  method getFreeLba(s: Variables)
  returns (lba : Option<BC.LBA>)
  requires s.Ready?
  requires IS.WFVars(s)
  ensures lba.Some? ==> BC.ValidLBAForNode(lba.value)
  ensures lba.Some? ==> BC.LBAFree(IS.IVars(s), lba.value)
  {
    if i: uint64 :| (
      && i as int * LBAType.BlockSize() as int < 0x1_0000_0000_0000_0000
      && var l := i * LBAType.BlockSize();
      && BC.ValidLBAForNode(l)
      && l !in s.persistentIndirectionTable.lbas.Values
      && l !in s.ephemeralIndirectionTable.lbas.Values
      && (s.frozenIndirectionTable.Some? ==>
          l !in s.frozenIndirectionTable.value.lbas.Values)
      && (forall id | id in s.outstandingBlockWrites ::
          s.outstandingBlockWrites[id].lba != l)
    ) {
      lba := Some(i * LBAType.BlockSize());
    } else {
      lba := None;
    }
  /*
    var v1 := s.persistentIndirectionTable.lbas.Values;
    var v2 := s.ephemeralIndirectionTable.lbas.Values;

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
    */
  }

  method write(k: Constants, s: Variables, ref: BT.G.Reference, node: IS.Node)
  returns (s': Variables)
  requires s.Ready?
  requires IS.WFVars(s)
  requires ref in s.ephemeralIndirectionTable.graph
  requires ref in s.cache
  requires ref == BT.G.Root() ==> s.rootBucket == TTT.EmptyTree
  requires IS.WFNode(node)
  requires BC.BlockPointsToValidReferences(IS.INode(node), s.ephemeralIndirectionTable.graph)
  requires s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value.graph ==> ref in s.frozenIndirectionTable.value.lbas
  ensures IS.WFVars(s')
  ensures BC.Dirty(k, IS.IVars(s), IS.IVars(s'), ref, IS.INode(node))
  {
    if (ref == BT.G.Root()) {
      INodeRootEqINodeForEmptyRootBucket(node);
    }

    s' := s
      .(ephemeralIndirectionTable :=
        BC.IndirectionTable(
          MapRemove(s.ephemeralIndirectionTable.lbas, {ref}),
          s.ephemeralIndirectionTable.graph[ref := if node.children.Some? then node.children.value else []]
        ))
      .(cache := s.cache[ref := node]);
  }

  method alloc(k: Constants, s: Variables, node: IS.Node)
  returns (s': Variables, ref: Option<BT.G.Reference>)
  requires IS.WFVars(s)
  requires IS.WFNode(node)
  requires BC.Inv(k, IS.IVars(s));
  requires s.Ready?
  requires BC.BlockPointsToValidReferences(IS.INode(node), s.ephemeralIndirectionTable.graph)
  ensures IS.WFVars(s')
  ensures ref.Some? ==> BC.Alloc(k, IS.IVars(s), IS.IVars(s'), ref.value, IS.INode(node))
  ensures ref.None? ==> s' == s
  ensures s.rootBucket == s'.rootBucket
  {
    ref := getFreeRef(s);
    if (ref.Some?) {
      s' := s
        .(ephemeralIndirectionTable :=
          BC.IndirectionTable(
            s.ephemeralIndirectionTable.lbas,
            s.ephemeralIndirectionTable.graph[ref.value := if node.children.Some? then node.children.value else []]
          )
        )
        .(cache := s.cache[ref.value := node]);
    } else {
      s' := s;
    }
  }

  lemma LemmaInsertToRootBucket(node: IS.Node, rootBucket: IS.TreeMap, rootBucket': IS.TreeMap, key: Key, msg: Message)
  requires IS.WFNode(node)
  requires TTT.TTTree(rootBucket)
  requires TTT.TTTree(rootBucket')
  requires TTT.I(rootBucket') == TTT.I(rootBucket)[key := msg]
  ensures IS.INodeRoot(node, rootBucket') == BT.AddMessageToNode(IS.INodeRoot(node, rootBucket), key, msg)

  method InsertKeyValue(k: Constants, s: Variables, key: MS.Key, value: MS.Value)
  returns (s': Variables, success: bool)
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires BT.G.Root() in s.cache
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), if success then UI.PutOp(key, value) else UI.NoOp, D.NoDiskOp)
  {
    if ((s.frozenIndirectionTable.Some? && BT.G.Root() in s.frozenIndirectionTable.value.graph) && !(BT.G.Root() in s.frozenIndirectionTable.value.lbas)) {
      // TODO write out the root here instead of giving up
      s' := s;
      success := false;
      assert noop(k, s, s');
      print "giving up; can't dirty root when frozen is not written yet\n";
      return;
    }

    var msg := Messages.Define(value);

    ghost var baseroot := s.cache[BT.G.Root()];

    ghost var r := Pivots.Route(baseroot.pivotTable, key);
    ghost var bucket := baseroot.buckets[r];

    assert BC.BlockPointsToValidReferences(IS.INodeRoot(baseroot, s.rootBucket), s.ephemeralIndirectionTable.graph);
    //assert IS.INode(oldroot).children == IS.INode(newroot).children;
    //assert BC.BlockPointsToValidReferences(IS.INode(newroot), s.ephemeralIndirectionTable.graph);

    var newRootBucket := TTT.Insert(s.rootBucket, key, msg);
    s' := s
        .(rootBucket := newRootBucket)
        .(ephemeralIndirectionTable :=
        BC.IndirectionTable(
          MapRemove(s.ephemeralIndirectionTable.lbas, {BT.G.Root()}),
          s.ephemeralIndirectionTable.graph
        ));
    success := true;

    ghost var oldroot := IS.INodeRoot(baseroot, s.rootBucket);
    ghost var newroot := IS.INodeRoot(baseroot, newRootBucket);
    LemmaInsertToRootBucket(baseroot, s.rootBucket, newRootBucket, key, msg);
    assert newroot == BT.AddMessageToNode(oldroot, key, msg);

    assert BT.G.Successors(newroot) == BT.G.Successors(oldroot);

    assert BC.Dirty(Ik(k), IS.IVars(s), IS.IVars(s'), BT.G.Root(), newroot);
    assert BC.OpStep(Ik(k), IS.IVars(s), IS.IVars(s'), BT.G.WriteOp(BT.G.Root(), newroot));
    assert BC.OpStep(Ik(k), IS.IVars(s), IS.IVars(s'), BT.BetreeStepOps(BT.BetreeInsert(BT.MessageInsertion(key, msg, oldroot)))[0]);
    assert BC.OpTransaction(Ik(k), IS.IVars(s), IS.IVars(s'), BT.BetreeStepOps(BT.BetreeInsert(BT.MessageInsertion(key, msg, oldroot))));
    assert BBC.BetreeMove(Ik(k), IS.IVars(s), IS.IVars(s'), UI.PutOp(key, value), SD.NoDiskOp, BT.BetreeInsert(BT.MessageInsertion(key, msg, oldroot)));
    assert stepsBetree(k, s, s', UI.PutOp(key, value), BT.BetreeInsert(BT.MessageInsertion(key, msg, oldroot)));
  }

  method TryRootBucketLookup(k: Constants, s: Variables, io: DiskIOHandler, key: MS.Key)
  returns (res: Option<MS.Value>)
  requires io.initialized()
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires s.Ready?
  modifies io
  ensures res.Some? ==> ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s),
    UI.GetOp(key, res.value), io.diskOp())
  ensures res.None? ==> io.initialized()
  ensures res.None? ==> key !in TTT.I(s.rootBucket)
  {
    var qres := TTT.Query(s.rootBucket, key);
    if (qres.ValueForKey?) {
      assert qres.value.Define?;
      res := Some(qres.value.value);

      ghost var lookup := [BT.G.ReadOp(BT.G.Root(), IS.INodeRoot(s.cache[BT.G.Root()], s.rootBucket))];

      assert BT.NodeLookup(IS.INodeRoot(s.cache[BT.G.Root()], s.rootBucket), key) == TTT.I(s.rootBucket)[key];

      assert BT.InterpretLookup(lookup, key) == TTT.I(s.rootBucket)[key]
          == qres.value;
      //assert BT.InterpretLookupAccountingForLeaf(lookup, key) == qres.value;

      //assert BT.ValidQuery(BT.LookupQuery(key, res.value, lookup));
      //assert BBC.BetreeMove(Ik(k), IS.IVars(s), IS.IVars(s),
      //  UI.GetOp(key, res.value),
      //  ADM.M.IDiskOp(io.diskOp()),
      //  BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup)));

      assert stepsBetree(k, s, s,
        UI.GetOp(key, res.value),
        BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup)));

    } else {
      res := None;
    }
  }

  // note: I split this out because of sequence-related trigger loop problems
  ghost method AugmentLookup(lookup: seq<BT.G.ReadOp>, ref: BT.G.Reference, node: BT.G.Node, key: MS.Key, cache: map<BT.G.Reference, BT.G.Node>, graph: map<BT.G.Reference, seq<BT.G.Reference>>)
  returns (lookup' : seq<BT.G.ReadOp>)
  requires |lookup| > 0 ==> BT.WFLookupForKey(lookup, key)
  requires forall i | 0 <= i < |lookup| :: lookup[i].ref in graph
  requires forall i | 0 <= i < |lookup| :: MapsTo(cache, lookup[i].ref, lookup[i].node)
  requires |lookup| == 0 ==> ref == BT.G.Root()
  requires |lookup| > 0 ==> Last(lookup).node.children.Some?
  requires |lookup| > 0 ==> Last(lookup).node.children.value[Pivots.Route(Last(lookup).node.pivotTable, key)] == ref
  requires BT.WFNode(node)
  requires MapsTo(cache, ref, node);
  requires ref in graph;
  ensures BT.WFLookupForKey(lookup', key)
  ensures Last(lookup').node == node
  ensures BT.InterpretLookup(lookup', key) == Messages.Merge(BT.InterpretLookup(lookup, key), BT.NodeLookup(node, key))
  ensures forall i | 0 <= i < |lookup'| :: lookup'[i].ref in graph
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

  lemma NodeLookupIfNotInRootBucket(node: IS.Node, rootBucket: IS.TreeMap, key: Key)
  requires IS.WFNode(node)
  requires TTT.TTTree(rootBucket)
  requires key !in TTT.I(rootBucket)
  ensures BT.NodeLookup(IS.INode(node), key) == BT.NodeLookup(IS.INodeRoot(node, rootBucket), key)

  method query(k: Constants, s: Variables, io: DiskIOHandler, key: MS.Key)
  returns (s': Variables, res: Option<MS.Value>)
  requires io.initialized()
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  modifies io
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'),
    if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
    io.diskOp())
  {
    if (s.Unready?) {
      s' := PageInIndirectionTableReq(k, s, io);
      res := None;
    } else {
      var ref := BT.G.Root();
      var msg := Messages.IdentityMessage();
      ghost var lookup := [];

      var rootLookup := TryRootBucketLookup(k, s, io, key);
      if (rootLookup.Some?) {
        s' := s;
        res := rootLookup;
        return;
      }

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
      invariant forall i | 0 <= i < |lookup| :: lookup[i].ref in s.ephemeralIndirectionTable.graph
      invariant forall i | 0 <= i < |lookup| :: MapsTo(IS.ICache(s.cache, s.rootBucket), lookup[i].ref, lookup[i].node)
      invariant ref in s.ephemeralIndirectionTable.graph
      invariant !exiting ==> msg == BT.InterpretLookup(lookup, key)
      invariant io.initialized()
      invariant key !in TTT.I(s.rootBucket)
      {
        assert !exiting;
        loopBound := loopBound - 1;

        if (ref !in s.cache) {
          s' := PageInReq(k, s, io, ref);
          res := None;

          exiting := true;
          return;
        } else {
          var node := s.cache[ref];
          ghost var inode := IS.INodeForRef(s.cache, ref, s.rootBucket);
          lookup := AugmentLookup(lookup, ref, inode, key, IS.ICache(s.cache, s.rootBucket), s.ephemeralIndirectionTable.graph); // ghost-y

          var r := Pivots.ComputeRoute(node.pivotTable, key);
          var sstMsg := SSTable.Query(node.buckets[r], key);
          var lookupMsg := if sstMsg.Some? then sstMsg.value else Messages.IdentityMessage();
          msg := Messages.Merge(msg, lookupMsg);

          NodeLookupIfNotInRootBucket(s.cache[BT.G.Root()], s.rootBucket, key);
          assert lookupMsg == BT.NodeLookup(inode, key);

          if (node.children.Some?) {
            var r1 := Pivots.ComputeRoute(node.pivotTable, key);
            ref := node.children.value[r1];
            assert ref in BT.G.Successors(inode);
            assert ref in s.ephemeralIndirectionTable.graph;
          } else {
            if !msg.Define? {
              // Case where we reach leaf and find nothing
              s' := s;
              res := Some(MS.V.DefaultValue());

              assert BBC.BetreeMove(Ik(k), IS.IVars(s), IS.IVars(s'),
                if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
                ADM.M.IDiskOp(io.diskOp()),
                BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup)));

              assert stepsBetree(k, s, s',
                if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
                BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup)));

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
        assert BBC.BetreeMove(Ik(k), IS.IVars(s), IS.IVars(s'),
          UI.GetOp(key, res.value),
          ADM.M.IDiskOp(io.diskOp()),
          BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup)));
        assert stepsBetree(k, s, s',
          if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
          BT.BetreeQuery(BT.LookupQuery(key, res.value, lookup)));
      } else {
        // loop bound exceeded; do nothing :/
        s' := s;
        res := None;

        assert noop(k, s, s');
        print "giving up; did not reach Leaf or a Define\n";
      }
    }
  }

  method insert(k: Constants, s: Variables, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (s': Variables, success: bool)
  requires io.initialized()
  modifies io
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'),
    if success then UI.PutOp(key, value) else UI.NoOp,
    io.diskOp())
  {
    if (s.Unready?) {
      s' := PageInIndirectionTableReq(k, s, io);
      success := false;
      return;
    }

    if (BT.G.Root() !in s.cache) {
      s' := PageInReq(k, s, io, BT.G.Root());
      success := false;
      return;
    }

    s', success := InsertKeyValue(k, s, key, value);
  }

  predicate method deallocable(s: Variables, ref: BT.G.Reference) {
    && s.Ready?
    && ref in s.ephemeralIndirectionTable.graph
    && ref != BT.G.Root()
    && forall r | r in s.ephemeralIndirectionTable.graph :: ref !in s.ephemeralIndirectionTable.graph[r]
  }

  method dealloc(k: Constants, s: Variables, io: DiskIOHandler, ref: BT.G.Reference)
  returns (s': Variables)
  requires IS.WFVars(s)
  requires io.initialized()
  requires deallocable(s, ref)
  modifies io
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    if (s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value.graph && ref !in s.frozenIndirectionTable.value.lbas) {
      s' := s;
      assert noop(k, s, s');
      print "giving up; dealloc can't dealloc because frozen isn't written\n";
      return;
    }

    s' :=
      s.(ephemeralIndirectionTable :=
        BC.IndirectionTable(
          MapRemove(s.ephemeralIndirectionTable.lbas, {ref}),
          MapRemove(s.ephemeralIndirectionTable.graph, {ref})
        )
      )
      .(cache := MapRemove(s.cache, {ref}))
      .(outstandingBlockReads := BC.OutstandingBlockReadsRemoveRef(s.outstandingBlockReads, ref));
    assert BC.Unalloc(Ik(k), IS.IVars(s), IS.IVars(s'), ADM.M.IDiskOp(io.diskOp()), ref);
    assert BBC.BlockCacheMove(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, ADM.M.IDiskOp(io.diskOp()), BC.UnallocStep(ref));
    assert stepsBC(k, s, s', UI.NoOp, io, BC.UnallocStep(ref));
  }

  method fixBigRoot(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
  requires IS.WFVars(s)
  requires s.Ready?
  requires io.initialized()
  requires s.rootBucket == TTT.EmptyTree
  modifies io
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    if (BT.G.Root() !in s.cache) {
      s' := PageInReq(k, s, io, BT.G.Root());
      return;
    }

    INodeRootEqINodeForEmptyRootBucket(s.cache[BT.G.Root()]);

    if (s.frozenIndirectionTable.Some? && BT.G.Root() in s.frozenIndirectionTable.value.graph && BT.G.Root() !in s.frozenIndirectionTable.value.lbas) {
      s' := s;
      assert noop(k, s, s');
      print "giving up; fixBigRoot can't run because frozen isn't written\n";
      return;
    }

    var oldroot := s.cache[BT.G.Root()];
    var s1, newref := alloc(k, s, oldroot);
    match newref {
      case None => {
        s' := s;
        assert noop(k, s, s');
        print "giving up; could not allocate ref\n";
      }
      case Some(newref) => {
        var newroot := IS.Node([], Some([newref]), [SSTable.Empty()]);

        assert BT.G.Root() in s.cache;
        assert BT.G.Root() in IS.ICache(s.cache, s.rootBucket);
        assert BT.G.Root() in IS.ICache(s1.cache, s1.rootBucket);
        assert BT.G.Root() in s1.cache;

        s' := write(k, s1, BT.G.Root(), newroot);

        ghost var growth := BT.RootGrowth(IS.INode(oldroot), newref);
        assert IS.INode(newroot) == BT.G.Node([], Some([growth.newchildref]), [map[]]);
        ghost var step := BT.BetreeGrow(growth);
        BC.MakeTransaction2(k, IS.IVars(s), IS.IVars(s1), IS.IVars(s'), BT.BetreeStepOps(step));
        //assert BBC.BetreeMove(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, ADM.M.IDiskOp(io.diskOp()), step);
        assert stepsBetree(k, s, s', UI.NoOp, step);
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
    var cLeft := Pivots.ComputeCutoffForLeft(node.pivotTable, pivot);
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
    var cRight := Pivots.ComputeCutoffForRight(node.pivotTable, pivot);
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

  // TODO FIXME this method is flaky and takes a long time to verify
  method {:fuel BT.NodeHasWFBuckets,0} doSplit(k: Constants, s: Variables, io: DiskIOHandler, parentref: BT.G.Reference, ref: BT.G.Reference, slot: int)
  returns (s': Variables)
  requires s.Ready?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires ref in s.ephemeralIndirectionTable.graph
  requires parentref in s.ephemeralIndirectionTable.graph
  requires ref in s.cache
  requires parentref in s.cache
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires s.cache[parentref].children.value[slot] == ref
  requires io.initialized()
  requires s.rootBucket == TTT.EmptyTree // FIXME we don't actually need this unless paretnref is root
  modifies io
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    if (s.frozenIndirectionTable.Some? && parentref in s.frozenIndirectionTable.value.graph && parentref !in s.frozenIndirectionTable.value.lbas) {
      s' := s;
      assert noop(k, s, s');
      print "giving up; doSplit can't run because frozen isn't written\n";
      return;
    }

    var fused_parent := s.cache[parentref];
    var fused_child := s.cache[ref];

    INodeRootEqINodeForEmptyRootBucket(fused_parent);
    INodeRootEqINodeForEmptyRootBucket(fused_child);

    assert BT.WFNode(IS.ICache(s.cache, s.rootBucket)[parentref]);
    assert BT.WFNode(IS.ICache(s.cache, s.rootBucket)[ref]);

    var lbound := (if slot > 0 then Some(fused_parent.pivotTable[slot - 1]) else None);
    var ubound := (if slot < |fused_parent.pivotTable| then Some(fused_parent.pivotTable[slot]) else None);
    var child := CutoffNode(fused_child, lbound, ubound);

    if !SSTable.IsEmpty(fused_parent.buckets[slot]) {
      s' := s;
      assert noop(k, s, s');
      print "giving up; trying to split but parent has non-empty buffer\n";
      return;
    }

    if (|child.pivotTable| == 0) {
      // TODO there should be an operation which just
      // cuts off the node and doesn't split it.
      s' := s;
      assert noop(k, s, s');
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
    ensures r in s.ephemeralIndirectionTable.graph
    {
      assert BC.BlockPointsToValidReferences(IS.INode(fused_child), s.ephemeralIndirectionTable.graph);
      assert r in BT.G.Successors(IS.INode(fused_child));
    }
    assert BC.BlockPointsToValidReferences(IS.INode(child), s.ephemeralIndirectionTable.graph);

    Pivots.WFSlice(child.pivotTable, 0, num_children_left - 1);
    Pivots.WFSuffix(child.pivotTable, num_children_left);
    INodeRootEqINodeForEmptyRootBucket(left_child);
    INodeRootEqINodeForEmptyRootBucket(right_child);

    // TODO can we get BetreeBlockCache to ensure that will be true generally whenever taking a betree step?
    // This sort of proof logic shouldn't have to be in the implementation.
    assert BC.BlockPointsToValidReferences(IS.INode(left_child), s.ephemeralIndirectionTable.graph);
    assert BC.BlockPointsToValidReferences(IS.INode(right_child), s.ephemeralIndirectionTable.graph);

    var s1, left_childref := alloc(k, s, left_child);
    if left_childref.None? {
      s' := s;
      assert noop(k, s, s');
      print "giving up; could not get ref\n";
      return;
    }

    var s2, right_childref := alloc(k, s1, right_child);
    if right_childref.None? {
      s' := s;
      assert noop(k, s, s');
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
    ensures r in s2.ephemeralIndirectionTable.graph
    {
      assert BC.BlockPointsToValidReferences(IS.INode(fused_parent), s2.ephemeralIndirectionTable.graph);
      var idx :| 0 <= idx < |split_parent_children| && split_parent_children[idx] == r;
      if (idx < slot) {
        assert r == fused_parent.children.value[idx];
        assert r in s2.ephemeralIndirectionTable.graph;
      } else if (idx == slot) {
        assert r == left_childref.value;
        assert r in s2.ephemeralIndirectionTable.graph;
      } else if (idx == slot + 1) {
        assert r == right_childref.value;
        assert r in s2.ephemeralIndirectionTable.graph;
      } else {
        assert r == fused_parent.children.value[idx-1];
        assert r in s2.ephemeralIndirectionTable.graph;
      }
    }
    assert BC.BlockPointsToValidReferences(IS.INode(split_parent), s2.ephemeralIndirectionTable.graph);

    assert parentref in s.cache;
    assert parentref in IS.ICache(s.cache, s.rootBucket);
    assert parentref in IS.ICache(s1.cache, s1.rootBucket);
    assert parentref in IS.ICache(s2.cache, s2.rootBucket);
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
    assert stepsBetree(k, s, s', UI.NoOp, step);
  }

  method flush(k: Constants, s: Variables, io: DiskIOHandler, ref: BT.G.Reference, slot: int)
  returns (s': Variables)
  requires IS.WFVars(s)
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable.graph
  requires ref in s.cache
  requires s.cache[ref].children.Some?
  requires 0 <= slot < |s.cache[ref].buckets|
  requires io.initialized()
  requires s.rootBucket == TTT.EmptyTree // FIXME we don't actually need this unless we're flushing the root
  modifies io
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    if (s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value.graph && ref !in s.frozenIndirectionTable.value.lbas) {
      s' := s;
      assert noop(k, s, s');
      print "giving up; flush can't run because frozen isn't written";
      return;
    }

    var node := s.cache[ref];

    INodeRootEqINodeForEmptyRootBucket(node);

    assert IS.INode(node) == IS.ICache(s.cache, s.rootBucket)[ref];
    assert BT.WFNode(IS.INode(node));

    var childref := node.children.value[slot];

    assert childref in BT.G.Successors(IS.INode(node));

    if (childref !in s.cache) {
      s' := PageInReq(k, s, io, childref);
      return;
    }

    var child := s.cache[childref];

    INodeRootEqINodeForEmptyRootBucket(child);

    assert IS.INode(child) == IS.ICache(s.cache, s.rootBucket)[childref];
    assert BT.WFNode(IS.INode(child));

    if (!(
        && |node.buckets[slot].strings| < 0x800_0000_0000_0000
        && |node.buckets[slot].starts| < 0x800_0000_0000_0000
        && (forall i | 0 <= i < |child.buckets| :: |child.buckets[i].strings| < 0x800_0000_0000_0000)
        && (forall i | 0 <= i < |child.buckets| :: |child.buckets[i].starts| < 0x800_0000_0000_0000)
    )) {
      s' := s;
      assert noop(k, s, s');
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
    assert BC.BlockPointsToValidReferences(IS.INode(newchild), s.ephemeralIndirectionTable.graph);

    var s1, newchildref := alloc(k, s, newchild);
    if newchildref.None? {
      s' := s;
      assert noop(k, s, s');
      print "giving up; could not get ref\n";
      return;
    }

    var newparent := IS.Node(
        node.pivotTable,
        Some(node.children.value[slot := newchildref.value]),
        node.buckets[slot := SSTable.Empty()]
      );

    assert BC.BlockPointsToValidReferences(IS.INode(node), s1.ephemeralIndirectionTable.graph);
    forall ref | ref in BT.G.Successors(IS.INode(newparent)) ensures ref in s1.ephemeralIndirectionTable.graph {
      if (ref == newchildref.value) {
      } else {
        assert ref in BT.G.Successors(IS.INode(node));
      }
    }
    assert BC.BlockPointsToValidReferences(IS.INode(newparent), s1.ephemeralIndirectionTable.graph);

    assert ref in s.cache;
    assert ref in IS.ICache(s.cache, s.rootBucket);
    assert ref in IS.ICache(s1.cache, s1.rootBucket);
    assert ref in s1.cache;

    s' := write(k, s1, ref, newparent);

    ghost var flushStep := BT.NodeFlush(ref, IS.INode(node), childref, IS.INode(child), newchildref.value, IS.INode(newchild), slot);
    assert BT.ValidFlush(flushStep);
    ghost var step := BT.BetreeFlush(flushStep);
    assert IS.INode(newparent) == BT.FlushOps(flushStep)[1].node;
    BC.MakeTransaction2(k, IS.IVars(s), IS.IVars(s1), IS.IVars(s'), BT.BetreeStepOps(step));
    assert stepsBetree(k, s, s', UI.NoOp, step);
  }

  method {:fuel BT.JoinBuckets,0} fixBigNode(k: Constants, s: Variables, io: DiskIOHandler, ref: BT.G.Reference, parentref: BT.G.Reference)
  returns (s': Variables)
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires ref in s.cache
  requires parentref in s.ephemeralIndirectionTable.graph
  requires ref in s.ephemeralIndirectionTable.graph[parentref]
  requires io.initialized()
  modifies io
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    if (ref !in s.cache) {
      s' := PageInReq(k, s, io, ref);
      return;
    }

    if (s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value.graph && ref !in s.frozenIndirectionTable.value.lbas) {
      s' := s;
      assert noop(k, s, s');
      print "giving up; fixBigRoot can't run because frozen isn't written";
      return;
    }

    var node := s.cache[ref];

    if i :| 0 <= i < |node.buckets| && !Marshalling.CappedBucket(node.buckets[i]) {
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
          assert noop(k, s, s');
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
          assert noop(k, s, s');
          print "giving up; stuff too big to call Split\n";
          return;
        }

        var buckets' := SSTable.SplitOnPivots(joined, pivots);
        var newnode := IS.Node(pivots, None, buckets');

        s' := write(k, s, ref, newnode);

        //assert BT.ValidRepivot(BT.Repivot(ref, node, pivots));
        ghost var step := BT.BetreeRepivot(BT.Repivot(ref, IS.INode(node), pivots));
        BC.MakeTransaction1(k, IS.IVars(s), IS.IVars(s'), BT.BetreeStepOps(step));
        assert stepsBetree(k, s, s', UI.NoOp, step);
      }
    } else if |node.buckets| > Marshalling.CapNumBuckets() as int {
      if (parentref !in s.cache) {
        s' := PageInReq(k, s, io, parentref);
        return;
      }

      var parent := s.cache[parentref];

      assert ref in BT.G.Successors(IS.INode(parent));
      var i :| 0 <= i < |parent.children.value| && parent.children.value[i] == ref;

      s' := doSplit(k, s, io, parentref, ref, i);
    } else {
      s' := s;
      assert noop(k, s, s');
      print "giving up; fixBigNode\n";
    }
  }

  method {:fuel BC.GraphClosed,0} sync(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
  requires io.initialized()
  modifies io
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    if (s.Unready?) {
      // TODO we could just do nothing here instead
      s' := PageInIndirectionTableReq(k, s, io);
      return;
    }

    if (s.outstandingIndirectionTableWrite.Some?) {
      s' := s;
      assert noop(k, s, s');
      print "sync: giving up; frozen table is currently being written\n";
      return;
    }

    // Plan:
    // - If the indirection table is not frozen then:
    //    - If anything can be unalloc'ed, do it
    //    - If any node is too big, do split/flush/whatever to shrink it
    //    - Freeze the indirection table
    // - Otherwise:
    //    - If any block in the frozen table doesn't have an LBA, Write it to disk
    //    - Write the frozenIndirectionTable to disk

    if (s.frozenIndirectionTable.None?) {
      if ref :| ref in s.ephemeralIndirectionTable.graph && deallocable(s, ref) {
        s' := dealloc(k, s, io, ref);
      } else if ref :| ref in s.ephemeralIndirectionTable.graph && ref in s.cache && !Marshalling.CappedNode(s.cache[ref]) {
        if (ref == BT.G.Root()) {
          s' := fixBigRoot(k, s, io);
        } else {
          assert !deallocable(s, ref);
          assert !(forall r | r in s.ephemeralIndirectionTable.graph :: ref !in s.ephemeralIndirectionTable.graph[r]);
          assert !(forall r :: r in s.ephemeralIndirectionTable.graph ==> ref !in s.ephemeralIndirectionTable.graph[r]);
          assert (exists r :: !(r in s.ephemeralIndirectionTable.graph ==> ref !in s.ephemeralIndirectionTable.graph[r]));
          var r :| !(r in s.ephemeralIndirectionTable.graph ==> ref !in s.ephemeralIndirectionTable.graph[r]);
          s' := fixBigNode(k, s, io, ref, r);
        }
      } else {
        s' := s.(frozenIndirectionTable := Some(s.ephemeralIndirectionTable))
            .(syncReqs := BC.syncReqs3to2(s.syncReqs));
        assert BC.Freeze(Ik(k), IS.IVars(s), IS.IVars(s'), ADM.M.IDiskOp(io.diskOp()));
        assert stepsBC(k, s, s', UI.NoOp, io, BC.FreezeStep);
        return;
      }
    } else if ref :| ref in s.frozenIndirectionTable.value.graph && ref !in s.frozenIndirectionTable.value.lbas {
      if (!Marshalling.CappedNode(s.cache[ref])) {
        // TODO we should be able to prove this is impossible by adding an invariant
        // about frozenIndirectionTable (that is, we should never be freezing a table
        // with too-big nodes in it)
        s' := s;
        assert noop(k, s, s');
        print "sync: giving up; frozen table has big node rip (TODO we should prove this case impossible)\n";
        return;
      }

      if (ref in s.ephemeralIndirectionTable.lbas) {
        // TODO we should be able to prove this is impossible as well
        s' := s;
        assert noop(k, s, s');
        print "sync: giving up; ref already in ephemeralIndirectionTable.lbas but not frozen";
        return;
      }

      var lba := getFreeLba(s);
      match lba {
        case Some(lba) => {
          var id := RequestWrite(io, lba, IS.SectorBlock(s.cache[ref]));
          if (id.Some?) {
            s' := s
              .(ephemeralIndirectionTable := BC.AssignRefToLBA(s.ephemeralIndirectionTable, ref, lba))
              .(frozenIndirectionTable := Some(BC.AssignRefToLBA(s.frozenIndirectionTable.value, ref, lba)))
              .(outstandingBlockWrites := s.outstandingBlockWrites[id.value := BC.OutstandingWrite(ref, lba)]);
            assert BC.WriteBackReq(Ik(k), IS.IVars(s), IS.IVars(s'), ADM.M.IDiskOp(io.diskOp()), ref);
            assert stepsBC(k, s, s', UI.NoOp, io, BC.WriteBackReqStep(ref));
          } else {
            s' := s;
            assert noop(k, s, s');
            print "sync: giving up; write req failed\n";
          }
        }
        case None => {
          s' := s;
          assert noop(k, s, s');
          print "sync: giving up; could not get lba\n";
        }
      }
    } else if (s.outstandingBlockWrites != map[]) {
      s' := s;
      assert noop(k, s, s');
      print "sync: giving up; blocks are still being written\n";
    } else {
      LBAType.reveal_ValidAddr();
      var id := RequestWrite(io, BC.IndirectionTableLBA(), IS.SectorIndirectionTable(s.frozenIndirectionTable.value));
      if (id.Some?) {
        s' := s.(outstandingIndirectionTableWrite := id);
        assert BC.WriteBackIndirectionTableReq(Ik(k), IS.IVars(s), IS.IVars(s'), ADM.M.IDiskOp(io.diskOp()));
        assert stepsBC(k, s, s', UI.NoOp, io, BC.WriteBackIndirectionTableReqStep);
      } else {
        s' := s;
        assert noop(k, s, s');
        print "sync: giving up; write back indirection table failed (no id)\n";
      }
    }
  }

  method readResponse(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
  requires io.diskOp().RespReadOp?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    if (s.Unready?) {
      s' := PageInIndirectionTableResp(k, s, io);
    } else {
      s' := PageInResp(k, s, io);
    }
  }

  method writeResponse(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables)
  requires io.diskOp().RespWriteOp?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    var id := io.getWriteResult();
    if (s.Ready? && s.outstandingIndirectionTableWrite == Some(id)) {
      s' := s.(outstandingIndirectionTableWrite := None)
             .(frozenIndirectionTable := None)
             .(persistentIndirectionTable := s.frozenIndirectionTable.value)
             .(syncReqs := BC.syncReqs2to1(s.syncReqs));
      assert stepsBC(k, s, s', UI.NoOp, io, BC.WriteBackIndirectionTableRespStep);
    } else if (s.Ready? && id in s.outstandingBlockWrites) {
      s' := s.(outstandingBlockWrites := MapRemove1(s.outstandingBlockWrites, id));
      assert stepsBC(k, s, s', UI.NoOp, io, BC.WriteBackRespStep);
    } else {
      s' := s;
      assert stepsBC(k, s, s', UI.NoOp, io, BC.NoOpStep);
    }
  }

  method freeId<A>(syncReqs: map<int, A>) returns (id: int)
  ensures id !in syncReqs
  {
    var s := syncReqs.Keys;
    if (|s| == 0) {
      id := 0;
    } else {
      var maxId := maximumInt(syncReqs.Keys);
      id := maxId + 1;
    }
  }

  method pushSync(k: Constants, s: Variables, io: DiskIOHandler)
  returns (s': Variables, id: int)
  requires io.initialized()
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.PushSyncOp(id), io.diskOp())
  {
    id := freeId(s.syncReqs);
    s' := s.(syncReqs := s.syncReqs[id := BC.State3]);
    assert stepsBC(k, s, s', UI.PushSyncOp(id), io, BC.PushSyncReqStep(id));
  }

  method popSync(k: Constants, s: Variables, io: DiskIOHandler, id: int)
  returns (s': Variables, success: bool)
  requires io.initialized()
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  modifies io
  ensures IS.WFVars(s')
  ensures ADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), if success then UI.PopSyncOp(id) else UI.NoOp, io.diskOp())
  {
    if (id in s.syncReqs && s.syncReqs[id] == BC.State1) {
      success := true;
      s' := s.(syncReqs := MapRemove1(s.syncReqs, id));
      assert stepsBC(k, s, s', UI.PopSyncOp(id), io, BC.PopSyncReqStep(id));
    } else {
      success := false;
      s' := sync(k, s, io);
    }
  }

  ////////// Top-level handlers

  method handlePushSync(k: Constants, hs: HeapState, io: DiskIOHandler)
  returns (id: int)
  {
    var s := hs.s;
    var s', id1 := pushSync(k, s, io);
    id := id1;
    var uiop := UI.PushSyncOp(id);
    BBC.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
  }

  method handlePopSync(k: Constants, hs: HeapState, io: DiskIOHandler, id: int)
  returns (success: bool)
  {
    var s := hs.s;
    var s', succ := popSync(k, s, io, id);
    success := succ;
    var uiop := if succ then UI.PopSyncOp(id) else UI.NoOp;
    BBC.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
  }

  method handleQuery(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key)
  returns (v: Option<MS.Value>)
  {
    var s := hs.s;
    var s', value := query(k, s, io, key);
    var uiop := if value.Some? then UI.GetOp(key, value.value) else UI.NoOp;
    BBC.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
    v := value;
  }

  method handleInsert(k: Constants, hs: HeapState, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (success: bool)
  {
    var s := hs.s;
    var s', succ := insert(k, s, io, key, value);
    var uiop := if succ then UI.PutOp(key, value) else UI.NoOp;
    BBC.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
    success := succ;
  }

  method handleReadResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  {
    var s := hs.s;
    var s' := readResponse(k, s, io);
    var uiop := UI.NoOp;
    BBC.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
  }

  method handleWriteResponse(k: Constants, hs: HeapState, io: DiskIOHandler)
  {
    var s := hs.s;
    var s' := writeResponse(k, s, io);
    var uiop := UI.NoOp;
    BBC.NextPreservesInv(k, IS.IVars(s), IS.IVars(s'), uiop, ADM.M.IDiskOp(io.diskOp()));
    hs.s := s';
  }
}
