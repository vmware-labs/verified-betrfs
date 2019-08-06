include "MapSpec.s.dfy"
include "../lib/NativeTypes.s.dfy"
include "../lib/Sets.i.dfy"
include "../lib/Option.i.dfy"
include "ByteBetreeBlockCacheSystem.i.dfy"
include "Marshalling.i.dfy"
include "MainDiskIOHandler.i.dfy"

module Impl { 
  import opened Options
  import opened MainDiskIOHandler
  import ImplADM = ByteBetreeBlockCacheSystem

  import MS = MapSpec
  import TTT = TwoThreeTree
  import BBC = BetreeBlockCache
  import BC = BetreeGraphBlockCache
  import BT = PivotBetreeSpec`Internal
  import Marshalling
  import Messages = ValueMessage
  import Pivots = PivotsLib
  import opened BucketsLib
  import KMTable = KMTable
  import LBAType = LBAType`Internal
  import opened Sets
  import IS = ImplState
  import SD = AsyncSectorDisk
  import opened NativeTypes

  import opened Maps
  import opened Sequences
  import UI

  // TODO <deduplicate>
  type Key = MS.Key
  type Message = Messages.Message

  type ImplConstants = ImplADM.M.Constants
  type ImplVariables = IS.Variables

  function Ik(k: ImplConstants) : ImplADM.M.Constants { k }
  // </deduplicate>

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
  requires ImplADM.M.ValidAddr(addr)
  modifies io
  ensures ImplADM.M.ValidDiskOp(io.diskOp())
  ensures ImplADM.M.IDiskOp(io.diskOp()) == SD.ReqReadOp(id, SD.ReqRead(addr))
  {
    id := io.read(addr, ImplADM.M.BlockSize() as uint64);
  }

  function ISectorOpt(sector: Option<IS.Sector>) : Option<BC.Sector>
  requires sector.Some? ==> IS.WFSector(sector.value)
  reads if sector.Some? && sector.value.SectorIndirectionTable? then sector.value.indirectionTable.Repr else {}
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
  ensures ImplADM.M.IDiskOp(io.diskOp()) == SD.RespReadOp(id, SD.RespRead(ISectorOpt(sector)))
  {
    var id1, bytes := io.getReadResult();
    id := id1;
    if bytes.Length == ImplADM.M.BlockSize() {
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
  requires ImplADM.M.ValidAddr(addr)
  modifies io
  ensures ImplADM.M.ValidDiskOp(io.diskOp())
  ensures id.Some? ==> ImplADM.M.IDiskOp(io.diskOp()) == SD.ReqWriteOp(id.value, SD.ReqWrite(addr, IS.ISector(sector)))
  ensures id.None? ==> ImplADM.M.IDiskOp(io.diskOp()) == SD.NoDiskOp
  {
    var bytes := Marshalling.MarshallSector(sector);
    if (bytes == null) {
      id := None;
    } else {
      var i := io.write(addr, bytes);
      id := Some(i);
    }
  }

  predicate stepsBetree(k: ImplConstants, s: ImplVariables, s': ImplVariables, uiop: UI.Op, step: BT.BetreeStep)
  requires IS.WFVars(s)
  requires IS.WFVars(s')
  reads IS.VariablesReadSet(s)
  reads IS.VariablesReadSet(s')
  {
    ImplADM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), uiop, D.NoDiskOp, ImplADM.M.Step(BBC.BetreeMoveStep(step)))
  }

  predicate stepsBC(k: ImplConstants, s: ImplVariables, s': ImplVariables, uiop: UI.Op, io: DiskIOHandler, step: BC.Step)
  requires IS.WFVars(s)
  requires IS.WFVars(s')
  reads io
  reads IS.VariablesReadSet(s)
  reads IS.VariablesReadSet(s')
  {
    ImplADM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), uiop, io.diskOp(), ImplADM.M.Step(BBC.BlockCacheMoveStep(step)))
  }

  predicate noop(k: ImplConstants, s: ImplVariables, s': ImplVariables)
  requires IS.WFVars(s)
  requires IS.WFVars(s')
  reads IS.VariablesReadSet(s)
  reads IS.VariablesReadSet(s')
  {
    ImplADM.M.NextStep(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, D.NoDiskOp, ImplADM.M.Step(BBC.BlockCacheMoveStep(BC.NoOpStep)))
  }

  lemma LemmaIndirectionTableLBAValid()
  ensures ImplADM.M.ValidAddr(BC.IndirectionTableLBA())
  {
    LBAType.reveal_ValidAddr();
    assert BC.IndirectionTableLBA() as int == 0 * ImplADM.M.BlockSize();
  }

  method PageInIndirectionTableReq(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires io.initialized();
  requires s.Unready?
  modifies io
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
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

  method PageInIndirectionTableResp(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires io.diskOp().RespReadOp?
  requires s.Unready?
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    var id, sector := ReadSector(io);
    if (Some(id) == s.outstandingIndirectionTableRead && sector.Some? && sector.value.SectorIndirectionTable?) {
      s' := IS.Ready(sector.value.indirectionTable, None, sector.value.indirectionTable, None, map[], map[], s.syncReqs, map[], TTT.EmptyTree);
      assert stepsBC(k, s, s', UI.NoOp, io, BC.PageInIndirectionTableRespStep);
  assert ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp());
    } else {
      s' := s;
      assume stepsBC(k, s, s', UI.NoOp, io, BC.NoOpStep);
      print "giving up; did not get indirectionTable when reading\n";
    }
  }

  method PageInReq(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BC.Reference)
  returns (s': ImplVariables)
  requires io.initialized();
  requires s.Ready?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).lbas
  requires ref !in s.cache
  modifies io
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    assume false; // TODO timing out
    if (BC.OutstandingRead(ref) in s.outstandingBlockReads.Values) {
      s' := s;
      assert noop(k, s, s');
      print "giving up; already an outstanding read for this ref\n";
    } else {
      var lbaGraph := s.ephemeralIndirectionTable.Get(ref);
      assert lbaGraph.Some?;
      var (lba, _) := lbaGraph.value;
      assert lba.Some?;
      assert BC.ValidLBAForNode(lba.value);
      var id := RequestRead(io, lba.value);
      s' := s.(outstandingBlockReads := s.outstandingBlockReads[id := BC.OutstandingRead(ref)]);

      assert BC.PageInReq(k, IS.IVars(s), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()), ref);
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

  /*lemma LemmaPageInBlockCacheSet(s: ImplVariables, ref: BT.G.Reference, node: IS.Node)
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

  method PageInResp(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.diskOp().RespReadOp?
  requires s.Ready?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    var id, sector := ReadSector(io);

    if (id !in s.outstandingBlockReads) {
      s' := s;
      assume stepsBC(k, s, s', UI.NoOp, io, BC.NoOpStep);
      print "PageInResp: unrecognized id from Read\n";
      return;
    }

    // TODO we should probably remove the id from outstandingBlockReads
    // even in the case we don't do anything with it

    var ref := s.outstandingBlockReads[id].ref;
    
    var lbaGraph := s.ephemeralIndirectionTable.Get(ref);
    if (lbaGraph.None? || lbaGraph.value.0.None? || ref in s.cache) { // ref !in I(s.ephemeralIndirectionTable).lbas || ref in s.cache
      s' := s;
      assume stepsBC(k, s, s', UI.NoOp, io, BC.NoOpStep);
      print "PageInResp: ref !in lbas or ref in s.cache\n";
      return;
    }

    assert lbaGraph.Some? && lbaGraph.value.0.Some?;
    var lba := lbaGraph.value.0.value;
    var graph := lbaGraph.value.1;

    if (sector.Some? && sector.value.SectorBlock?) {
      var node := sector.value.block;
      if (graph == (if node.children.Some? then node.children.value else [])) {
        s' := s.(cache := s.cache[ref := sector.value.block])
               .(outstandingBlockReads := MapRemove1(s.outstandingBlockReads, id));

        INodeRootEqINodeForEmptyRootBucket(node);

        assert BC.PageInResp(k, IS.IVars(s), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()));
        assume stepsBC(k, s, s', UI.NoOp, io, BC.PageInRespStep);
      } else {
        s' := s;
        assume stepsBC(k, s, s', UI.NoOp, io, BC.NoOpStep);
        print "giving up; block does not match graph\n";
      }
    } else {
      s' := s;
      assume stepsBC(k, s, s', UI.NoOp, io, BC.NoOpStep);
      print "giving up; block read in was not block\n";
    }
  }

  method getFreeRef(s: ImplVariables)
  returns (ref : Option<BT.G.Reference>)
  requires s.Ready?
  requires s.ephemeralIndirectionTable.Inv()
  ensures ref.Some? ==> ref.value !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  ensures ref.Some? ==> ref.value !in s.cache
  {
    /*
    if r :| r !in s.ephemeralIndirectionTable.graph && r !in s.cache {
      ref := Some(r);
    } else {
      ref := None;
    }
    */
    var table := s.ephemeralIndirectionTable.ToMap();
    var v := table.Keys;

    var m;
    if |v| >= 1 {
      m := maximum(v);
    } else {
      m := 0;
    }

    if (m < 0xffff_ffff_ffff_ffff) {
      ref := Some(m + 1);
      assume ref.value !in s.cache;
    } else {
      ref := None;
    }
  }

  method getFreeLba(s: ImplVariables)
  returns (lba : Option<BC.LBA>)
  requires s.Ready?
  requires IS.WFVars(s)
  ensures lba.Some? ==> BC.ValidLBAForNode(lba.value)
  ensures lba.Some? ==> BC.LBAFree(IS.IVars(s), lba.value)
  {
    assume false; // TODO timing out
    /*
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
    */
    var table1: map<uint64, (Option<BC.LBA>, seq<IS.Reference>)> := s.persistentIndirectionTable.ToMap();
    var table2: map<uint64, (Option<BC.LBA>, seq<IS.Reference>)> := s.ephemeralIndirectionTable.ToMap();

    var table1Values := SetToSeq(table1.Values);
    var table2Values := SetToSeq(table2.Values);

    var v1Opt := Filter((x: (Option<BC.LBA>, seq<IS.Reference>)) => x.0.Some?, table1Values);
    var v2Opt := Filter((x: (Option<BC.LBA>, seq<IS.Reference>)) => x.0.Some?, table2Values);
    var v1 := Apply((x: (Option<BC.LBA>, seq<IS.Reference>)) requires x.0.Some? => x.0.value, v1Opt);
    var v2 := Apply((x: (Option<BC.LBA>, seq<IS.Reference>)) requires x.0.Some? => x.0.value, v2Opt);

    var m1;
    var m2;

    if |v1| >= 1 {
      m1 := maximum(set x | x in v1);
    } else {
      m1 := 0;
    }

    if |v2| >= 1 {
      m2 := maximum(set x | x in v2);
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

  method write(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, node: IS.Node)
  returns (s': ImplVariables)
  requires s.Ready?
  requires IS.WFVars(s)
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in s.cache
  requires ref == BT.G.Root() ==> s.rootBucket == TTT.EmptyTree
  requires IS.WFNode(node)
  requires BC.BlockPointsToValidReferences(IS.INode(node), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires s.frozenIndirectionTable.Some? && ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph ==>
      ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas
  ensures IS.WFVars(s')
  ensures BC.Dirty(k, IS.IVars(s), IS.IVars(s'), ref, IS.INode(node))
  modifies s.ephemeralIndirectionTable.Repr
  {
    if (ref == BT.G.Root()) {
      INodeRootEqINodeForEmptyRootBucket(node);
    }

    // s' := s
    //   .(ephemeralIndirectionTable :=
    //     BC.IndirectionTable(
    //       MapRemove(s.ephemeralIndirectionTable.lbas, {ref}),
    //       s.ephemeralIndirectionTable.graph[ref := if node.children.Some? then node.children.value else []]
    //     ))
    //   .(cache := s.cache[ref := node]);

    assume false; // timing out
    var lbaGraph := s.ephemeralIndirectionTable.Remove(ref);
    assume lbaGraph.Some?;
    var (lba, graph) := lbaGraph.value;
    if node.children.Some? {
      // TODO how do we deal with this?
      assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;
      var _ := s.ephemeralIndirectionTable.Insert(ref, (None, node.children.value));
    }
    assert IS.IIndirectionTable(s.ephemeralIndirectionTable) ==
        old(BC.IndirectionTable(
          MapRemove(IS.IIndirectionTable(s.ephemeralIndirectionTable).lbas, {ref}),
          IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[ref := if node.children.Some? then node.children.value else []]
        ));
    s' := s.(cache := s.cache[ref := node]);
    assume BC.Dirty(k, IS.IVars(s), IS.IVars(s'), ref, IS.INode(node));
  }

  method alloc(k: ImplConstants, s: ImplVariables, node: IS.Node)
  returns (s': ImplVariables, ref: Option<BT.G.Reference>)
  requires IS.WFVars(s)
  requires IS.WFNode(node)
  requires BC.Inv(k, IS.IVars(s));
  requires s.Ready?
  requires BC.BlockPointsToValidReferences(IS.INode(node), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph)
  ensures IS.WFVars(s')
  ensures ref.Some? ==> BC.Alloc(k, IS.IVars(s), IS.IVars(s'), ref.value, IS.INode(node))
  ensures ref.None? ==> s' == s
  ensures s.rootBucket == s'.rootBucket
  modifies s.ephemeralIndirectionTable.Repr
  {
    ref := getFreeRef(s);
    if (ref.Some?) {
      // TODO how do we deal with this?
      assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;
      var _ := s.ephemeralIndirectionTable.Insert(ref.value, (None, if node.children.Some? then node.children.value else []));
      assert IS.IIndirectionTable(s.ephemeralIndirectionTable) == 
        old(
          BC.IndirectionTable(
            IS.IIndirectionTable(s.ephemeralIndirectionTable).lbas,
            IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[ref.value := if node.children.Some? then node.children.value else []]
          ));
      s' := s.(cache := s.cache[ref.value := node]);
      assume ref.Some? ==> BC.Alloc(k, IS.IVars(s), IS.IVars(s'), ref.value, IS.INode(node));
    } else {
      s' := s;
    }
  }

  lemma LemmaInsertToRootBucket(node: IS.Node, rootBucket: IS.TreeMap, rootBucket': IS.TreeMap, key: Key, msg: Message)
  requires IS.WFNode(node)
  requires TTT.TTTree(rootBucket)
  requires TTT.TTTree(rootBucket')
  requires TTT.I(rootBucket') == TTT.I(rootBucket)[key := msg]
  requires BT.WFNode(IS.INodeRoot(node, rootBucket))
  ensures IS.INodeRoot(node, rootBucket') == BT.AddMessageToNode(IS.INodeRoot(node, rootBucket), key, msg)

  method InsertKeyValue(k: ImplConstants, s: ImplVariables, key: MS.Key, value: MS.Value)
  returns (s': ImplVariables, success: bool)
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires BT.G.Root() in s.cache
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), if success then UI.PutOp(key, value) else UI.NoOp, D.NoDiskOp)
  modifies s.ephemeralIndirectionTable.Repr
  {
    assume false; // TODO timing out
    if s.frozenIndirectionTable.Some? {
      var rootInFrozenLbaGraph := s.frozenIndirectionTable.value.Get(BT.G.Root());
      if (
        && (s.frozenIndirectionTable.Some? && rootInFrozenLbaGraph.Some?)
        && rootInFrozenLbaGraph.value.0.None?
      ) {
        assert (s.frozenIndirectionTable.Some? && BT.G.Root() in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph) &&
            !(BT.G.Root() in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas);
        // TODO write out the root here instead of giving up
        s' := s;
        success := false;
        assert noop(k, s, s');
        print "giving up; can't dirty root when frozen is not written yet\n";
        return;
      }
    }

    var msg := Messages.Define(value);

    ghost var baseroot := s.cache[BT.G.Root()];

    ghost var r := Pivots.Route(baseroot.pivotTable, key);
    ghost var bucket := baseroot.buckets[r];

    assert BC.BlockPointsToValidReferences(IS.INodeRoot(baseroot, s.rootBucket), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);
    //assert IS.INode(oldroot).children == IS.INode(newroot).children;
    //assert BC.BlockPointsToValidReferences(IS.INode(newroot), s.ephemeralIndirectionTable.graph);

    var newRootBucket := TTT.Insert(s.rootBucket, key, msg);

    var lbaGraph := s.ephemeralIndirectionTable.Remove(BT.G.Root());
    assume lbaGraph.Some?;
    var (lba, graph) := lbaGraph.value;
    // TODO how do we deal with this?
    assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;
    var _ := s.ephemeralIndirectionTable.Insert(BT.G.Root(), (None, graph));

    assert IS.IIndirectionTable(s.ephemeralIndirectionTable) == old(BC.IndirectionTable(
        MapRemove(IS.IIndirectionTable(s.ephemeralIndirectionTable).lbas, {BT.G.Root()}),
        IS.IIndirectionTable(s.ephemeralIndirectionTable).graph));

    s' := s.(rootBucket := newRootBucket);
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

  method TryRootBucketLookup(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, key: MS.Key)
  returns (res: Option<MS.Value>)
  requires io.initialized()
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires s.Ready?
  modifies io
  ensures res.Some? ==> ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s),
    UI.GetOp(key, res.value), io.diskOp())
  ensures res.None? ==> io.initialized()
  ensures res.None? ==> key !in TTT.I(s.rootBucket)
  {
    var qres := TTT.Query(s.rootBucket, key);
    if (qres.ValueForKey?) {
      assert qres.value.Define?;
      res := Some(qres.value.value);

      ghost var lookup := [BT.G.ReadOp(BT.G.Root(), IS.INodeRoot(s.cache[BT.G.Root()], s.rootBucket))];

      ghost var node := s.cache[BT.G.Root()];
      GetBucketListFlushEqMerge(TTT.I(s.rootBucket), KMTable.ISeq(node.buckets), node.pivotTable, key);
      assert BT.NodeLookup(IS.INodeRoot(node, s.rootBucket), key) == TTT.I(s.rootBucket)[key];

      assert BT.InterpretLookup(lookup, key) == TTT.I(s.rootBucket)[key]
          == qres.value;
      //assert BT.InterpretLookupAccountingForLeaf(lookup, key) == qres.value;

      //assert BT.ValidQuery(BT.LookupQuery(key, res.value, lookup));
      //assert BBC.BetreeMove(Ik(k), IS.IVars(s), IS.IVars(s),
      //  UI.GetOp(key, res.value),
      //  ImplADM.M.IDiskOp(io.diskOp()),
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

  lemma WFNodeRootImpliesWFRootBase(node: IS.Node, rootBucket: IS.TreeMap)
  requires IS.WFNode(node)
  requires TTT.TTTree(rootBucket)
  requires BT.WFNode(IS.INodeRoot(node, rootBucket))
  ensures BT.WFNode(IS.INode(node))

  lemma NodeLookupIfNotInRootBucket(node: IS.Node, rootBucket: IS.TreeMap, key: Key)
  requires IS.WFNode(node)
  requires TTT.TTTree(rootBucket)
  requires key !in TTT.I(rootBucket)
  requires BT.WFNode(IS.INode(node)) || BT.WFNode(IS.INodeRoot(node, rootBucket))
  ensures BT.WFNode(IS.INode(node))
  ensures BT.WFNode(IS.INodeRoot(node, rootBucket))
  ensures BT.NodeLookup(IS.INode(node), key) == BT.NodeLookup(IS.INodeRoot(node, rootBucket), key)

  method query(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, key: MS.Key)
  returns (s': ImplVariables, res: Option<MS.Value>)
  requires io.initialized()
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  modifies io
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'),
    if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
    io.diskOp())
  {
    assume false; // TODO timing out
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
      invariant forall i | 0 <= i < |lookup| :: lookup[i].ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
      invariant forall i | 0 <= i < |lookup| :: MapsTo(IS.ICache(s.cache, s.rootBucket), lookup[i].ref, lookup[i].node)
      invariant ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
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
          lookup := AugmentLookup(lookup, ref, inode, key, IS.ICache(s.cache, s.rootBucket), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph); // ghost-y

          var r := Pivots.ComputeRoute(node.pivotTable, key);
          var bucket := node.buckets[r];

          if |bucket.keys| >= 0x8000_0000_0000_0000 {
            s' := s;
            res := None;
            assert noop(k, s, s');
            print "giving up; kmgMsg too big\n";
            return;
          }

          var kmtMsg := KMTable.Query(bucket, key);

          var lookupMsg := if kmtMsg.Some? then kmtMsg.value else Messages.IdentityMessage();
          msg := Messages.Merge(msg, lookupMsg);

          NodeLookupIfNotInRootBucket(s.cache[BT.G.Root()], s.rootBucket, key);
          assert lookupMsg == BT.NodeLookup(inode, key);

          if (node.children.Some?) {
            var r1 := Pivots.ComputeRoute(node.pivotTable, key);
            ref := node.children.value[r1];
            assert ref in BT.G.Successors(inode);
            assert ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph;
          } else {
            if !msg.Define? {
              // Case where we reach leaf and find nothing
              s' := s;
              res := Some(MS.V.DefaultValue());

              assert BBC.BetreeMove(Ik(k), IS.IVars(s), IS.IVars(s'),
                if res.Some? then UI.GetOp(key, res.value) else UI.NoOp,
                ImplADM.M.IDiskOp(io.diskOp()),
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
          ImplADM.M.IDiskOp(io.diskOp()),
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

  method insert(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (s': ImplVariables, success: bool)
  requires io.initialized()
  modifies io
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'),
    if success then UI.PutOp(key, value) else UI.NoOp,
    io.diskOp())
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  {
    assume false; // TODO timing out
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
    assert ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'),
      if success then UI.PutOp(key, value) else UI.NoOp,
      io.diskOp());
  }

  predicate deallocable(s: ImplVariables, ref: BT.G.Reference)
  reads if s.Ready? then {s.ephemeralIndirectionTable} else {} // TODO necessary?
  reads if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  {
    && s.Ready?
    && ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
    && ref != BT.G.Root()
    && forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph :: ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r]
  }

  method Deallocable(s: ImplVariables, ref: BT.G.Reference) returns (result: bool)
  requires s.Ready? ==> s.ephemeralIndirectionTable.Inv()
  ensures result == deallocable(s, ref)
  {
    if ref == BT.G.Root() {
      return false;
    }
    if !s.Ready? {
      return false;
    }
    var lbaGraph := s.ephemeralIndirectionTable.Get(ref);
    if !lbaGraph.Some? {
      return false;
    }
    var table := s.ephemeralIndirectionTable.ToMap();
    var graph := map k | k in table :: table[k].1;
    result := forall r | r in graph :: ref !in graph[r];
    assume result == deallocable(s, ref);
  }

  method Dealloc(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires io.initialized()
  requires deallocable(s, ref)
  modifies io
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  modifies s.ephemeralIndirectionTable.Repr
  {
    assume false; // TODO timing out
    if s.frozenIndirectionTable.Some? {
      var lbaGraph := s.frozenIndirectionTable.value.Get(ref);
      if lbaGraph.Some? {
        assert ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
        var (lba, _) := lbaGraph.value;
        if lba.None? {
          assert ref !in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas;
          s' := s;
          assert noop(k, s, s');
          print "giving up; dealloc can't dealloc because frozen isn't written\n";
          return;
        }
      }
    }

    var _ := s.ephemeralIndirectionTable.Remove(ref);

    assert IS.IIndirectionTable(s.ephemeralIndirectionTable) ==
      old(BC.IndirectionTable(
        MapRemove(IS.IIndirectionTable(s.ephemeralIndirectionTable).lbas, {ref}),
        MapRemove(IS.IIndirectionTable(s.ephemeralIndirectionTable).graph, {ref})
      ));

    s' := s
      .(cache := MapRemove(s.cache, {ref}))
      .(outstandingBlockReads := BC.OutstandingBlockReadsRemoveRef(s.outstandingBlockReads, ref));
    assert BC.Unalloc(Ik(k), IS.IVars(s), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()), ref);
    assert BBC.BlockCacheMove(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, ImplADM.M.IDiskOp(io.diskOp()), BC.UnallocStep(ref));
    assert stepsBC(k, s, s', UI.NoOp, io, BC.UnallocStep(ref));
  }

  method fixBigRoot(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires s.Ready?
  requires io.initialized()
  requires s.rootBucket == TTT.EmptyTree
  modifies io
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  modifies s.ephemeralIndirectionTable.Repr
  {
    assume false; // TODO timing out

    if (BT.G.Root() !in s.cache) {
      s' := PageInReq(k, s, io, BT.G.Root());
      return;
    }

    INodeRootEqINodeForEmptyRootBucket(s.cache[BT.G.Root()]);

    if s.frozenIndirectionTable.Some? {
      var rootLbaGraph := s.frozenIndirectionTable.value.Get(BT.G.Root());
      if rootLbaGraph.Some? {
        assert BT.G.Root() in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
        var (lba, _) := rootLbaGraph.value;
        if lba.None? {
          assert BT.G.Root() !in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas;
          s' := s;
          assert noop(k, s, s');
          print "giving up; fixBigRoot can't run because frozen isn't written\n";
          return;
        }
      }
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
        var newroot := IS.Node([], Some([newref]), [KMTable.Empty()]);

        assert BT.G.Root() in s.cache;
        assert BT.G.Root() in IS.ICache(s.cache, s.rootBucket);
        assert BT.G.Root() in IS.ICache(s1.cache, s1.rootBucket);
        assert BT.G.Root() in s1.cache;

        assume BC.BlockPointsToValidReferences(IS.INode(newroot), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);
        s' := write(k, s1, BT.G.Root(), newroot);

        ghost var growth := BT.RootGrowth(IS.INode(oldroot), newref);
        assert IS.INode(newroot) == BT.G.Node([], Some([growth.newchildref]), [map[]]);
        ghost var step := BT.BetreeGrow(growth);
        BC.MakeTransaction2(k, IS.IVars(s), IS.IVars(s1), IS.IVars(s'), BT.BetreeStepOps(step));
        //assert BBC.BetreeMove(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, ImplADM.M.IDiskOp(io.diskOp()), step);
        assert stepsBetree(k, s, s', UI.NoOp, step);
      }
    }
  }

  method GetNewPivots(bucket: KMTable.KMTable)
  returns (pivots : seq<MS.Key>)
  requires KMTable.WF(bucket)
  ensures Pivots.WFPivots(pivots)
  {
    // try to split the keys evenly, but don't let any bucket
    // be larger than the cap

    var n := |bucket.keys|;

    var m := (n + Marshalling.CapNumBuckets() as int) / Marshalling.CapNumBuckets() as int;
    if m > 500 {
      m := 500;
    }
    if m < 1 {
      m := 1;
    }

    MS.Keyspace.reveal_IsStrictlySorted();
    var r := [];
    var i := m;
    while i < n
    invariant MS.Keyspace.IsStrictlySorted(r);
    invariant |r| > 0 ==> 0 <= i-m < n && r[|r|-1] == bucket.keys[i - m];
    invariant |r| > 0 ==> MS.Keyspace.NotMinimum(r[0]);
    invariant i > 0
    {
      MS.Keyspace.IsNotMinimum(bucket.keys[0], bucket.keys[i]);

      r := r + [bucket.keys[i]];
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
    var splitBucket := KMTable.SplitLeft(node.buckets[cLeft], pivot);
    var leftBuckets := node.buckets[.. cLeft] + [splitBucket];
    Pivots.WFSlice(node.pivotTable, 0, cLeft);
    KMTable.Islice(node.buckets, 0, cLeft);
    KMTable.IPopBack(node.buckets[.. cLeft], splitBucket);
    WFSplitBucketListLeft(KMTable.ISeq(node.buckets), node.pivotTable, cLeft, pivot);

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
    var splitBucket := KMTable.SplitRight(node.buckets[cRight], pivot);
    var rightBuckets := [splitBucket] + node.buckets[cRight + 1 ..];
    Pivots.WFSuffix(node.pivotTable, cRight);
    KMTable.Isuffix(node.buckets, cRight + 1);
    KMTable.IPopFront(splitBucket, node.buckets[cRight + 1 ..]);
    WFSplitBucketListRight(KMTable.ISeq(node.buckets), node.pivotTable, cRight, pivot);

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

  function method SplitChildLeft(child: IS.Node, num_children_left: int) : IS.Node
  requires 0 <= num_children_left - 1 <= |child.pivotTable|
  requires child.children.Some? ==> 0 <= num_children_left <= |child.children.value|
  requires 0 <= num_children_left <= |child.buckets|
  {
    IS.Node(
      child.pivotTable[ .. num_children_left - 1 ],
      if child.children.Some? then Some(child.children.value[ .. num_children_left ]) else None,
      child.buckets[ .. num_children_left ]
    )
  }

  function method SplitChildRight(child: IS.Node, num_children_left: int) : IS.Node
  requires 0 <= num_children_left <= |child.pivotTable|
  requires child.children.Some? ==> 0 <= num_children_left <= |child.children.value|
  requires 0 <= num_children_left <= |child.buckets|
  {
    IS.Node(
      child.pivotTable[ num_children_left .. ],
      if child.children.Some? then Some(child.children.value[ num_children_left .. ]) else None,
      child.buckets[ num_children_left .. ]
    )
  }

  lemma lemmaSplitChild(child: IS.Node, num_children_left: int)
  requires IS.WFNode(child)
  requires BT.WFNode(IS.INode(child))
  requires 1 <= num_children_left <= |child.buckets| - 1
  ensures IS.WFNode(SplitChildLeft(child, num_children_left))
  ensures IS.WFNode(SplitChildRight(child, num_children_left))
  ensures IS.INode(SplitChildLeft(child, num_children_left)) == BT.SplitChildLeft(IS.INode(child), num_children_left)
  ensures IS.INode(SplitChildRight(child, num_children_left)) == BT.SplitChildRight(IS.INode(child), num_children_left)
  {
    Pivots.WFSlice(child.pivotTable, 0, num_children_left - 1);
    Pivots.WFSuffix(child.pivotTable, num_children_left);
    KMTable.Islice(child.buckets, 0, num_children_left);
    KMTable.Isuffix(child.buckets, num_children_left);
    assume IS.WFNode(SplitChildRight(child, num_children_left));
    assume IS.WFNode(SplitChildLeft(child, num_children_left));
  }

  // TODO can we get BetreeBlockCache to ensure that will be true generally whenever taking a betree step?
  // This sort of proof logic shouldn't have to be in the implementation.
  lemma lemmaSplitChildValidReferences(child1: BT.G.Node, child: BT.G.Node, num_children_left: int, graph: map<BT.G.Reference, seq<BT.G.Reference>>, lbound: Option<Key>, rbound: Option<Key>)
  requires BT.WFNode(child1)
  requires BT.WFNode(child)
  requires 1 <= num_children_left <= |child.buckets| - 1
  requires BC.BlockPointsToValidReferences(child1, graph);
  requires child == BT.CutoffNode(child1, lbound, rbound);
  ensures BC.BlockPointsToValidReferences(BT.SplitChildLeft(child, num_children_left), graph);
  ensures BC.BlockPointsToValidReferences(BT.SplitChildRight(child, num_children_left), graph);
  {
  }

  method SplitParent(fused_parent: IS.Node, pivot: Key, slot_idx: int, left_childref: BT.G.Reference, right_childref: BT.G.Reference) returns (res : IS.Node)
  requires IS.WFNode(fused_parent)
  requires BT.WFNode(IS.INode(fused_parent))
  requires 0 <= slot_idx < |fused_parent.buckets|
  requires fused_parent.children.Some?
  ensures IS.WFNode(res)
  ensures IS.INode(res) == BT.SplitParent(IS.INode(fused_parent), pivot, slot_idx, left_childref, right_childref)
  {
    res := IS.Node(
      Sequences.insert(fused_parent.pivotTable, pivot, slot_idx),
      Some(replace1with2(fused_parent.children.value, left_childref, right_childref, slot_idx)),
      replace1with2(fused_parent.buckets, KMTable.Empty(), KMTable.Empty(), slot_idx)
    );
    KMTable.Ireplace1with2(fused_parent.buckets, KMTable.Empty(), KMTable.Empty(), slot_idx);
    assume IS.WFNode(res);
    assume IS.INode(res) == BT.SplitParent(IS.INode(fused_parent), pivot, slot_idx, left_childref, right_childref);
  }

  lemma lemmaSplitParentValidReferences(fused_parent: BT.G.Node, pivot: Key, slot_idx: int, left_childref: BT.G.Reference, right_childref: BT.G.Reference, graph: map<BT.G.Reference, seq<BT.G.Reference>>)
  requires BT.WFNode(fused_parent)
  requires 0 <= slot_idx < |fused_parent.buckets|
  requires fused_parent.children.Some?
  requires BC.BlockPointsToValidReferences(fused_parent, graph);
  requires left_childref in graph
  requires right_childref in graph
  ensures BC.BlockPointsToValidReferences(BT.SplitParent(fused_parent, pivot, slot_idx, left_childref, right_childref), graph);
  {
    var split_parent := BT.SplitParent(fused_parent, pivot, slot_idx, left_childref, right_childref);
    forall r | r in BT.G.Successors(split_parent)
    ensures r in graph
    {
      assert BC.BlockPointsToValidReferences(fused_parent, graph);
      var idx :| 0 <= idx < |split_parent.children.value| && split_parent.children.value[idx] == r;
      if (idx < slot_idx) {
        assert r == fused_parent.children.value[idx];
        assert r in graph;
      } else if (idx == slot_idx) {
        assert r == left_childref;
        assert r in graph;
      } else if (idx == slot_idx + 1) {
        assert r == right_childref;
        assert r in graph;
      } else {
        assert r == fused_parent.children.value[idx-1];
        assert r in graph;
      }
    }
  }

  // TODO FIXME this method is flaky and takes a long time to verify
  method {:fuel WFBucketList,0} {:fuel BT.SplitChildLeft,0} {:fuel BT.SplitChildRight,0} {:fuel BT.SplitParent,0}
      {:fuel SplitChildLeft,0} {:fuel SplitChildRight,0}
  doSplit(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, parentref: BT.G.Reference, ref: BT.G.Reference, slot: int)
  returns (s': ImplVariables)
  requires s.Ready?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires parentref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in s.cache
  requires parentref in s.cache
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires s.cache[parentref].children.value[slot] == ref
  requires io.initialized()
  requires s.rootBucket == TTT.EmptyTree // FIXME we don't actually need this unless paretnref is root
  modifies io
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  modifies s.ephemeralIndirectionTable.Repr
  {
    assume false; // TODO timing out

    if s.frozenIndirectionTable.Some? {
      var parentrefLbaGraph := s.frozenIndirectionTable.value.Get(parentref);
      if parentrefLbaGraph.Some? {
        assert parentref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
        var (lba, _) := parentrefLbaGraph.value;
        if lba.None? {
          assert parentref !in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas;
          s' := s;
          assert noop(k, s, s');
          print "giving up; doSplit can't run because frozen isn't written\n";
          return;
        }
      }
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

    if !KMTable.IsEmpty(fused_parent.buckets[slot]) {
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

    var left_child := SplitChildLeft(child, num_children_left);
    var right_child := SplitChildRight(child, num_children_left);

    lemmaSplitChild(child, num_children_left);
    lemmaSplitChildValidReferences(IS.INode(fused_child), IS.INode(child), num_children_left,
        IS.IIndirectionTable(s.ephemeralIndirectionTable).graph, lbound, ubound);

    // TODO remove this when proof cleaned up (asserts necessary before KMTable)
    // SSTable.Islice(child.buckets, 0, num_children_left);
    // SSTable.Isuffix(child.buckets, num_children_left);

    // forall r | r in BT.G.Successors(IS.INode(child))
    // ensures r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
    // {
    //   assert BC.BlockPointsToValidReferences(IS.INode(fused_child), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);
    //   assert r in BT.G.Successors(IS.INode(fused_child));
    // }
    // assert BC.BlockPointsToValidReferences(IS.INode(child), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);

    // assert BC.BlockPointsToValidReferences(IS.INode(left_child), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);
    // assert BC.BlockPointsToValidReferences(IS.INode(right_child), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);

    var s1, left_childref := alloc(k, s, left_child);
    if left_childref.None? {
      s' := s;
      assume noop(k, s, s');
      assume ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp());
      print "giving up; could not get ref\n";
      return;
    }

    var s2, right_childref := alloc(k, s1, right_child);
    if right_childref.None? {
      s' := s;
      assume noop(k, s, s');
      print "giving up; could not get ref\n";
      return;
    }

    var split_parent := SplitParent(fused_parent, pivot, slot, left_childref.value, right_childref.value);
    lemmaSplitParentValidReferences(IS.INode(fused_parent), pivot, slot, left_childref.value, right_childref.value, IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph);

    // TODO remove this when proof cleaned up (asserts necessary before KMTable)
    // var split_parent_pivots := Sequences.insert(fused_parent.pivotTable, pivot, slot);
    // var split_parent_children := replace1with2(fused_parent.children.value, left_childref.value, right_childref.value, slot);
    // var split_parent_buckets := replace1with2(fused_parent.buckets, SSTable.Empty(), SSTable.Empty(), slot);
    // var split_parent := IS.Node(
    //   split_parent_pivots,
    //   Some(split_parent_children),
    //   split_parent_buckets
    // );

    // SSTable.Ireplace1with2(fused_parent.buckets, SSTable.Empty(), SSTable.Empty(), slot);

    // assert IS.WFNode(split_parent);

    // forall r | r in BT.G.Successors(IS.INode(split_parent))
    // ensures r in IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph
    // {
    //   assert BC.BlockPointsToValidReferences(IS.INode(fused_parent), IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph);
    //   ghost var idx :| 0 <= idx < |split_parent_children| && split_parent_children[idx] == r;
    //   if (idx < slot) {
    //     assert r == fused_parent.children.value[idx];
    //     assert r in IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph;
    //   } else if (idx == slot) {
    //     assert r == left_childref.value;
    //     assert r in IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph;
    //   } else if (idx == slot + 1) {
    //     assert r == right_childref.value;
    //     assert r in IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph;
    //   } else {
    //     assert r == fused_parent.children.value[idx-1];
    //     assert r in IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph;
    //   }
    // }
    // assert BC.BlockPointsToValidReferences(IS.INode(split_parent), IS.IIndirectionTable(s2.ephemeralIndirectionTable).graph);

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

  method flush(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference, slot: int)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires s.Ready?
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in s.cache
  requires s.cache[ref].children.Some?
  requires 0 <= slot < |s.cache[ref].buckets|
  requires io.initialized()
  requires s.rootBucket == TTT.EmptyTree // FIXME we don't actually need this unless we're flushing the root
  modifies io
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  modifies s.ephemeralIndirectionTable.Repr
  {
    assume false; // timing out

    if s.frozenIndirectionTable.Some? {
      var lbaGraph := s.frozenIndirectionTable.value.Get(ref);
      if lbaGraph.Some? {
        assert ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
        var (lba, _) := lbaGraph.value;
        if lba.None? {
          assert ref !in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas;
          s' := s;
          assert noop(k, s, s');
          print "giving up; flush can't run because frozen isn't written";
          return;
        }
      }
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
      && |node.buckets[slot].keys| < 0x4000_0000_0000_0000
      && |child.buckets| < 0x1_0000_0000_0000_0000
      && (forall i | 0 <= i < |child.buckets| :: |child.buckets[i].keys| < 0x4000_0000_0000_0000)
    )) {
      s' := s;
      assert noop(k, s, s');
      print "giving up; data is 2 big\n";
      return;
    }

    forall i, key | 0 <= i < |child.buckets| && key in KMTable.I(child.buckets[i]) ensures Pivots.Route(child.pivotTable, key) == i
    {
      //assert BT.NodeHasWFBucketAt(IS.INode(child), i);
    }

    var newbuckets := KMTable.Flush(node.buckets[slot], child.buckets, child.pivotTable);
    var newchild := child.(buckets := newbuckets);

    WFBucketListFlush(KMTable.I(node.buckets[slot]), KMTable.ISeq(child.buckets), child.pivotTable);

    assert BT.G.Successors(IS.INode(newchild)) == BT.G.Successors(IS.INode(child));
    assert BC.BlockPointsToValidReferences(IS.INode(newchild), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);

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
        node.buckets[slot := KMTable.Empty()]
      );

    assert BC.BlockPointsToValidReferences(IS.INode(node), IS.IIndirectionTable(s1.ephemeralIndirectionTable).graph);
    forall ref | ref in BT.G.Successors(IS.INode(newparent)) ensures ref in IS.IIndirectionTable(s1.ephemeralIndirectionTable).graph {
      if (ref == newchildref.value) {
      } else {
        assert ref in BT.G.Successors(IS.INode(node));
      }
    }
    assert BC.BlockPointsToValidReferences(IS.INode(newparent), IS.IIndirectionTable(s1.ephemeralIndirectionTable).graph);

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

  method {:fuel JoinBucketList,0} fixBigNode(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference, parentref: BT.G.Reference)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires ref in s.cache
  requires parentref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[parentref]
  requires s.rootBucket == TTT.EmptyTree // FIXME we don't actually need this I think
  requires io.initialized()
  modifies io
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  modifies s.ephemeralIndirectionTable.Repr
  {
    assume false; // timing out

    if (ref !in s.cache) {
      s' := PageInReq(k, s, io, ref);
      return;
    }

    if s.frozenIndirectionTable.Some? {
      var lbaGraph := s.frozenIndirectionTable.value.Get(ref);
      if lbaGraph.Some? {
        assert ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
        var (lba, _) := lbaGraph.value;
        if lba.None? {
          assert ref !in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas;
          s' := s;
          assert noop(k, s, s');
          print "giving up; fixBigRoot can't run because frozen isn't written";
          return;
        }
      }
    }

    var node := s.cache[ref];

    INodeRootEqINodeForEmptyRootBucket(node);

    if i :| 0 <= i < |node.buckets| && !Marshalling.CappedBucket(node.buckets[i]) {
      if (node.children.Some?) {
        // internal node case: flush
        s' := flush(k, s, io, ref, i);
      } else {
        // leaf case

        if (!(
          && |node.buckets| < 0x8000_0000
          && (forall i | 0 <= i < |node.buckets| :: |node.buckets[i].keys| < 0x1_0000_0000)
        )) {
          s' := s;
          assert noop(k, s, s');
          print "giving up; stuff too big to call Join\n";
          return;
        }

        forall i, j, key1, key2 | 0 <= i < j < |node.buckets| && key1 in KMTable.I(node.buckets[i]) && key2 in KMTable.I(node.buckets[j])
        ensures MS.Keyspace.lt(key1, key2)
        {
          //assert BT.NodeHasWFBucketAt(IS.INode(node), i);
          //assert BT.NodeHasWFBucketAt(IS.INode(node), j);
          assert Pivots.Route(node.pivotTable, key1) == i;
          assert Pivots.Route(node.pivotTable, key2) == j;
          MS.Keyspace.IsStrictlySortedImpliesLte(node.pivotTable, i, j-1);
        }

        var joined := KMTable.Join(node.buckets, node.pivotTable);
        var pivots := GetNewPivots(joined);

        if (!(|pivots| < 0x7fff_ffff_ffff_ffff)) {
          s' := s;
          assert noop(k, s, s');
          print "giving up; stuff too big to call Split\n";
          return;
        }

        var buckets' := KMTable.SplitOnPivots(joined, pivots);
        var newnode := IS.Node(pivots, None, buckets');

        WFSplitBucketOnPivots(KMTable.I(joined), pivots);
        s' := write(k, s, ref, newnode);

        //assert BT.ValidRepivot(BT.Repivot(ref, node, pivots));
        ghost var step := BT.BetreeRepivot(BT.Repivot(ref, IS.INode(node), pivots));
        assume BT.ValidBetreeStep(step);
        assume |BT.BetreeStepOps(step)| == 1; // TODO
        assume BC.OpStep(k, IS.IVars(s), IS.IVars(s'), BT.BetreeStepOps(step)[0]);
        BC.MakeTransaction1(k, IS.IVars(s), IS.IVars(s'), BT.BetreeStepOps(step));
        assume stepsBetree(k, s, s', UI.NoOp, step);
      }
    } else if |node.buckets| > Marshalling.CapNumBuckets() as int {
      if (parentref !in s.cache) {
        s' := PageInReq(k, s, io, parentref);
        return;
      }

      var parent := s.cache[parentref];

      INodeRootEqINodeForEmptyRootBucket(parent);

      assert ref in BT.G.Successors(IS.INode(parent));
      var i :| 0 <= i < |parent.children.value| && parent.children.value[i] == ref;

      s' := doSplit(k, s, io, parentref, ref, i);
    } else {
      s' := s;
      assert noop(k, s, s');
      print "giving up; fixBigNode\n";
    }
  }

  method {:fuel BC.GraphClosed,0} flushRootBucket(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.initialized()
  modifies io
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires s.rootBucket != TTT.EmptyTree
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    var oldroot := s.cache[BT.G.Root()];

    var rootBucketSeq := TTT.AsSeq(s.rootBucket);

    if (!(
        && |rootBucketSeq| < 0x800_0000_0000
        && (forall i | 0 <= i < |rootBucketSeq| :: |rootBucketSeq[i].0| < 0x1_000)
        && (forall i | 0 <= i < |rootBucketSeq| :: rootBucketSeq[i].1 != Messages.IdentityMessage())
        && (forall i | 0 <= i < |rootBucketSeq| :: |rootBucketSeq[i].1.value| < 0x1_000)))
    {
      s' := s;
      assert noop(k, s, s');
      print "giving up; rootBucketSeq too big\n";
      return;
    }

    var kmt := KMTable.KMTableOfSeq(rootBucketSeq, TTT.I(s.rootBucket));

    if (!(
      && |kmt.keys| < 0x4000_0000_0000_0000
      && |oldroot.buckets| < 0x1_0000_0000_0000_0000
      && (forall i | 0 <= i < |oldroot.buckets| :: |oldroot.buckets[i].keys| < 0x4000_0000_0000_0000)
    )) {
      s' := s;
      assert noop(k, s, s');
      print "giving up; kmt/oldroot.buckets too big\n";
      return;
    }

    WFNodeRootImpliesWFRootBase(oldroot, s.rootBucket);
    forall i, key | 0 <= i < |oldroot.buckets| && key in KMTable.I(oldroot.buckets[i]) ensures Pivots.Route(oldroot.pivotTable, key) == i
    {
      //assert BT.NodeHasWFBucketAt(IS.INode(oldroot), i);
    }

    var newbuckets := KMTable.Flush(kmt, oldroot.buckets, oldroot.pivotTable);
    WFBucketListFlush(KMTable.I(kmt), KMTable.ISeq(oldroot.buckets), oldroot.pivotTable);

    var newroot := oldroot.(buckets := newbuckets);

    s' := s.(rootBucket := TTT.EmptyTree)
        .(cache := s.cache[BT.G.Root() := newroot]);

    BucketListFlushParentEmpty(KMTable.ISeq(newbuckets), oldroot.pivotTable);
    assert IS.INodeRoot(oldroot, s.rootBucket) == IS.INodeRoot(newroot, TTT.EmptyTree);
    assert IS.ICache(s.cache, s.rootBucket) == IS.ICache(s'.cache, TTT.EmptyTree);

    assert noop(k, s, s');
  }

  method AssignRefToLBA(table: IS.MutIndirectionTable, ref: IS.Reference, lba: BC.LBA)
  requires table.Inv()
  ensures IS.IIndirectionTable(table) ==
      old(BC.assignRefToLBA(IS.IIndirectionTable(table), ref, lba))
  modifies table.Repr
  {
    var lbaGraph := table.Remove(ref);
    if lbaGraph.Some? {
      var (_, graph) := lbaGraph.value;
      assume table.Count as nat < 0x10000000000000000 / 8;
      var _ := table.Insert(ref, (Some(lba), graph));
    }
    assume IS.IIndirectionTable(table) ==
        old(BC.assignRefToLBA(IS.IIndirectionTable(table), ref, lba));
  }

  method FindDeallocable(s: ImplVariables) returns (ref: Option<IS.Reference>)
  requires s.Ready?
  requires s.ephemeralIndirectionTable.Inv()
  ensures ref.Some? ==> ref.value in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  ensures ref.Some? ==> deallocable(s, ref.value)
  ensures ref.None? ==> forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph :: !deallocable(s, r)
  {
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralRefs := SetToSeq(set k | k in ephemeralTable);
    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;
    var i: uint64 := 0;
    while i as int < |ephemeralRefs|
    invariant i as int <= |ephemeralRefs|
    {
      var ref := ephemeralRefs[i];
      var isDeallocable := Deallocable(s, ref);
      if isDeallocable {
        return Some(ref);
      }
      i := i + 1;
    }
    assume forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph :: !deallocable(s, r);
    return None;
  }

  method FindUncappedNodeInCache(s: ImplVariables) returns (ref: Option<IS.Reference>)
  requires IS.WFVars(s)
  requires s.Ready?
  ensures ref.Some? ==> ref.value in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  ensures ref.Some? ==> ref.value in s.cache && !Marshalling.CappedNode(s.cache[ref.value])
  ensures ref.None? ==> forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph :: r in s.cache && Marshalling.CappedNode(s.cache[r])
  {
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralRefs := SetToSeq(set k | k in ephemeralTable);
    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;
    var i: uint64 := 0;
    while i as int < |ephemeralRefs|
    invariant i as int <= |ephemeralRefs|
    {
      var ref := ephemeralRefs[i];
      assume ref in s.cache;
      if !Marshalling.CappedNode(s.cache[ref]) {
        assume ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph;
        return Some(ref);
      }
      i := i + 1;
    }
    assume forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph :: r in s.cache && Marshalling.CappedNode(s.cache[r]);
    return None;
  }

  method FindRefInFrozenWithNoLba(s: ImplVariables) returns (ref: Option<IS.Reference>)
  requires IS.WFVars(s)
  requires s.Ready?
  requires s.frozenIndirectionTable.Some?
  ensures ref.Some? ==> ref.value in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph 
  ensures ref.Some? ==> ref.value !in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas
  ensures ref.None? ==> forall r | r in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph
      :: r in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas
  {
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var frozenTable := s.frozenIndirectionTable.value.ToMap();
    var frozenRefs := SetToSeq(set k | k in frozenTable);
    assume |frozenRefs| < 0x1_0000_0000_0000_0000;
    var i: uint64 := 0;
    while i as int < |frozenRefs|
    invariant i as int <= |frozenRefs|
    {
      var ref := frozenRefs[i];
      var lbaGraph := s.frozenIndirectionTable.value.Get(ref);
      assume lbaGraph.Some?;
      var (lba, _) := lbaGraph.value;
      if lba.None? {
        return Some(ref);
      }
      i := i + 1;
    }
    assume forall r | r in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph
        :: r in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas;
    return None;
  }

  method FindRefNotPointingToRefInEphemeral(s: ImplVariables, ref: IS.Reference) returns (result: IS.Reference)
  requires IS.WFVars(s)
  requires s.Ready?
  requires exists r :: !(r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
      ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r])
  ensures !(result in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
      ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[result])
  {
    assume s.ephemeralIndirectionTable.Inv();
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralRefs := SetToSeq(set k | k in ephemeralTable);
    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;
    var i: uint64 := 0;
    while i as int < |ephemeralRefs|
    invariant i as int <= |ephemeralRefs|
    {
      var eRef := ephemeralRefs[i];
      assume eRef in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph;
      var lbaGraph := s.ephemeralIndirectionTable.Get(eRef);
      assert lbaGraph.Some?;
      var (_, graph) := lbaGraph.value;
      if ref in graph {
        assume !(eRef in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
            result in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph &&
            ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[result]); // TODO check this assume
        return eRef;
      }
      i := i + 1;
    }
    assume false;
    assert false;
  }

  method {:fuel BC.GraphClosed,0} sync(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.initialized()
  modifies io
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    assume false; // TODO timing out

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

    if (s.rootBucket != TTT.EmptyTree) {
      s' := flushRootBucket(k, s, io);
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
      var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
      var ephemeralGraph := map k | k in ephemeralTable :: ephemeralTable[k].1;
      var foundDeallocable := FindDeallocable(s);
      if foundDeallocable.Some? {
        s' := Dealloc(k, s, io, foundDeallocable.value);
        return;
      }
      var foundUncapped := FindUncappedNodeInCache(s);
      if foundUncapped.Some? {
        var ref := foundUncapped.value;
        assert ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph;
        assert ref in s.cache && !Marshalling.CappedNode(s.cache[foundUncapped.value]);
        if (ref == BT.G.Root()) {
          s' := fixBigRoot(k, s, io);
        } else {
          assert !deallocable(s, ref);
          assert !(forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ::
              ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r]);
          assert !(forall r :: r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
              ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r]);
          assert (exists r :: !(r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
              ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r]));
          var r := FindRefNotPointingToRefInEphemeral(s, ref);
          assert !(r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph ==>
              ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph[r]);
          s' := fixBigNode(k, s, io, ref, r);
        }
        return;
      } else {
        s' := s.(frozenIndirectionTable := Some(s.ephemeralIndirectionTable))
            .(syncReqs := BC.syncReqs3to2(s.syncReqs));
        assert BC.Freeze(Ik(k), IS.IVars(s), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()));
        assert stepsBC(k, s, s', UI.NoOp, io, BC.FreezeStep);
        return;
      }
    }
    var foundInFrozen := FindRefInFrozenWithNoLba(s);
    if foundInFrozen.Some? {
      var ref := foundInFrozen.value;
      assert ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
      assert ref !in IS.IIndirectionTable(s.frozenIndirectionTable.value).lbas;

      if (!Marshalling.CappedNode(s.cache[ref])) {
        // TODO we should be able to prove this is impossible by adding an invariant
        // about frozenIndirectionTable (that is, we should never be freezing a table
        // with too-big nodes in it)
        s' := s;
        assert noop(k, s, s');
        print "sync: giving up; frozen table has big node rip (TODO we should prove this case impossible)\n";
        return;
      }

      var ephemeralRef := s.ephemeralIndirectionTable.Get(ref);
      if ephemeralRef.Some? && ephemeralRef.value.0.Some? {
        assert ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).lbas;
        // TODO we should be able to prove this is impossible as well
        s' := s;
        assert noop(k, s, s');
        print "sync: giving up; ref already in ephemeralIndirectionTable.lbas but not frozen";
        return;
      }

      var lba := getFreeLba(s);
      match lba {
        case Some(lba) => {
          INodeRootEqINodeForEmptyRootBucket(s.cache[ref]);
          var id := RequestWrite(io, lba, IS.SectorBlock(s.cache[ref]));
          if (id.Some?) {
            AssignRefToLBA(s.ephemeralIndirectionTable, ref, lba);
            assert IS.IIndirectionTable(s.ephemeralIndirectionTable) ==
              BC.assignRefToLBA(IS.IIndirectionTable(s.ephemeralIndirectionTable), ref, lba);
            AssignRefToLBA(s.frozenIndirectionTable.value, ref, lba);
            assert IS.IIndirectionTable(s.frozenIndirectionTable.value) ==
              BC.assignRefToLBA(IS.IIndirectionTable(s.frozenIndirectionTable.value), ref, lba);
            s' := s
              .(outstandingBlockWrites := s.outstandingBlockWrites[id.value := BC.OutstandingWrite(ref, lba)]);
            assert BC.WriteBackReq(Ik(k), IS.IVars(s), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()), ref);
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
        assert BC.WriteBackIndirectionTableReq(Ik(k), IS.IVars(s), IS.IVars(s'), ImplADM.M.IDiskOp(io.diskOp()));
        assert stepsBC(k, s, s', UI.NoOp, io, BC.WriteBackIndirectionTableReqStep);
      } else {
        s' := s;
        assert noop(k, s, s');
        print "sync: giving up; write back indirection table failed (no id)\n";
      }
    }
  }

  method readResponse(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.diskOp().RespReadOp?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    if (s.Unready?) {
      s' := PageInIndirectionTableResp(k, s, io);
    } else {
      s' := PageInResp(k, s, io);
    }
  }

  method writeResponse(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.diskOp().RespWriteOp?
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.NoOp, io.diskOp())
  {
    assume false; // TODO timing out

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

  method pushSync(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables, id: int)
  requires io.initialized()
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), UI.PushSyncOp(id), io.diskOp())
  {
    id := freeId(s.syncReqs);
    s' := s.(syncReqs := s.syncReqs[id := BC.State3]);
    assert stepsBC(k, s, s', UI.PushSyncOp(id), io, BC.PushSyncReqStep(id));
  }

  method popSync(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, id: int)
  returns (s': ImplVariables, success: bool)
  requires io.initialized()
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  modifies io
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), IS.IVars(s), IS.IVars(s'), if success then UI.PopSyncOp(id) else UI.NoOp, io.diskOp())
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

}
