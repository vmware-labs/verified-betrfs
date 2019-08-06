include "MapSpec.s.dfy"
include "../lib/NativeTypes.s.dfy"
include "../lib/Sets.i.dfy"
include "../lib/Option.s.dfy"
include "ByteBetreeBlockCacheSystem.i.dfy"
include "Marshalling.i.dfy"
include "MainDiskIOHandler.s.dfy"

// See dependency graph in MainImpl.dfy

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
  {
    assume false;
  }
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



}
