include "../treemodel/MapSpec.s.dfy"
include "../lib/Base/NativeTypes.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../treemodel/ByteBetreeBlockCacheSystem.i.dfy"
include "../treemodel/Marshalling.i.dfy"
include "../treemodel/MainDiskIOHandler.s.dfy"
include "../treemodel/ImplState.i.dfy"

include "../treemodel/PivotBetree_Refines_Map.i.dfy"
include "../treemodel/ByteBetreeBlockCacheSystem_Refines_BetreeBlockCacheSystem.i.dfy"
include "../treemodel/BetreeBlockCacheSystem_Refines_ThreeStateVersionedPivotBetree.i.dfy"

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
  import LBAType = LBAType
  import opened Sets
  import IS = ImplState
  import SD = AsyncSectorDisk
  import opened NativeTypes

  import opened Maps
  import opened Sequences
  import UI

  // TODO <deduplicate>
  type Message = Messages.Message

  type ImplConstants = ImplADM.M.Constants
  type ImplVariables = IS.Variables

  function Ik(k: ImplConstants) : ImplADM.M.Constants { k }
  // </deduplicate>

  predicate stepsBetree(k: ImplConstants, s: BBC.Variables, s': BBC.Variables, uiop: UI.Op, step: BT.BetreeStep)
  {
    ImplADM.M.NextStep(Ik(k), s, s', uiop, D.NoDiskOp, ImplADM.M.Step(BBC.BetreeMoveStep(step)))
  }

  predicate stepsBC(k: ImplConstants, s: BBC.Variables, s': BBC.Variables, uiop: UI.Op, io: DiskIOHandler, step: BC.Step)
  reads io
  {
    ImplADM.M.NextStep(Ik(k), s, s', uiop, io.diskOp(), ImplADM.M.Step(BBC.BlockCacheMoveStep(step)))
  }

  predicate noop(k: ImplConstants, s: BBC.Variables, s': BBC.Variables)
  {
    ImplADM.M.NextStep(Ik(k), s, s', UI.NoOp, D.NoDiskOp, ImplADM.M.Step(BBC.BlockCacheMoveStep(BC.NoOpStep)))
  }
}
