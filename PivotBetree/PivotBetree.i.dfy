include "../Betree/BlockInterface.i.dfy"  
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Maps.s.dfy"
include "../MapSpec/MapSpec.s.dfy"
include "../Betree/Graph.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Message.i.dfy"
include "../Betree/BetreeSpec.i.dfy"
include "../Betree/Betree.i.dfy"
include "../Betree/BetreeInv.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "../MapSpec/UIStateMachine.s.dfy"
//
// Like Betree, PivetBetree lowers the "lifted" op-sequences of PivotBetreeSpec
// down to concrete state machine steps that advance the PivotBetreeBlockInterface
// as required by BetreeSpec. The only difference is that the interface has a more
// concrete (pivot-y) type.
//

module PivotBetree refines UIStateMachine {
  import opened PivotBetreeSpec`Internal

  import BI = PivotBetreeBlockInterface
  import MS = MapSpec
  import opened Maps
  import opened Options

  import opened G = PivotBetreeGraph

  datatype Constants = Constants(bck: BI.Constants)
  datatype Variables = Variables(bcv: BI.Variables)

  function EmptyNode() : Node
  {
    Node([], None, [map[]])
  }

  predicate Init(k: Constants, s: Variables) {
    && BI.Init(k.bck, s.bcv)
    && s.bcv.view[G.Root()] == EmptyNode()
  }

  predicate GC(k: Constants, s: Variables, s': Variables, uiop: UIOp, refs: iset<Reference>) {
    && uiop.NoOp? 
    && BI.GC(k.bck, s.bcv, s'.bcv, refs)
  }

  predicate Betree(k: Constants, s: Variables, s': Variables, uiop: UIOp, betreeStep: BetreeStep)
  {
    && ValidBetreeStep(betreeStep)
    && BI.Reads(k.bck, s.bcv, BetreeStepReads(betreeStep))
    && BI.OpTransaction(k.bck, s.bcv, s'.bcv, BetreeStepOps(betreeStep))
    && BetreeStepUI(betreeStep, uiop)
  }
 
  datatype Step =
    | BetreeStep(step: BetreeStep)
    | GCStep(refs: iset<Reference>)
    | StutterStep

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: Step) {
    match step {
      case BetreeStep(betreeStep) => Betree(k, s, s', uiop, betreeStep)
      case GCStep(refs) => GC(k, s, s', uiop, refs)
      case StutterStep => s == s' && uiop.NoOp?
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp) {
    exists step: Step :: NextStep(k, s, s', uiop, step)
  }
}
