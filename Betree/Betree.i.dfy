include "../Betree/BlockInterface.i.dfy"  
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Maps.s.dfy"
include "../MapSpec/MapSpec.s.dfy"
include "../Betree/Graph.i.dfy"
include "../Betree/BetreeSpec.i.dfy"
//
// Betree lowers the "lifted" op-sequences of BetreeSpec down to concrete state machine
// steps that advance the BetreeBlockInterface as required by BetreeSpec.
// It also interleaves Betree operations with BlockInterface garbage collection.
// 
// TODO(jonh): This probably should get renamed; its place in the heirarchy
// is confusing.
//

module Betree {
  import opened BetreeSpec`Internal
  import BI = BetreeBlockInterface
  import MS = MapSpec
  import opened Maps
  import opened Sequences
  import opened KeyType
  import opened ValueType
  import UI

  import opened G = BetreeGraph

  datatype Constants = Constants(bck: BI.Constants)
  datatype Variables = Variables(bcv: BI.Variables)
  
  // TODO(jonh): [cleanup] Not sure why these 3 are in this file.
  predicate LookupRespectsDisk(view: BI.View, lookup: Lookup) {
    forall i :: 0 <= i < |lookup| ==> IMapsTo(view, lookup[i].ref, lookup[i].node)
  }

  predicate IsPathFromRootLookup(k: Constants, view: BI.View, key: Key, lookup: Lookup) {
    && |lookup| > 0
    && lookup[0].ref == Root()
    && LookupRespectsDisk(view, lookup)
    && LookupFollowsChildRefs(key, lookup)
  }

  predicate IsSatisfyingLookup(k: Constants, view: BI.View, key: Key, value: Value, lookup: Lookup) {
    && IsPathFromRootLookup(k, view, key, lookup)
    && LookupVisitsWFNodes(lookup)
    && BufferDefinesValue(InterpretLookup(lookup, key), value)
  }

  function EmptyNode() : Node {
    var buffer := imap key | MS.InDomain(key) :: G.M.Define(G.M.DefaultValue());
    Node(imap[], buffer)
  }

  predicate Init(k: Constants, s: Variables) {
    && BI.Init(k.bck, s.bcv)
    && s.bcv.view[Root()] == EmptyNode()
  }

  predicate GC(k: Constants, s: Variables, s': Variables, uiop: UI.Op, refs: iset<Reference>) {
    && uiop.NoOp?
    && BI.GC(k.bck, s.bcv, s'.bcv, refs)
  }

  predicate Betree(k: Constants, s: Variables, s': Variables, uiop: UI.Op, betreeStep: BetreeStep)
  {
    && ValidBetreeStep(betreeStep)
    && BetreeStepUI(betreeStep, uiop)
    && BI.Reads(k.bck, s.bcv, BetreeStepReads(betreeStep))
    && BI.OpTransaction(k.bck, s.bcv, s'.bcv, BetreeStepOps(betreeStep))
  }
  
  datatype Step =
    | BetreeStep(step: BetreeStep)
    | GCStep(refs: iset<Reference>)
    | StutterStep

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: UI.Op, step: Step) {
    match step {
      case BetreeStep(betreeStep) => Betree(k, s, s', uiop, betreeStep)
      case GCStep(refs) => GC(k, s, s', uiop, refs)
      case StutterStep => s == s' && uiop.NoOp?
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UI.Op) {
    exists step: Step :: NextStep(k, s, s', uiop, step)
  }
}
