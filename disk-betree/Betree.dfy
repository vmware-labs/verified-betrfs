include "inc/disk-betree/BlockInterface.dfy"  
include "inc/lib/sequences.dfy"
include "inc/lib/Maps.dfy"
include "inc/disk-betree/MapSpec.dfy"
include "inc/disk-betree/Graph.dfy"
include "inc/disk-betree/BetreeSpec.dfy"

module Betree {
  import opened BetreeSpec`Internal
  import BI = BetreeBlockInterface
  import MS = MapSpec
  import opened Maps
  import opened Sequences

  import opened G = BetreeGraph
  type UIOp = MS.UI.Op<Value>

  datatype Constants = Constants(bck: BI.Constants)
  datatype Variables = Variables(bcv: BI.Variables)

  predicate ValidLayerIndex(lookup: Lookup, idx: int) {
    && 0 <= idx < |lookup|
  }

  predicate LookupFollowsChildRefAtLayer(key: Key, lookup: Lookup, idx: int)
  requires ValidLayerIndex(lookup, idx) && idx < |lookup| - 1;
  requires key in lookup[idx].node.children;
  {
    lookup[idx].node.children[key] == lookup[idx+1].ref
  }

  predicate LookupFollowsChildRefs(key: Key, lookup: Lookup) {
    && (forall idx :: ValidLayerIndex(lookup, idx) && idx < |lookup| - 1 ==> key in lookup[idx].node.children)
    && (forall idx :: ValidLayerIndex(lookup, idx) && idx < |lookup| - 1 ==> LookupFollowsChildRefAtLayer(key, lookup, idx))
  }
  
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
    && BI.Init(k.bck, s.bcv, EmptyNode())
  }

  predicate GC(k: Constants, s: Variables, s': Variables, uiop: UIOp, refs: iset<Reference>) {
    && uiop.NoOp?
    && BI.GC(k.bck, s.bcv, s'.bcv, refs)
  }

  predicate Betree(k: Constants, s: Variables, s': Variables, uiop: UIOp, betreeStep: BetreeStep)
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
