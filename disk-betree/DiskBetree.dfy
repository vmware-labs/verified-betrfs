include "BlockInterface.dfy"  
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "MapSpec.dfy"
include "Graph.dfy"
include "BetreeSpec.dfy"

module DiskBetree {
  import opened BetreeSpec
  import BI = BetreeBlockInterface
  import MS = MapSpec
  import opened Maps

  import opened G = BetreeGraph

  datatype Constants = Constants(bck: BI.Constants)
  datatype Variables = Variables(bcv: BI.Variables)

  datatype Layer = Layer(ref: Reference, node: Node)
  type Lookup = seq<Layer>

  predicate LookupFollowsChildRefs(key: Key, lookup: Lookup) {
    && (forall i :: 0 <= i < |lookup| - 1 ==> key in lookup[i].node.children)
    && (forall i :: 0 <= i < |lookup| - 1 ==> lookup[i].node.children[key] == lookup[i+1].ref)
  }
  
  predicate LookupRespectsDisk(view: BI.View, lookup: Lookup) {
    forall i :: 0 <= i < |lookup| ==> IMapsTo(view, lookup[i].ref, lookup[i].node)
  }

  predicate LookupVisitsWFNodes(lookup: Lookup) {
    forall i :: 0 <= i < |lookup| ==> WFNode(lookup[i].node)
  }

  predicate IsPathFromRootLookup(k: Constants, view: BI.View, key: Key, lookup: Lookup) {
    && |lookup| > 0
    && lookup[0].ref == Root()
    && LookupRespectsDisk(view, lookup)
    && LookupFollowsChildRefs(key, lookup)
  }

  function TotalLog(lookup: Lookup, key: Key) : seq<BufferEntry>
  requires LookupVisitsWFNodes(lookup);
  {
    if |lookup| == 0 then [] else TotalLog(lookup[..|lookup|-1], key) + lookup[|lookup|-1].node.buffer[key]
  }

  predicate IsSatisfyingLookup(k: Constants, view: BI.View, key: Key, value: Value, lookup: Lookup) {
    && IsPathFromRootLookup(k, view, key, lookup)
    && LookupVisitsWFNodes(lookup)
    && BufferDefinesValue(TotalLog(lookup, key), value)
  }

  predicate Query(k: Constants, s: Variables, s': Variables, key: Key, value: Value, lookup: Lookup) {
    && s == s'
    && IsSatisfyingLookup(k, s.bcv.view, key, value, lookup)
  }

  predicate Init(k: Constants, s: Variables) {
    && BI.Init(k.bck, s.bcv, EmptyNode())
  }

  predicate GC(k: Constants, s: Variables, s': Variables, refs: iset<Reference>) {
    BI.GC(k.bck, s.bcv, s'.bcv, refs)
  }

  predicate Betree(k: Constants, s: Variables, s': Variables, betreeStep: BetreeStep)
  {
    && ValidBetreeStep(betreeStep)
    && BI.Reads(k.bck, s.bcv, BetreeStepReads(betreeStep))
    && BI.OpTransaction(k.bck, s.bcv, s'.bcv, BetreeStepOps(betreeStep))
  }
  
  datatype Step =
    | QueryStep(key: Key, value: Value, lookup: Lookup)
    | BetreeStep(step: BetreeStep)
    | GCStep(refs: iset<Reference>)

  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step) {
    match step {
      case QueryStep(key, value, lookup) => Query(k, s, s', key, value, lookup)
      case BetreeStep(betreeStep) => Betree(k, s, s', betreeStep)
      case GCStep(refs) => GC(k, s, s', refs)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables) {
    exists step: Step :: NextStep(k, s, s', step)
  }
}
