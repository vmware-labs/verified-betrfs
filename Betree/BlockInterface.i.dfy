include "../lib/Base/Maps.s.dfy"
include "../lib/Base/sequences.i.dfy"
include "../Betree/Graph.i.dfy"
include "../Betree/Transactable.i.dfy"
//
// A BlockInterface lets its client code (the Betree) perform atomic sequences
// of block allocation (assigning a new value),
// block write (replacing an existing value),
// and read steps.
// It also supports a GC step that frees some subset of unreferenced blocks.
//
  
abstract module BlockInterface refines Transactable {
  // A BlockInterface, being a Transactable, is parameterized by the graph
  // type Transactable.G.
  import opened Maps
    
  type View = G.Graph

  datatype Constants = Constants()
  datatype Variables = Variables(view: View)

  predicate RefGraphIsClosed(k: Constants, s: Variables) {
    forall key :: key in s.view ==> G.Successors(s.view[key]) <= s.view.Keys
  }

  type Lookup = seq<Reference>

  predicate LookupIsValid(k: Constants, s: Variables, lookup: Lookup)
  {
    && |lookup| > 0
    && lookup[0] == G.Root()
    && (forall i :: 0 <= i < |lookup| ==> lookup[i] in s.view)
    && (forall i :: 0 <= i < |lookup|-1 ==> lookup[i+1] in G.Successors(s.view[lookup[i]]))
  }

  predicate ReachableReference(k: Constants, s: Variables, ref: Reference)
  {
    exists lookup :: LookupIsValid(k, s, lookup) && Last(lookup) == ref
  }

  function LiveReferences(k: Constants, s: Variables) : iset<Reference> {
    iset ref | ReachableReference(k, s, ref)
  }

  predicate LiveDataAvailable(k: Constants, s: Variables) {
    LiveReferences(k, s) <= s.view.Keys
  }

  function Read(k: Constants, s: Variables, ref: Reference) : Node
    requires LiveDataAvailable(k, s)
    requires ref in s.view
  {
    s.view[ref]
  }
    
  predicate Init(k: Constants, s: Variables) {
    && s.view.Keys == iset{G.Root()}
    && G.Successors(s.view[G.Root()]) == iset{}
  }

  predicate Alloc(k: Constants, s: Variables, s': Variables, block: Node, ref: Reference) {
    && G.Successors(block) <= s.view.Keys
    && ref !in s.view

    && s'.view == s.view[ref := block]
  }
    
  predicate Write(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node) {
    && G.Successors(block) <= s.view.Keys
    && ref in s.view

    && s'.view == s.view[ref := block]
  }

  predicate ReadStep(k: Constants, s: Variables, op: ReadOp)
  {
    IMapsTo(s.view, op.ref, op.node)
  }

  predicate OpStep(k: Constants, s: Variables, s': Variables, op: Op)
  {
    match op {
      case AllocOp(ref, block) => Alloc(k, s, s', block, ref)
      case WriteOp(ref, block) => Write(k, s, s', ref, block)
    }
  }

  function Predecessors(view: View, ref: Reference) : iset<Reference> {
    iset ref1 | ref1 in view && ref in G.Successors(view[ref1])
  }
  
  predicate ClosedUnderPredecessor(view: View, refs: iset<Reference>) {
    forall ref :: ref in refs ==> Predecessors(view, ref) <= refs
  }

  predicate Transaction(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
  {
    OpTransaction(k, s, s', ops)
  }
   
  predicate CanGCRefs(k: Constants, s: Variables, refs: iset<Reference>)
  {
    && refs !! LiveReferences(k, s)
    && refs <= s.view.Keys
    && ClosedUnderPredecessor(s.view, refs)
  }

  predicate GC(k: Constants, s: Variables, s': Variables, refs: iset<Reference>) {
    && CanGCRefs(k, s, refs) 
    && s'.view == IMapRemove(s.view, refs)
  }

  datatype Step =
    //| AllocStep(block: Node, ref: Reference)
    //| WriteStep(ref: Reference, block: Node)
    | TransactionStep(ops: seq<Op>)
    | GCStep(refs: iset<Reference>)
    | StutterStep
    
  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step)
  {
    match step {
      //case AllocStep(block, ref) => Alloc(k, s, s', block, ref)
      //case WriteStep(ref, block) => Write(k, s, s', ref, block)
      case TransactionStep(ops) => Transaction(k, s, s', ops)
      case StutterStep => s == s'
      case GCStep(refs) => GC(k, s, s', refs)
    }
  }
    
  predicate Next(k: Constants, s: Variables, s': Variables) {
    exists step :: NextStep(k, s, s', step)
  }

  /////////// Some helper facts

  /*
  function AllocatedReferences(ops: seq<Op>) : iset<Reference>
  {
    //iset ref | (exists i :: 0 <= i < |steps| && steps[i].AllocStep? && steps[i].ref == ref)
    if |steps| == 0 then iset{}
    else
      (if steps[0].AllocStep? then iset{steps[0].ref} else iset{}) + AllocatedReferences(steps[1..])
  }
  */
  
  /*
  lemma PostTransactionView(k: Constants, s: Variables, s': Variables, steps: seq<Step>)
    requires NextStep(k, s, s', TransactionStep(steps))
    requires ValidTransaction(steps)
    ensures s'.view.Keys == s.view.Keys + AllocatedReferences(steps)
  {
    if |steps| == 0 {
    } else {
      var path: seq<Variables> :| IsStatePath(k, s, s', steps, path);
      if steps[0].WriteStep? {
        assert steps[0].ref in path[0].view;
        assert path[1].view.Keys == path[0].view.Keys;
      } else {
        assert steps[0].ref !in path[0].view;
        assert path[1].view.Keys == s.view.Keys + AllocatedReferences([steps[0]]);
      }
    }
  }
  */
    
  
  /////////// Invariants

  predicate Inv(k: Constants, s: Variables) {
    && G.Root() in s.view // Redundant? (yes, but can we delete it?)
    && RefGraphIsClosed(k, s)
    && LiveDataAvailable(k, s)
  }

  lemma AllocPreservesInv(k: Constants, s: Variables, s': Variables, block: Node, ref: Reference)
    requires Inv(k, s)
    requires Alloc(k, s, s', block, ref)
    ensures Inv(k, s')
  {
  }
  
  lemma WritePreservesInv(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires Write(k, s, s', ref, block)
    ensures Inv(k, s')
  {
  }

  lemma OpStepPreservesInv(k: Constants, s: Variables, s': Variables, op: Op)
    requires Inv(k, s)
    requires OpStep(k, s, s', op)
    ensures Inv(k, s')
  {
    match op {
      case AllocOp(ref, block) => AllocPreservesInv(k, s, s', block, ref);
      case WriteOp(ref, block) => WritePreservesInv(k, s, s', ref, block);
    }
  }

  lemma TransactionPreservesInv(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
    requires Inv(k, s)
    requires Transaction(k, s, s', ops)
    ensures Inv(k, s')
  {
    reveal_OpTransaction();
    var path :| IsStatePath(k, s, s', ops, path);
    var i := 0;
    while i < |ops|
      invariant 0 <= i <= |ops|
      invariant forall j :: 0 <= j <= i ==> Inv(k, path[j])
    {
      OpStepPreservesInv(k, path[i], path[i+1], ops[i]);
      i := i + 1;
    }
  }

  lemma GCPreservesInv(k: Constants, s: Variables, s': Variables, refs: iset<Reference>)
    requires Inv(k, s)
    requires GC(k, s, s', refs)
    ensures Inv(k, s')
  {
    assert LookupIsValid(k, s, [G.Root()]);
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', step)
    ensures Inv(k, s')
  {
    match step {
      //case AllocStep(block, ref) => AllocPreservesInv(k, s, s', block, ref);
      //case WriteStep(ref, block) => WritePreservesInv(k, s, s', ref, block);
      case TransactionStep(steps) => TransactionPreservesInv(k, s, s', steps);
      case GCStep(ref) => GCPreservesInv(k, s, s', ref);
      case StutterStep => { }
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables)
    requires Inv(k, s)
    requires Next(k, s, s')
    ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', step);
    NextStepPreservesInv(k, s, s', step);
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
  }
}
