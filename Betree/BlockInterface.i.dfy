include "../lib/Base/Maps.i.dfy"
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

  datatype Variables = Variables(view: View)

  predicate RefGraphIsClosed(s: Variables) {
    forall key :: key in s.view ==> G.Successors(s.view[key]) <= s.view.Keys
  }

  type Lookup = seq<Reference>

  predicate LookupIsValid(s: Variables, lookup: Lookup)
  {
    && |lookup| > 0
    && lookup[0] == G.Root()
    && (forall i :: 0 <= i < |lookup| ==> lookup[i] in s.view)
    && (forall i :: 0 <= i < |lookup|-1 ==> lookup[i+1] in G.Successors(s.view[lookup[i]]))
  }

  predicate ReachableReference(s: Variables, ref: Reference)
  {
    exists lookup :: LookupIsValid(s, lookup) && Last(lookup) == ref
  }

  function LiveReferences(s: Variables) : iset<Reference> {
    iset ref | ReachableReference(s, ref)
  }

  predicate LiveDataAvailable(s: Variables) {
    LiveReferences(s) <= s.view.Keys
  }

  function Read(s: Variables, ref: Reference) : Node
    requires LiveDataAvailable(s)
    requires ref in s.view
  {
    s.view[ref]
  }
    
  predicate Init(s: Variables) {
    && s.view.Keys == iset{G.Root()}
    && G.Successors(s.view[G.Root()]) == iset{}
  }

  predicate Alloc(s: Variables, s': Variables, block: Node, ref: Reference) {
    && G.Successors(block) <= s.view.Keys
    && ref !in s.view

    && s'.view == s.view[ref := block]
  }
    
  predicate Write(s: Variables, s': Variables, ref: Reference, block: Node) {
    && G.Successors(block) <= s.view.Keys
    && ref in s.view

    && s'.view == s.view[ref := block]
  }

  predicate ReadStep(s: Variables, op: ReadOp)
  {
    IMapsTo(s.view, op.ref, op.node)
  }

  predicate OpStep(s: Variables, s': Variables, op: Op)
  {
    match op {
      case AllocOp(ref, block) => Alloc(s, s', block, ref)
      case WriteOp(ref, block) => Write(s, s', ref, block)
    }
  }

  function Predecessors(view: View, ref: Reference) : iset<Reference> {
    iset ref1 | ref1 in view && ref in G.Successors(view[ref1])
  }
  
  predicate ClosedUnderPredecessor(view: View, refs: iset<Reference>) {
    forall ref :: ref in refs ==> Predecessors(view, ref) <= refs
  }

  predicate Transaction(s: Variables, s': Variables, ops: seq<Op>)
  {
    OpTransaction(s, s', ops)
  }
   
  predicate CanGCRefs(s: Variables, refs: iset<Reference>)
  {
    && refs !! LiveReferences(s)
    && refs <= s.view.Keys
    && ClosedUnderPredecessor(s.view, refs)
  }

  predicate GC(s: Variables, s': Variables, refs: iset<Reference>) {
    && CanGCRefs(s, refs) 
    && s'.view == IMapRemove(s.view, refs)
  }

  datatype Step =
    //| AllocStep(block: Node, ref: Reference)
    //| WriteStep(ref: Reference, block: Node)
    | TransactionStep(ops: seq<Op>)
    | GCStep(refs: iset<Reference>)
    | StutterStep
    
  predicate NextStep(s: Variables, s': Variables, step: Step)
  {
    match step {
      //case AllocStep(block, ref) => Alloc(s, s', block, ref)
      //case WriteStep(ref, block) => Write(s, s', ref, block)
      case TransactionStep(ops) => Transaction(s, s', ops)
      case StutterStep => s == s'
      case GCStep(refs) => GC(s, s', refs)
    }
  }
    
  predicate Next(s: Variables, s': Variables) {
    exists step :: NextStep(s, s', step)
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
  lemma PostTransactionView(s: Variables, s': Variables, steps: seq<Step>)
    requires NextStep(s, s', TransactionStep(steps))
    requires ValidTransaction(steps)
    ensures s'.view.Keys == s.view.Keys + AllocatedReferences(steps)
  {
    if |steps| == 0 {
    } else {
      var path: seq<Variables> :| IsStatePath(s, s', steps, path);
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

  predicate Inv(s: Variables) {
    && G.Root() in s.view // Redundant? (yes, but can we delete it?)
    && RefGraphIsClosed(s)
    && LiveDataAvailable(s)
  }

  lemma AllocPreservesInv(s: Variables, s': Variables, block: Node, ref: Reference)
    requires Inv(s)
    requires Alloc(s, s', block, ref)
    ensures Inv(s')
  {
  }
  
  lemma WritePreservesInv(s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(s)
    requires Write(s, s', ref, block)
    ensures Inv(s')
  {
  }

  lemma OpStepPreservesInv(s: Variables, s': Variables, op: Op)
    requires Inv(s)
    requires OpStep(s, s', op)
    ensures Inv(s')
  {
    match op {
      case AllocOp(ref, block) => AllocPreservesInv(s, s', block, ref);
      case WriteOp(ref, block) => WritePreservesInv(s, s', ref, block);
    }
  }

  lemma TransactionPreservesInv(s: Variables, s': Variables, ops: seq<Op>)
    requires Inv(s)
    requires Transaction(s, s', ops)
    ensures Inv(s')
  {
    reveal_OpTransaction();
    var path :| IsStatePath(s, s', ops, path);
    var i := 0;
    while i < |ops|
      invariant 0 <= i <= |ops|
      invariant forall j :: 0 <= j <= i ==> Inv(path[j])
    {
      OpStepPreservesInv(path[i], path[i+1], ops[i]);
      i := i + 1;
    }
  }

  lemma GCPreservesInv(s: Variables, s': Variables, refs: iset<Reference>)
    requires Inv(s)
    requires GC(s, s', refs)
    ensures Inv(s')
  {
    assert LookupIsValid(s, [G.Root()]);
  }

  lemma NextStepPreservesInv(s: Variables, s': Variables, step: Step)
    requires Inv(s)
    requires NextStep(s, s', step)
    ensures Inv(s')
  {
    match step {
      //case AllocStep(block, ref) => AllocPreservesInv(s, s', block, ref);
      //case WriteStep(ref, block) => WritePreservesInv(s, s', ref, block);
      case TransactionStep(steps) => TransactionPreservesInv(s, s', steps);
      case GCStep(ref) => GCPreservesInv(s, s', ref);
      case StutterStep => { }
    }
  }

  lemma NextPreservesInv(s: Variables, s': Variables)
    requires Inv(s)
    requires Next(s, s')
    ensures Inv(s')
  {
    var step :| NextStep(s, s', step);
    NextStepPreservesInv(s, s', step);
  }

  lemma InitImpliesInv(s: Variables)
    requires Init(s)
    ensures Inv(s)
  {
  }
}
