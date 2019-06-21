include "../lib/Maps.dfy"
include "../lib/sequences.dfy"
include "Graph.dfy"
  
abstract module BlockInterface {
  // BlockInterface is parameterized by the graph type
  import opened G : Graph 

  import opened Sequences
  import opened Maps
    
  type View = Graph

  datatype Constants = Constants()
  datatype Variables = Variables(view: View)

  predicate RefGraphIsClosed(k: Constants, s: Variables) {
    forall key :: key in s.view ==> Successors(s.view[key]) <= s.view.Keys
  }

  type Lookup = seq<Reference>

  predicate LookupIsValid(k: Constants, s: Variables, lookup: Lookup)
  {
    && |lookup| > 0
    && lookup[0] == Root()
    && (forall i :: 0 <= i < |lookup| ==> lookup[i] in s.view)
    && (forall i :: 0 <= i < |lookup|-1 ==> lookup[i+1] in Successors(s.view[lookup[i]]))
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
    
  predicate Init(k: Constants, s: Variables, block: Node) {
    && s.view == imap[Root() := block]
  }

  predicate Alloc(k: Constants, s: Variables, s': Variables, block: Node, ref: Reference) {
    && Successors(block) <= s.view.Keys
    && ref !in s.view

    && s'.view == s.view[ref := block]
  }
    
  predicate Write(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node) {
    && Successors(block) <= s.view.Keys
    && ref in s.view

    && s'.view == s.view[ref := block]
  }

  predicate OpStep(k: Constants, s: Variables, s': Variables, op: Op)
  {
    match op {
      case AllocOp(ref, block) => Alloc(k, s, s', block, ref)
      case WriteOp(ref, block) => Write(k, s, s', ref, block)
    }
  }

  predicate IsStatePath(k: Constants, s: Variables, s': Variables, ops: seq<Op>, path: seq<Variables>)
  {
    && |path| == |ops| + 1
    && path[0] == s
    && Last(path) == s'
    && (forall i :: 0 <= i < |ops| ==> OpStep(k, path[i], path[i+1], ops[i]))
  }

  lemma Transaction1Steps(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
  ensures (
    && 0 < |ops|
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
    && |ops| == 1
  ) ==>
      && OpStep(k, s, s', ops[0])
  {
    if (
        && 0 < |ops|
        && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
        && |ops| == 1)
    {
      var path :| IsStatePath(k, s, s', ops, path);
      assert OpStep(k, s, s', ops[0]);
    }
  }


  lemma Transaction2Steps(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
  ensures (
    && 0 < |ops|
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
    && |ops| == 2
  ) ==>
      exists sint ::
      && OpStep(k, s, sint, ops[0])
      && OpStep(k, sint, s', ops[1])
  {
    if (
        && 0 < |ops|
        && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
        &&| ops| == 2)
    {
      var path :| IsStatePath(k, s, s', ops, path);
      var sint := path[1];
      assert OpStep(k, s, sint, ops[0]);
      assert OpStep(k, sint, s', ops[1]);
    }
  }

  lemma Transaction3Steps(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
  ensures (
    && 0 < |ops|
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
    && |ops| == 3
  ) ==>
      exists sint, sint' ::
      && OpStep(k, s, sint, ops[0])
      && OpStep(k, sint, sint', ops[1])
      && OpStep(k, sint', s', ops[2])
  {
    if (
        && 0 < |ops|
        && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
        && |ops| == 3)
    {
      var path :| IsStatePath(k, s, s', ops, path);
      var sint := path[1];
      var sint' := path[2];
      assert OpStep(k, s, sint, ops[0]);
      assert OpStep(k, sint, sint', ops[1]);
      assert OpStep(k, sint', s', ops[2]);
    }
  }

  
  predicate Transaction(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
    ensures Transaction(k, s, s', ops) && |ops| == 1 ==>
      && OpStep(k, s, s', ops[0])
    ensures Transaction(k, s, s', ops) && |ops| == 2 ==> exists sint ::
      && OpStep(k, s, sint, ops[0])
      && OpStep(k, sint, s', ops[1])
    ensures Transaction(k, s, s', ops) && |ops| == 3 ==> exists sint, sint' ::
      && OpStep(k, s, sint, ops[0])
      && OpStep(k, sint, sint', ops[1])
      && OpStep(k, sint', s', ops[2])
  {
    Transaction1Steps(k, s, s', ops);
    Transaction2Steps(k, s, s', ops);
    Transaction3Steps(k, s, s', ops);
    && 0 < |ops|
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', ops, path))
  }

  function Predecessors(view: View, ref: Reference) : iset<Reference> {
    iset ref1 | ref1 in view && ref in Successors(view[ref1])
  }
  
  predicate ClosedUnderPredecessor(view: View, refs: iset<Reference>) {
    forall ref :: ref in refs ==> Predecessors(view, ref) <= refs
  }
   
  predicate GC(k: Constants, s: Variables, s': Variables, refs: iset<Reference>) {
    && refs !! LiveReferences(k, s)
    && refs <= s.view.Keys
    && ClosedUnderPredecessor(s.view, refs)
    
    && s'.view == IMapRemove(s.view, refs)
  }

  datatype Op =
    | AllocOp(ref: Reference, block: Node)
    | WriteOp(ref: Reference, block: Node)
  
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
    && Root() in s.view // Redundant? (yes, but can we delete it?)
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
    assert LookupIsValid(k, s, [Root()]);
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
}
