include "../lib/Maps.dfy"
include "../lib/sequences.dfy"
  
abstract module BlockInterface {
  import opened Sequences
  import opened Maps
    
  type Reference(!new,==) // LBA

  type View<T> = imap<Reference, T>
  type ReferenceGraph = imap<Reference, iset<Reference>>

  function Root(k: Constants) : Reference

  type Constants
  datatype Variables<T> = Variables(view: imap<Reference, T>, refGraph: ReferenceGraph)

  predicate RefGraphIsClosed(k: Constants, s: Variables) {
    forall key :: key in s.refGraph ==> s.refGraph[key] <= s.refGraph.Keys
  }

  predicate ViewAndRefGraphAreConsistent(k: Constants, s: Variables) {
    s.view.Keys == s.refGraph.Keys
  }
  
  type Lookup = seq<Reference>

  predicate LookupIsValid(k: Constants, s: Variables, lookup: Lookup)
  {
    && |lookup| > 0
    && lookup[0] == Root(k)
    && (forall i :: 0 <= i < |lookup| ==> lookup[i] in s.refGraph)
    && (forall i :: 0 <= i < |lookup|-1 ==> lookup[i+1] in s.refGraph[lookup[i]])
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

  function Read<T>(k: Constants, s: Variables, ref: Reference) : T
    requires LiveDataAvailable(k, s)
    requires ref in s.view
  {
    s.view[ref]
  }
    
  predicate Init<T>(k: Constants, s: Variables, block: T) {
    && s.view == imap[Root(k) := block]
    && s.refGraph == imap[Root(k) := iset{}]
  }

  predicate Alloc<T>(k: Constants, s: Variables, s': Variables, block: T, successors: iset<Reference>, ref: Reference) {
    && successors <= s.view.Keys
    && ref !in s.view

    && s'.refGraph == s.refGraph[ref := successors]
    && s'.view == s.view[ref := block]
  }
    
  predicate Write<T>(k: Constants, s: Variables, s': Variables, ref: Reference, block: T, successors: iset<Reference>) {
    && successors <= s.view.Keys
    && ref in s.view

    && s'.refGraph == s.refGraph[ref := successors]
    && s'.view == s.view[ref := block]
  }

  predicate IsStatePath(k: Constants, s: Variables, s': Variables, steps: seq<Step>, path: seq<Variables>)
    decreases steps, 0
  {
    && |path| == |steps| + 1
    && path[0] == s
    && Last(path) == s'
    && (forall i :: 0 <= i < |steps| ==> NextStep(k, path[i], path[i+1], steps[i]))
  }

  predicate ValidTransaction(steps: seq<Step>)
  {
    && (forall i :: 0 <= i < |steps| ==> steps[i].AllocStep? || steps[i].WriteStep?)
  }
  
  predicate Transaction<T(!new)>(k: Constants, s: Variables, s': Variables, steps: seq<Step>)
    decreases steps, 1
  {
    && 0 < |steps|
    && ValidTransaction(steps)
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', steps, path))
  }

  function Predecessors(refGraph: ReferenceGraph, ref: Reference) : iset<Reference> {
    iset ref1 | ref1 in refGraph && ref in refGraph[ref1]
  }
  
  predicate ClosedUnderPredecessor(refGraph: ReferenceGraph, refs: iset<Reference>) {
    forall ref :: ref in refs ==> Predecessors(refGraph, ref) <= refs
  }
   
  predicate GC(k: Constants, s: Variables, s': Variables, refs: iset<Reference>) {
    && refs !! LiveReferences(k, s)
    && refs <= s.view.Keys
    && ClosedUnderPredecessor(s.refGraph, refs)
    
    && s'.view == IMapRemove(s.view, refs)
    && s'.refGraph == IMapRemove(s.refGraph, refs)
  }
  
  datatype Step<T> =
    | AllocStep(block: T, successors: iset<Reference>, ref: Reference)
    | WriteStep(ref: Reference, block: T, successors: iset<Reference>)
    | TransactionStep(steps: seq<Step>)
    | GCStep(refs: iset<Reference>)
    
  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step)
    decreases step
  {
    match step {
      case AllocStep(block, successors, ref) => Alloc(k, s, s', block, successors, ref)
      case WriteStep(ref, block, successors) => Write(k, s, s', ref, block, successors)
      case TransactionStep(steps) => Transaction(k, s, s', steps)
      case GCStep(refs) => GC(k, s, s', refs)
    }
  }
    
  predicate Next<T(!new)>(k: Constants, s: Variables, s': Variables) {
    exists step :: NextStep(k, s, s', step)
  }

  /////////// Some helper facts

  function AllocatedReferences(steps: seq<Step>) : iset<Reference>
    requires ValidTransaction(steps)
  {
    //iset ref | (exists i :: 0 <= i < |steps| && steps[i].AllocStep? && steps[i].ref == ref)
    if |steps| == 0 then iset{}
    else
      (if steps[0].AllocStep? then iset{steps[0].ref} else iset{}) + AllocatedReferences(steps[1..])
  }
  
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
    
  
  /////////// Invariants

  predicate Inv(k: Constants, s: Variables) {
    && Root(k) in s.view // Redundant? (yes, but can we delete it?)
    && ViewAndRefGraphAreConsistent(k, s)
    && RefGraphIsClosed(k, s)
    && LiveDataAvailable(k, s)
  }

  lemma AllocPreservesInv<T>(k: Constants, s: Variables, s': Variables, block: T, successors: iset<Reference>, ref: Reference)
    requires Inv(k, s)
    requires Alloc(k, s, s', block, successors, ref)
    ensures Inv(k, s')
  {
  }
  
  lemma WritePreservesInv<T>(k: Constants, s: Variables, s': Variables, ref: Reference, block: T, successors: iset<Reference>)
    requires Inv(k, s)
    requires Write(k, s, s', ref, block, successors)
    ensures Inv(k, s')
  {
  }

  lemma TransactionPreservesInv(k: Constants, s: Variables, s': Variables, steps: seq<Step>)
    requires Inv(k, s)
    requires Transaction(k, s, s', steps)
    ensures Inv(k, s')
    decreases steps
  {
    var path :| IsStatePath(k, s, s', steps, path);
    var i := 0;
    while i < |steps|
      invariant 0 <= i <= |steps|
      invariant forall j :: 0 <= j <= i ==> Inv(k, path[j])
    {
      NextStepPreservesInv(k, path[i], path[i+1], steps[i]);
      i := i + 1;
    }
  }

  lemma GCPreservesInv(k: Constants, s: Variables, s': Variables, refs: iset<Reference>)
    requires Inv(k, s)
    requires GC(k, s, s', refs)
    ensures Inv(k, s')
  {
    assert LookupIsValid(k, s, [Root(k)]);
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', step)
    ensures Inv(k, s')
    decreases step
  {
    match step {
      case AllocStep(block, successors, ref) => AllocPreservesInv(k, s, s', block, successors, ref);
      case WriteStep(ref, block, successors) => WritePreservesInv(k, s, s', ref, block, successors);
      case TransactionStep(steps) => TransactionPreservesInv(k, s, s', steps);
      case GCStep(ref) => GCPreservesInv(k, s, s', ref);
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
