include "../lib/Maps.dfy"
include "../lib/sequences.dfy"
  
abstract module BlockInterface {
  import opened Sequences
  import opened Maps
    
  type Reference(!new,==) // LBA

  type View<T> = imap<Reference, T>
  type ReferenceTree = imap<Reference, iset<Reference>>

  function Root(k: Constants) : Reference

  type Constants
  datatype Variables<T> = Variables(view: View, refGraph: ReferenceTree)
    
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
  
  predicate Transaction<T(!new)>(k: Constants, s: Variables, s': Variables, steps: seq<Step>)
    decreases steps, 1
  {
    && 0 < |steps|
    && (forall i :: 0 <= i < |steps| ==> steps[i].AllocStep? || steps[i].WriteStep?)
    && (exists path: seq<Variables> :: IsStatePath(k, s, s', steps, path))
   }
  
  predicate GC(k: Constants, s: Variables, s': Variables, ref: Reference) {
    && ref !in LiveReferences(k, s)
    && ref in s.view
    && s'.view == IMapRemove(s.view, ref)
    && s'.refGraph == s.refGraph
  }
  
  datatype Step<T> =
    | AllocStep(block: T, successors: iset<Reference>, ref: Reference)
    | WriteStep(ref: Reference, block: T, successors: iset<Reference>)
    | TransactionStep(steps: seq<Step>)
    | GCStep(ref: Reference)
    
  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step)
    decreases step
  {
    match step {
      case AllocStep(block, successors, ref) => Alloc(k, s, s', block, successors, ref)
      case WriteStep(ref, block, successors) => Write(k, s, s', ref, block, successors)
      case TransactionStep(steps) => Transaction(k, s, s', steps)
      case GCStep(ref) => GC(k, s, s', ref)
    }
  }
    
  predicate Next<T(!new)>(k: Constants, s: Variables, s': Variables) {
    exists step :: NextStep(k, s, s', step)
  }
    
  /////////// Invariants

  predicate Inv(k: Constants, s: Variables) {
    && LiveDataAvailable(k, s)
  }

  lemma AllocPreservesInv<T>(k: Constants, s: Variables, s': Variables, block: T, successors: iset<Reference>, ref: Reference)
    requires Inv(k, s)
    requires Alloc(k, s, s', block, successors, ref)
    ensures Inv(k, s')
  {
    forall ref1 | ref1 in LiveReferences(k, s')
      ensures ref1 in LiveReferences(k, s) + iset{ref}
    {
      var lookup :| LookupIsValid(k, s', lookup) && Last(lookup) == ref1;
      
    }
  }
  
  lemma WritePreservesInv<T>(k: Constants, s: Variables, s': Variables, ref: Reference, block: T, successors: iset<Reference>)
    requires Inv(k, s)
    requires Write(k, s, s', ref, block, successors)
    ensures Inv(k, s')
  {
    forall ref1 | ref1 in LiveReferences(k, s')
      ensures ref1 in LiveReferences(k, s) + iset{ref}
    { // OBSERVE?
    }
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

  lemma GCPreservesInv(k: Constants, s: Variables, s': Variables, ref: Reference)
    requires Inv(k, s)
    requires GC(k, s, s', ref)
    ensures Inv(k, s')
  {
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
