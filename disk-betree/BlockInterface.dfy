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
  datatype Variables<T> = Variables(view: View, reftree: ReferenceTree)
    
  type Lookup = seq<Reference>

  predicate IsLookupStart(k: Constants, s: Variables, ref: Reference)
  {
    && ref in s.reftree
    && !exists ref2 :: ref2 in s.reftree && ref in s.reftree[ref2]
  }
    
  predicate LookupIsValid(k: Constants, s: Variables, lookup: Lookup)
  {
    && |lookup| > 0
    && IsLookupStart(k, s, lookup[0])
    && (forall i :: 0 <= i < |lookup| ==> lookup[i] in s.reftree)
    && (forall i :: 0 <= i < |lookup|-1 ==> lookup[i+1] in s.reftree[lookup[i]])
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

  predicate OneRoot(k: Constants, s: Variables) {
    && IsLookupStart(k, s, Root(k))
    && forall ref :: IsLookupStart(k, s, ref) ==> ref == Root(k)
  }
  
  function Read<T>(k: Constants, s: Variables, ref: Reference) : T
    requires LiveDataAvailable(k, s)
    requires ReachableReference(k, s, ref)
  {
    s.view[ref]
  }
    
  predicate Init<T>(k: Constants, s: Variables, block: T) {
    && s.view == imap[Root(k) := block]
    && s.reftree == imap[Root(k) := iset{}]
  }

  predicate Alloc<T>(k: Constants, s: Variables, s': Variables, block: T, successors: iset<Reference>, ref: Reference) {
    && successors <= LiveReferences(k, s)
    && ref !in LiveReferences(k, s)

    && s'.reftree == s.reftree[ref := successors]
    && s'.view == s.view[ref := block]
  }
    
  predicate Write<T>(k: Constants, s: Variables, s': Variables, ref: Reference, block: T, successors: iset<Reference>) {
    && successors <= LiveReferences(k, s)
    && ref in LiveReferences(k, s)

    && s'.reftree == s.reftree[ref := successors]
    && s'.view == s.view[ref := block]
  }

  predicate IsPath(k: Constants, s: Variables, s': Variables, steps: seq<Step>, path: seq<Variables>)
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
    && (exists path: seq<Variables> :: IsPath(k, s, s', steps, path))
   }
  
  predicate GC(k: Constants, s: Variables, s': Variables, ref: Reference) {
    && ref !in LiveReferences(k, s)
    && ref in s.view
    && s'.view == IMapRemove(s.view, ref)
    && s'.reftree == s.reftree
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

  lemma AllocPreservesInvariant<T>(k: Constants, s: Variables, s': Variables, block: T, successors: iset<Reference>, ref: Reference)
    requires Inv(k, s)
    requires Alloc(k, s, s', block, successors, ref)
    ensures Inv(k, s')
  {
    forall ref1 | ref1 in LiveReferences(k, s')
      ensures ref1 in LiveReferences(k, s) + iset{ref}
    { // OBSERVE?
    }
  }
  
  lemma WritePreservesInvariant<T>(k: Constants, s: Variables, s': Variables, ref: Reference, block: T, successors: iset<Reference>)
    requires Inv(k, s)
    requires Write(k, s, s', ref, block, successors)
    ensures Inv(k, s')
  {
    forall ref1 | ref1 in LiveReferences(k, s')
      ensures ref1 in LiveReferences(k, s) + iset{ref}
    { // OBSERVE?
    }
  }

  lemma TransactionPreservesInvariant(k: Constants, s: Variables, s': Variables, steps: seq<Step>)
    requires Inv(k, s)
    requires Transaction(k, s, s', steps)
    ensures Inv(k, s')
    decreases steps
  {
    var path :| IsPath(k, s, s', steps, path);
    var i := 0;
    while i < |steps|
      invariant 0 <= i <= |steps|
      invariant forall j :: 0 <= j <= i ==> Inv(k, path[j])
    {
      NextStepPreservesInvariant(k, path[i], path[i+1], steps[i]);
      i := i + 1;
    }
  }

  lemma GCPreservesInvariant(k: Constants, s: Variables, s': Variables, ref: Reference)
    requires Inv(k, s)
    requires GC(k, s, s', ref)
    ensures Inv(k, s')
  {
  }

  lemma NextStepPreservesInvariant(k: Constants, s: Variables, s': Variables, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', step)
    ensures Inv(k, s')
    decreases step
  {
    match step {
      case AllocStep(block, successors, ref) => AllocPreservesInvariant(k, s, s', block, successors, ref);
      case WriteStep(ref, block, successors) => WritePreservesInvariant(k, s, s', ref, block, successors);
      case TransactionStep(steps) => TransactionPreservesInvariant(k, s, s', steps);
      case GCStep(ref) => GCPreservesInvariant(k, s, s', ref);
    }
  }
}
