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
    
  predicate LookupIsValid(k: Constants, s: Variables, lookup: Lookup)
  {
    && |lookup| > 0
    && lookup[0] == Root(k)
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
  
  function Read<T>(k: Constants, s: Variables, ref: Reference) : T
    requires LiveDataAvailable(k, s)
    requires ReachableReference(k, s, ref)
  {
    s.view[ref]
  }
    
  datatype CacheOp<T> =
    | AllocOp(block: T, successors: iset<Reference>, ref: Reference)
    | WriteOp(ref: Reference, block: T, successors: iset<Reference>)

  function ApplyToReferenceTree(reftree: ReferenceTree, op: CacheOp) : ReferenceTree {
    reftree[op.ref := op.successors]
  }
    
  function ApplyToView(view: View, op: CacheOp) : View {
    view[op.ref := op.block]
  }
    
  predicate Write<T>(k: Constants, s: Variables, s': Variables, ref: Reference, block: T, successors: iset<Reference>) {
    && successors <= LiveReferences(k, s)
    && ref in LiveReferences(k, s)

    && s'.reftree == s.reftree[ref := successors]
    && s'.view == s.view[ref := block]
  }
    
  predicate Alloc<T>(k: Constants, s: Variables, s': Variables, block: T, successors: iset<Reference>, ref: Reference) {
    && successors <= LiveReferences(k, s)
    && ref !in LiveReferences(k, s)

    && s'.reftree == s.reftree[ref := successors]
    && s'.view == s.view[ref := block]
  }
    
  predicate GC(k: Constants, s: Variables, s': Variables, ref: Reference) {
    && ref !in LiveReferences(k, s)
    && ref in s.view
    && s'.view == IMapRemove(s.view, ref)
    && s'.reftree == s.reftree
  }
  
  predicate Init<T>(k: Constants, s: Variables, block: T) {
    && s.view == imap[Root(k) := block]
    && s.reftree == imap[Root(k) := iset{}]
  }

  datatype Step<T> =
    | AllocStep(block: T, successors: iset<Reference>, ref: Reference)
    | WriteStep(ref: Reference, block: T, successors: iset<Reference>)
    | GCStep(ref: Reference)

  predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step) {
    match step {
      case AllocStep(block, successors, ref) => Alloc(k, s, s', block, successors, ref)
      case WriteStep(ref, block, successors) => Write(k, s, s', ref, block, successors)
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
  }
  
}
