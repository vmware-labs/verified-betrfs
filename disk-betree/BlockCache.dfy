abstract module BlockCache {
  import MissingLibrary
    
  type Reference(!new,==)

  type View<T> = imap<Reference, T>
  type ReferenceTree = imap<Reference, set<Reference>>

  function Root(k: Constants) : Reference

  type Constants
  datatype Variables<T> = Variables(view: View, reftree: ReferenceTree)
    
  type Lookup = seq<Reference>
    
  predicate LookupIsValid(k: Constants, s: Variables, lookup: Lookup)
  {
    && |lookup| > 0
    && lookup[0] == Root(k)
    && (forall i :: 0 <= i < |lookup|-1 ==> lookup[i+1] in s.reftree[lookup[i]])
  }

  predicate ReachableReference(k: Constants, s: Variables, ref: Reference)
  {
    exists lookup :: LookupIsValid(k, s, lookup) && Last(lookup) == ref
  }

  function LiveReferences(k: Constants, s: Variables) : set<Reference> {
    set ref | ReachableReference(k, s, ref)
  }

  
  function ViewOf<T>(k: Constants, s: Variables) : View
  
  // function Read<T>(k: Constants, s: Variables, ref: Reference) : T
  //   requires ref in ViewOf(k, s)
  //   ensures Read(k, s, ref) == ViewOf(k, s)[ref];
    
  datatype CacheOp<T> =
    | AllocOp(block: T, successors: iset<Reference>, ref: Reference)
    | WriteOp(ref: Reference, block: T, successors: iset<Reference>)
    
  function ApplyToView(view: View, op: CacheOp) : View {
    view[op.ref := op.block]
  }
    
  predicate Apply(k: Constants, s: Variables, s': Variables, op: CacheOp)
    ensures Apply(k, s, s', op) ==> ViewOf(k, s') == ApplyToView(ViewOf(k, s), op)
    ensures op.AllocOp? && Apply(k, s, s', op) ==> op.ref !in LiveReferences(k, s)
    ensures op.WriteOp? && Apply(k, s, s', op) ==> op.ref in LiveReferences(k, s)
    
  predicate Apply2(k: Constants, s: Variables, s': Variables, op1: CacheOp, op2: CacheOp)
    ensures Apply2(k, s, s', op1, op2) ==> ViewOf(k, s') == ApplyToView(ApplyToView(ViewOf(k, s), op1), op2)
  {
    exists sint ::
      && Apply(k, s, sint, op1)
      && Apply(k, sint, s', op2)
  }

  predicate GC(k: Constants, s: Variables, s': Variables, ref: Reference) {
    && ref !in LiveReferences(k, s)
    && ref in ViewOf(k, s)
    && s'.view == MapRemove(s, ref)
    && s'.reftree == s.reftree
  }
  
  predicate Init(k: Constants, s: Variables)
}
