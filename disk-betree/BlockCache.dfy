abstract module BlockCache {
  type Constants
  type Variables(!new)<T>

  type Reference(!new,==)

  function View<T>(k: Constants, s: Variables) : imap<Reference, T>
    ensures forall ref :: ref in View(k, s)
    
  function Read<T>(k: Constants, s: Variables, ref: Reference) : T
    ensures Read(k, s, ref) == View(k, s)[ref];
    
  datatype CacheOp<T> =
    | AllocOp(block: T, successors: iset<Reference>, new_ref: Reference)
    | WriteOp(ref: Reference, block: T, successors: iset<Reference>)
    
  predicate Apply(k: Constants, s: Variables, s': Variables, op: CacheOp)
    
  predicate Apply2(k: Constants, s: Variables, s': Variables, op1: CacheOp, op2: CacheOp) {
    exists sint :: 
      && Apply(k, s, sint, op1)
      && Apply(k, sint, s', op2)
  }
    
  function Root(k: Constants) : Reference

  predicate Init(k: Constants, s: Variables)
}
