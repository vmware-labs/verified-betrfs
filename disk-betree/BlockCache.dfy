abstract module BlockCache {
  type Constants
  type Variables(!new)<T>

  type Reference(!new,==)

  type View<T> = imap<Reference, T>
    
  function ViewOf<T>(k: Constants, s: Variables) : View
  ensures Root(k) in ViewOf(k, s)
  
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
    ensures op.AllocOp? && Apply(k, s, s', op) ==> op.ref !in ViewOf(k, s)
    ensures op.WriteOp? && Apply(k, s, s', op) ==> op.ref in ViewOf(k, s)
    
  predicate Apply2(k: Constants, s: Variables, s': Variables, op1: CacheOp, op2: CacheOp)
    ensures Apply2(k, s, s', op1, op2) ==> ViewOf(k, s') == ApplyToView(ApplyToView(ViewOf(k, s), op1), op2)
  {
    exists sint ::
      && Apply(k, s, sint, op1)
      && Apply(k, sint, s', op2)
  }
    
  function Root(k: Constants) : Reference

  predicate Init(k: Constants, s: Variables)
}
