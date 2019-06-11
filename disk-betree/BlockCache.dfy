abstract module BlockCache {
  type Constants
  type Variables(!new)<T>

  type Reference(!new,==)

  type View<T> = imap<Reference, T>
    
  function ViewOf<T>(k: Constants, s: Variables) : View
    
  function Read<T>(k: Constants, s: Variables, ref: Reference) : T
    requires ref in ViewOf(k, s)
    ensures Read(k, s, ref) == ViewOf(k, s)[ref];
    
  datatype CacheOp<T> =
    | AllocOp(block: T, successors: iset<Reference>, new_ref: Reference)
    | WriteOp(ref: Reference, block: T, successors: iset<Reference>)
    
  function ApplyToView(view: View, op: CacheOp) : View {
    match op {
      case AllocOp(block, successors, new_ref) => view[op.new_ref := op.block]
      case WriteOp(ref, block, successors) => view[op.ref := op.block]
    }
  }
    
  predicate Apply(k: Constants, s: Variables, s': Variables, op: CacheOp)
    requires op.AllocOp? ==> op.new_ref !in ViewOf(k, s)
    ensures Apply(k, s, s', op) ==> ViewOf(k, s') == ApplyToView(ViewOf(k, s), op)
    
  predicate Apply2(k: Constants, s: Variables, s': Variables, op1: CacheOp, op2: CacheOp)
    requires op1.AllocOp? ==> op1.new_ref !in ViewOf(k, s)
    requires op2.AllocOp? ==> op2.new_ref !in ApplyToView(ViewOf(k, s), op1)
    ensures Apply2(k, s, s', op1, op2) ==> ViewOf(k, s') == ApplyToView(ApplyToView(ViewOf(k, s), op1), op2)
  {
    exists sint :: 
      && Apply(k, s, sint, op1)
      && assert ViewOf(k, sint) == ApplyToView(ViewOf(k, s), op1);
      && Apply(k, sint, s', op2)
      && assert ViewOf(k, s') == ApplyToView(ViewOf(k, sint), op2);
      && true
  }
    
  function Root(k: Constants) : Reference

  predicate Init(k: Constants, s: Variables)
}
