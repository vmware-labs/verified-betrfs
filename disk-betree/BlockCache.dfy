abstract module BlockCache {
  type Reference;

  type Constants;
  type Variables<T>;

  predicate Read<T>(k: Constants, s: Variables, ref: Reference, block: T)
  predicate Alloc<T>(k: Constants, s: Variables, s': Variables, block: T, successors: set<Reference>, new_ref: Reference)
  predicate Write<T>(k: Constants, s: Variables, s': Variables, ref: Reference, block: T, successors: set<Reference>)

  function Root<T>(k: Constants) : Reference
}
