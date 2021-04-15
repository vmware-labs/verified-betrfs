module Functional {
  predicate ImpliesRequires<D(!new),R>(p: D -> bool, f: D --> R) {
    forall x | p(x) :: f.requires(x)
  }
}
