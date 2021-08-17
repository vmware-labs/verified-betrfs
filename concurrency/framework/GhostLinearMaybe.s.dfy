
module GhostLinearMaybe {
  // note: cannot test gmaybe<A> for equality at run-time (because has is ghost)
  type {:extern "predefined"} gmaybe(!new)<A>

  predicate {:axiom} has<A>(m: gmaybe<A>)

  // return value in m if has(m), return default ghost A value otherwise
  function {:axiom} read<A>(m: gmaybe<A>): A

  function method peek<A>(gshared m: gmaybe<A>): (gshared a: A)
    requires has(m)
    ensures a == read(m)

  function method unwrap<A>(glinear m: gmaybe<A>): (glinear a: A)
    requires has(m)
    ensures a == read(m)

  function method give<A>(glinear a: A):(glinear m: gmaybe<A>)
    ensures has(m)
    ensures read(m) == a
    ensures forall x:gmaybe<A> {:trigger give(read(x))} | has(x) && a == read(x) :: m == x

  function method empty<A>():(glinear m: gmaybe<A>)
    ensures !has(m)

  function method discard<A>(glinear m:gmaybe<A>):()
    requires !has(m)

  // function {:axiom} imagine<A>(h:bool, a:A):(m:gmaybe<A>)
  //   ensures has(m) == h
  //   ensures read(m) == a

  // lemma {:axiom} axiom_extensional<A>(m1:gmaybe<A>, m2:gmaybe<A>)
  //   requires has(m1) == has(m2)
  //   requires read(m1) == read(m2)
  //   ensures m1 == m2

} // module
