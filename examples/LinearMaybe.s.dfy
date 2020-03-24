
// module LinearMaybe {
  type maybe<A>
  predicate has<A>(m:maybe<A>)
  function read<A>(m:maybe<A>):A
  function method peek<A>(shared m:maybe<A>):(shared a:A)
      requires has(m)
      ensures a == read(m)
  function method take<A>(linear m:maybe<A>):(linear a:A)
      requires has(m)
      ensures a == read(m)
  function method give<A>(linear a:A):(linear m:maybe<A>)
      ensures has(m)
      ensures read(m) == a
      ensures forall x:maybe<A> {:trigger give(read(x))} | has(x) && a == read(x) :: m == x
  function method empty<A>():(linear m:maybe<A>)
      ensures !has(m)
  function method discard<A>(linear m:maybe<A>):()
      requires !has(m)
// } // module
