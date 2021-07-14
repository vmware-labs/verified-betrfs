include "PCM.s.dfy"

abstract module PCMWrap refines PCM {
  import opened GhostLoc

  /*abstract*/ type G(!new)

  datatype M = M(ghost m: multiset<G>)

  function nil() : M { M(multiset{}) }
  function one(g: G) : M { M(multiset{g}) }

  function unit() : M { nil() }

  function dot(x: M, y: M) : M { M(x.m + y.m) }

  predicate transition(a: M, b: M) { a == b }

  lemma dot_unit(x: M) { }
  lemma commutative(x: M, y: M) { }
  lemma associative(x: M, y: M, z: M) { }
  lemma transition_is_monotonic(a: M, b: M, c: M) { }

  function {:extern} singleton_loc(): Loc

  predicate is_one(m: M) {
    exists a :: m == one(a)
  }

  function get_one(m: M) : G
  requires is_one(m)
  {
    var a :| m == one(a); a
  }
}

module PCMWrapTokens(pcm: PCMWrap) {
  import T = Tokens(pcm)
  type G = pcm.G

  type GToken = t : T.Token | t.loc == pcm.singleton_loc()
    witness *

  function method {:extern} wrap(glinear g: G) : (glinear t: GToken)
  ensures t.val == pcm.one(g)

  function method {:extern} unwrap(glinear t: GToken) : (glinear g: G)
  requires pcm.is_one(t.val)
  ensures g == pcm.get_one(t.val)

  function method {:extern} unwrap_borrow(gshared t: GToken) : (gshared g: G)
  requires pcm.is_one(t.val)
  ensures g == pcm.get_one(t.val)
}
