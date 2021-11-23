include "PCM.s.dfy"

abstract module PCMWrap refines PCM {
  import opened GhostLoc

  /*abstract*/ type G(!new)

  datatype M = M(ghost m: multiset<G>)

  function nil() : M { M(multiset{}) }
  function one(g: G) : M { M(multiset{g}) }
  // TODO remove? function many(gs: set<G>) : M { M(multiset(gs)) }

  function unit() : M { nil() }

  function dot(x: M, y: M) : M { M(x.m + y.m) }

  predicate transition(a: M, b: M) { a == b }

  predicate valid(x: M) { true }

  lemma dot_unit(x: M) { }
  lemma commutative(x: M, y: M) { }
  lemma associative(x: M, y: M, z: M) { }
  lemma transition_is_monotonic(a: M, b: M, c: M) { }
  lemma transition_is_refl(a: M) { }
  lemma transition_is_trans(a: M, b: M, c: M) { }
  lemma valid_unit(x: M) { }

  function {:extern} singleton_loc(): Loc

  predicate is_one(m: M) {
    exists a :: m == one(a)
  }

  // TODO remove? predicate is_many(m: M) {
    // TODO remove? exists gs :: m == many(gs)
  // TODO remove? }

  function get_one(m: M) : G
  requires is_one(m)
  {
    var a :| m == one(a); a
  }

  // TODO remove? function get_many(m: M) : set<G>
  // TODO remove? requires is_many(m)
  // TODO remove? {
  // TODO remove? var gs :| m == many(gs); gs
  // TODO remove? }
}

module PCMWrapTokens(pcmWrap: PCMWrap) {
  import T = Tokens(pcmWrap)
  type G = pcmWrap.G

  type GToken = t : T.Token | t.loc == pcmWrap.singleton_loc()
    witness *

  function method {:extern} wrap(glinear g: G) : (glinear t: GToken)
  ensures t.val == pcmWrap.one(g)

  function method {:extern} unwrap(glinear t: GToken) : (glinear g: G)
  requires pcmWrap.is_one(t.val)
  ensures g == pcmWrap.get_one(t.val)

  // TODO remove? function method {:extern} unwrap_many(glinear t: GToken) : (glinear g: set<G>)
  // TODO remove? requires pcmWrap.is_many(t.val)
  // TODO remove? ensures g == pcmWrap.get_many(t.val)

  function method {:extern} unwrap_borrow(gshared t: GToken) : (gshared g: G)
  requires pcmWrap.is_one(t.val)
  ensures g == pcmWrap.get_one(t.val)
}
