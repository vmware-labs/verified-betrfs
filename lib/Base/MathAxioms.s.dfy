// This files contains math axioms which, for whatever reason,
// don't seem to be provable with Dafny.

module MathAxioms {
  lemma {:axiom} as_int_as_bv64(a: bv64)
  ensures (a as int) as bv64 == a
}
