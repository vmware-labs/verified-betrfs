// This files contains math axioms which seem to be missing
// from Dafny's (Boogie's?) math reasoning, resulting in
// an incomplete theory.

// TODO follow up on these: file a ticket with Dafny about
// shoring up these holes.

module MathAxioms {
  lemma {:axiom} as_int_as_bv64(a: bv64)
  ensures (a as int) as bv64 == a
}
