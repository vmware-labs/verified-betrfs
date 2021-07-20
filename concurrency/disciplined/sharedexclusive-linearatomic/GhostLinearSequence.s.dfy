include "GhostLinearMaybe.s.dfy"

module GhostLinearSequence_s {
  import opened GhostLinearMaybe

  type {:extern "predefined"} glseq<A>

  function {:axiom} glseqs_raw<A>(l: glseq<A>) : (s: seq<gmaybe<A>>)
    ensures rank_is_less_than(s, l)

  function glseq_has<A>(l:glseq<A>):(s:seq<bool>)
    ensures |s| == |glseqs_raw(l)|
  {
    seq(|glseqs_raw(l)|, i requires 0 <= i < |glseqs_raw(l)| => has(glseqs_raw(l)[i]))
  }

  lemma {:axiom} axiom_glseqs_rank<A>(l: glseq<A>, s:seq<A>)
    requires |glseqs_raw(l)| == |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == read(glseqs_raw(l)[i])
    ensures rank_is_less_than(s, l)

  function method glseq_swap_raw<A>(glinear s1:glseq<A>, i:nat, glinear a1:gmaybe<A>):(glinear p:(glinear glseq<A>, glinear gmaybe<A>))
    requires i < |glseqs_raw(s1)|
    ensures p.1 == glseqs_raw(s1)[i]
    ensures glseqs_raw(p.0) == glseqs_raw(s1)[i := a1]

}
