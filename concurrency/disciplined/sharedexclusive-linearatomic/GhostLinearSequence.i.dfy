include "GhostLinearSequence.s.dfy"

module GhostLinearSequence_i {
  import opened GhostLinearMaybe
  import opened GhostLinearSequence_s

  function glseqs<A>(l:glseq<A>):(s:seq<A>)
    ensures rank_is_less_than(s, l)
    ensures |s| == |glseqs_raw(l)|
  {
    var s := seq(|glseqs_raw(l)|, i requires 0 <= i < |glseqs_raw(l)| => read(glseqs_raw(l)[i]));
    axiom_glseqs_rank(l, s);
    s
  }

  function operator(| |)<A>(s:glseq<A>):nat
  {
    |glseqs(s)|
  }

  function{:inline true} operator([])<A>(s:glseq<A>, i:nat):A
      requires i < |s|
  {
    glseqs(s)[i]
  }

  function{:inline true} operator(in)<A>(s:glseq<A>, i:nat): bool
    requires i < |s|
  {
    glseq_has(s)[i]
  }

  function method glseq_take<A>(glinear s1:glseq<A>, i:nat): (glinear p: (glinear glseq<A>, glinear A))
      requires i < |s1| && i in s1
      ensures p.1 == s1[i]
      ensures glseq_has(p.0) == glseq_has(s1)[i := false]
      ensures forall j:nat | j < |s1| && j != i as nat :: glseqs(p.0)[j] == glseqs(s1)[j]
  {
      glinear var x1:gmaybe<A> := empty();
      glinear var (s2tmp, x2) := glseq_swap_raw(s1, i, x1);
      (glinear s2tmp, glinear unwrap(x2))
  }

  function method glseq_give<A>(glinear s1: glseq<A>, i :nat, glinear a:A): (glinear s2: glseq<A>)
    requires i < |s1|
    requires i !in s1
    ensures glseq_has(s2) == glseq_has(s1)[i := true]
    ensures glseqs(s2) == glseqs(s1)[i := a]
  {
      glinear var x1:gmaybe<A> := give(a);
      glinear var (s2tmp, x2) := glseq_swap_raw(s1, i, x1);
      var _ := discard(x2);
      s2tmp
  }

  method lseq_give_inout<A>(glinear inout s1:glseq<A>, i:nat, glinear a:A)
      requires i < |old_s1|
      requires i !in old_s1
      ensures glseq_has(s1) == glseq_has(old_s1)[i := true]
      ensures glseqs(s1) == glseqs(old_s1)[i := a]
  {
    s1 := glseq_give(s1, i, a);
  }

  method lseq_take_inout<A>(glinear inout s:glseq<A>, i: nat) returns(glinear a:A)
      requires i < |old_s| && i in old_s
      ensures a == old_s[i]
      ensures glseq_has(s) == glseq_has(old_s)[i := false]
      ensures forall j:nat | j < |s| && j != i :: glseqs(s)[j] == glseqs(old_s)[j]
  {
    glinear var (s2tmp, x2) := glseq_take(s, i);
    s := s2tmp;
    a := x2;
  }
}
