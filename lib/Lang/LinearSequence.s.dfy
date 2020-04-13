include "NativeTypes.s.dfy"
include "LinearMaybe.s.dfy"

module {:extern "LinearExtern"} LinearSequence_s {
  import opened NativeTypes
  import opened LinearMaybe

  function method {:extern "LinearExtern", "seq_get"} seq_get<A>(shared s:seq<A>, i:uint64):(a:A)
      requires i as int < |s|
      ensures a == s[i]

  function method {:extern "LinearExtern", "seq_set"} seq_set<A>(linear s1:seq<A>, i:uint64, a:A):(linear s2:seq<A>) // can be implemented as in-place update
      requires i as nat < |s1|
      ensures s2 == s1[i as nat := a]

  function method {:extern "LinearExtern", "seq_length"} seq_length<A>(shared s:seq<A>):(n:uint64)
      ensures n as int == |s|

  function method {:extern "LinearExtern", "seq_alloc"} seq_alloc<A>(length:uint64):(linear s:seq<A>)
      ensures |s| == length as int

  function method {:extern "LinearExtern", "seq_free"} seq_free<A>(linear s:seq<A>):()

  function method {:extern "LinearExtern", "seq_unleash"} seq_unleash<A>(linear s1:seq<A>):(s2:seq<A>)
      ensures s1 == s2


  type {:extern "predefined"} lseq<A>

  function {:axiom} lseqs_raw<A>(l:lseq<A>):(s:seq<maybe<A>>) // contents of an lseq, as ghost seq
    ensures rank_is_less_than(s, l)

  lemma {:axiom} axiom_lseqs_rank<A>(l:lseq<A>, s:seq<A>)
    requires |lseqs_raw(l)| == |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == read(lseqs_raw(l)[i])
    ensures rank_is_less_than(s, l)

  // it's okay to synthesize all the lseqs you want if they're ghosty
  function {:axiom} imagine_lseq_raw<A>(s:seq<A>):(l:lseq<A>)
    requires |s| < 0x1_0000_0000_0000_0000
    ensures lseq_length_raw(l) as int == |s|
    ensures forall i :: 0 <= i < |s| ==> s[i] == read(lseqs_raw(l)[i])

  function method {:extern "LinearExtern", "lseq_length_raw"} lseq_length_raw<A>(shared s:lseq<A>):(n:uint64)
      ensures n as int == |lseqs_raw(s)|

  function method {:extern "LinearExtern", "lseq_alloc_raw"} lseq_alloc_raw<A>(length:uint64):(linear s:lseq<A>)
      ensures |lseqs_raw(s)| == length as nat
      ensures forall i:nat | i < length as nat :: !has(lseqs_raw(s)[i])

  function method {:extern "LinearExtern", "lseq_free_raw"} lseq_free_raw<A>(linear s:lseq<A>):()
      requires forall i:nat | i < |lseqs_raw(s)| :: !has(lseqs_raw(s)[i])

  // can be implemented as in-place swap
  function method {:extern "LinearExtern", "lseq_swap_raw_fun"} lseq_swap_raw_fun<A>(linear s1:lseq<A>, i:uint64, linear a1:maybe<A>):(linear p:(linear lseq<A>, linear maybe<A>))
      requires i as int < |lseqs_raw(s1)|
      ensures p.1 == lseqs_raw(s1)[i]
      ensures lseqs_raw(p.0) == lseqs_raw(s1)[i as int := a1]

  function method {:extern "LinearExtern", "lseq_share_raw"} lseq_share_raw<A>(shared s:lseq<A>, i:uint64):(shared a:maybe<A>)
      requires i as int < |lseqs_raw(s)|
      ensures a == lseqs_raw(s)[i]

} // module
