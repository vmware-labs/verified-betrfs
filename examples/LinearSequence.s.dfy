include "LinearMaybe.s.dfy"

// module LinearSequence {
  // import opened LinearMaybe

  function method seq_get<A>(shared s:seq<A>, i:nat):(a:A)
      requires i < |s|
      ensures a == s[i]
  function method seq_set<A>(linear s1:seq<A>, i:nat, a:A):(linear s2:seq<A>) // can be implemented as in-place update
      requires i < |s1|
      ensures s2 == s1[i := a]
  function method seq_length<A>(shared s:seq<A>):(n:nat)
      ensures n == |s|

  method seq_alloc<A>(length:nat) returns(linear s:seq<A>)
      ensures |s| == length

  method seq_free<A>(linear s:seq<A>)

  method seq_unleash<A>(linear s1:seq<A>) returns(s2:seq<A>)
      ensures s1 == s2

  type lseq<A>
  function lseqs<A>(s:lseq<A>):seq<maybe<A>> // contents of an lseq, as ghost seq
  function method lseq_length<A>(shared s:lseq<A>):(n:nat)
      ensures n == |lseqs(s)|

  method lseq_alloc<A>(length:nat) returns(linear s:lseq<A>)
      ensures |lseqs(s)| == length
      ensures forall i:nat | i < length :: !has(lseqs(s)[i])

  method lseq_free<A>(linear s:lseq<A>)
      requires forall i:nat | i < |lseqs(s)| :: !has(lseqs(s)[i])

  // can be implemented as in-place swap
  method lseq_swap<A>(linear s1:lseq<A>, i:nat, linear a1:maybe<A>) returns(linear s2:lseq<A>, linear a2:maybe<A>)
      requires i < |lseqs(s1)|
      ensures a2 == lseqs(s1)[i]
      ensures lseqs(s2) == lseqs(s1)[i := a1]

  function method lseq_share<A>(shared s:lseq<A>, i:nat):(shared a:maybe<A>)
      requires i < |lseqs(s)|
      ensures a == lseqs(s)[i]

// } // module
