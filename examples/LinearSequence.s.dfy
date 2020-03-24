include "../lib/Base/sequences.i.dfy"

include "LinearMaybe.s.dfy"

import opened Sequences

// module LinearSequence {
  // import opened LinearMaybe

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

  function method lseq_peek<A>(shared s:lseq<A>, i:nat):(shared a:A)
      requires i < |lseqs(s)|
      requires has(lseqs(s)[i])
      ensures a == peek(lseqs(s)[i])
  {
      peek(lseq_share(s, i))
  }

  method lseq_get<A>(linear s1:lseq<A>, i:nat) returns(linear s2:lseq<A>, linear a:A)
      requires i < |lseqs(s1)|
      requires has(lseqs(s1)[i])
      ensures a == read(lseqs(s1)[i])
      ensures lseqs(s2) == lseqs(s1)[i := empty()]
  {
      linear var x1:maybe<A> := empty();
      linear var x2:maybe<A>;
      s2, x2 := lseq_swap(s1, i, x1);
      a := unwrap(x2);
  }

  method lseq_set<A>(linear s1:lseq<A>, i:nat, linear a:A) returns(linear s2:lseq<A>)
      requires i < |lseqs(s1)|
      requires !has(lseqs(s1)[i])
      ensures lseqs(s2) == lseqs(s1)[i := give(a)]
  {
      linear var x1:maybe<A> := give(a);
      linear var x2:maybe<A>;
      s2, x2 := lseq_swap(s1, i, x1);
      var _ := discard(x2);
  }

  predicate lseq_full<A>(s: lseq<A>)
  {
      && (forall i | 0 <= i < lseq_length(s) :: has(lseqs(s)[i]))
  }

  function lseqs_full<A>(s: lseq<A>): (result: seq<A>)
      requires lseq_full(s)
      ensures |result| == lseq_length(s)
      ensures forall i | 0 <= i < lseq_length(s) :: result[i] == peek(lseqs(s)[i])
  {
      Apply(x requires has(x) => peek(x), lseqs(s))
  }

// } // module
