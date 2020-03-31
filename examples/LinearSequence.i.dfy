include "../lib/Base/sequences.i.dfy"

include "LinearMaybe.s.dfy"
include "LinearSequence.s.dfy"

import opened Sequences

// module LinearSequence_i {
  // import opened LinearMaybe
  // import opened LinearSequence

  method seq_alloc_init<A>(length:nat, a:A) returns(linear s:seq<A>)
      ensures |s| == length
      ensures forall i:nat | i < |s| :: s[i] == a
  {
      s := seq_alloc(length);
      var n := 0;
      while (n < length)
          invariant |s| == length;
          invariant n <= length;
          invariant forall i:nat | i < n :: s[i] == a
      {
          s := seq_set(s, n, a);
          n := n + 1;
      }
  }

  function method lseq_peek<A>(shared s:lseq<A>, i:nat):(shared a:A)
      requires i < |lseqs(s)|
      requires has(lseqs(s)[i])
      ensures a == peek(lseqs(s)[i])
  {
      peek(lseq_share(s, i))
  }

  method lseq_take<A>(linear s1:lseq<A>, i:nat) returns(linear s2:lseq<A>, linear a:A)
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

  method lseq_give<A>(linear s1:lseq<A>, i:nat, linear a:A) returns(linear s2:lseq<A>)
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

  function{:opaque} lseqs_full<A>(s: lseq<A>): (result: seq<A>)
      requires lseq_full(s)
      ensures |result| == lseq_length(s)
      ensures forall i | 0 <= i < lseq_length(s) :: result[i] == peek(lseqs(s)[i])
  {
      Apply(x requires has(x) => peek(x), lseqs(s))
  }

// } // module
