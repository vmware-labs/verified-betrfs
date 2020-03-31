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

  function{:inline true} operator(| |)<A>(s:lseq<A>):nat
  {
      |lseqs(s)|
  }

  function{:inline true} operator([])<A>(s:lseq<A>, i:nat):A
      requires i < |s|
  {
      read(lseqs(s)[i])
  }

  function{:inline true} operator(in)<A>(s:lseq<A>, i:nat):bool
      requires i < |s|
  {
      has(lseqs(s)[i])
  }

  function method lseq_peek<A>(shared s:lseq<A>, i:nat):(shared a:A)
      requires i < |s|
      requires i in s
      ensures a == s[i]
  {
      peek(lseq_share(s, i))
  }

  method lseq_take<A>(linear s1:lseq<A>, i:nat) returns(linear s2:lseq<A>, linear a:A)
      requires i < |s1|
      requires i in s1
      ensures a == s1[i]
      ensures lseqs(s2) == lseqs(s1)[i := empty()]
  {
      linear var x1:maybe<A> := empty();
      linear var x2:maybe<A>;
      s2, x2 := lseq_swap(s1, i, x1);
      a := unwrap(x2);
  }

  method lseq_give<A>(linear s1:lseq<A>, i:nat, linear a:A) returns(linear s2:lseq<A>)
      requires i < |s1|
      requires !(i in s1)
      ensures lseqs(s2) == lseqs(s1)[i := give(a)]
  {
      linear var x1:maybe<A> := give(a);
      linear var x2:maybe<A>;
      s2, x2 := lseq_swap(s1, i, x1);
      var _ := discard(x2);
  }

  predicate lseq_full<A>(s: lseq<A>)
  {
      && (forall i | 0 <= i < |s| :: i in s)
  }

  function{:opaque} lseqs_full<A>(s: lseq<A>): (result: seq<A>)
      requires lseq_full(s)
      ensures |result| == |s|
      ensures forall i | 0 <= i < |s| :: result[i] == s[i]
  {
      Apply(x requires has(x) => peek(x), lseqs(s))
  }

// } // module
