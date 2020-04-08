include "LinearMaybe.s.dfy"
include "LinearSequence.s.dfy"

module LinearSequence_i {
  import opened LinearMaybe
  import opened LinearSequence_s
  export
    provides LinearSequence_s
    provides seq_alloc_init, lseqs, imagine_lseq, lseq_has, lseq_length, lseq_peek
    provides lseq_alloc, lseq_free, lseq_swap, lseq_take, lseq_give
    reveals lseq_full, linLast
    reveals operator'cardinality?lseq, operator'in?lseq, operator'subscript?lseq

  // method seq_alloc_init<A>(length:nat, a:A) returns(linear s:seq<A>)
  //     ensures |s| == length
  //     ensures forall i:nat | i < |s| :: s[i] == a
  // {
  //     s := seq_alloc(length);
  //     var n := 0;
  //     while (n < length)
  //         invariant |s| == length;
  //         invariant n <= length;
  //         invariant forall i:nat | i < n :: s[i] == a
  //     {
  //         s := seq_set(s, n, a);
  //         n := n + 1;
  //     }
  // }

  function method seq_alloc_init_iterate<A>(length:nat, a:A, i:nat, linear sofar:seq<A>) : (linear s:seq<A>)
    requires i<=length;
    requires |sofar| == length;
    requires forall j:nat | j < i :: sofar[j] == a
    ensures |s| == length;
    ensures forall j:nat | j < length :: s[j] == a
    decreases length - i;
  {
    if i == length then
      sofar
    else
      seq_alloc_init_iterate(length, a, i + 1, seq_set(sofar, i, a))
  }

  function method seq_alloc_init<A>(length:nat, a:A) : (linear s:seq<A>)
      ensures |s| == length
      ensures forall i:nat | i < |s| :: s[i] == a
  {
    seq_alloc_init_iterate(length, a, 0, seq_alloc(length))
  }

  function lseqs<A>(l:lseq<A>):(s:seq<A>)
  {
      seq(lseq_length_raw(l), i requires 0<=i<lseq_length_raw(l) => read(lseqs_raw(l)[i]))
  }

  function imagine_lseq<A>(s:seq<A>):(l:lseq<A>)
    ensures lseqs(l) == s
  {
    imagine_lseq_raw(s)
  }

  function linLast<A>(l:lseq<A>) : A
    requires 0<|l|
  {
    lseqs(l)[|l| - 1]
  }

  function lseq_has<A>(l:lseq<A>):(s:seq<bool>)
      ensures |s| == |lseqs(l)|
  {
      seq(lseq_length_raw(l), i requires 0<=i<lseq_length_raw(l) => has(lseqs_raw(l)[i]))
  }

  function method lseq_length<A>(shared s:lseq<A>):(n:nat)
      ensures n == |lseqs(s)|
  {
      lseq_length_raw(s)
  }

  function method{:inline true} operator(| |)<A>(shared s:seq<A>):nat
  {
      seq_length(s)
  }

  function method{:inline true} operator(| |)<A>(shared s:lseq<A>):nat
  {
      lseq_length(s)
  }

  function{:inline true} operator([])<A>(s:lseq<A>, i:nat):A
      requires i < |s|
  {
      lseqs(s)[i]
  }

  function{:inline true} operator(in)<A>(s:lseq<A>, i:nat):bool
      requires i < |s|
  {
      lseq_has(s)[i]
  }

  function method lseq_peek<A>(shared s:lseq<A>, i:nat):(shared a:A)
      requires i < |s| && i in s
      ensures a == s[i]
  {
      peek(lseq_share_raw(s, i))
  }

  method lseq_alloc<A>(length:nat) returns(linear s:lseq<A>)
      ensures |s| == length
      ensures forall i:nat | i < length :: i !in s
  {
      s := lseq_alloc_raw(length);
  }

  method lseq_free<A>(linear s:lseq<A>)
      requires forall i:nat | i < |s| :: i !in s
  {
      assert forall i:nat {:trigger lseqs_raw(s)[i]} | i < |lseqs_raw(s)| :: i !in s;
      var _ := lseq_free_raw(s);
  }

  // can be implemented as in-place swap
  method lseq_swap<A>(linear s1:lseq<A>, i:nat, linear a1:A) returns(linear s2:lseq<A>, linear a2:A)
      requires i < |s1| && i in s1
      ensures a2 == s1[i]
      ensures lseq_has(s2) == lseq_has(s1)
      ensures lseqs(s2) == lseqs(s1)[i := a1]
  {
      linear var x1:maybe<A> := give(a1);
      linear var x2:maybe<A>;
      s2, x2 := lseq_swap_raw(s1, i, x1);
      a2 := unwrap(x2);
  }

  method lseq_take<A>(linear s1:lseq<A>, i:nat) returns(linear s2:lseq<A>, linear a:A)
      requires i < |s1| && i in s1
      ensures a == s1[i]
      ensures lseq_has(s2) == lseq_has(s1)[i := false]
      ensures forall j:nat | j < |s1| && j != i :: lseqs(s2)[j] == lseqs(s1)[j]
  {
      linear var x1:maybe<A> := empty();
      linear var x2:maybe<A>;
      s2, x2 := lseq_swap_raw(s1, i, x1);
      a := unwrap(x2);
  }

  method lseq_give<A>(linear s1:lseq<A>, i:nat, linear a:A) returns(linear s2:lseq<A>)
      requires i < |s1|
      requires i !in s1
      ensures lseq_has(s2) == lseq_has(s1)[i := true]
      ensures lseqs(s2) == lseqs(s1)[i := a]
  {
      linear var x1:maybe<A> := give(a);
      linear var x2:maybe<A>;
      s2, x2 := lseq_swap_raw(s1, i, x1);
      var _ := discard(x2);
  }

  predicate lseq_full<A>(s: lseq<A>)
  {
      && (forall i | 0 <= i < |s| :: i in s)
  }
} // module
