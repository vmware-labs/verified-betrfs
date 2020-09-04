include "LinearMaybe.s.dfy"
include "LinearSequence.s.dfy"

module LinearSequence_i {
  import opened NativeTypes
  import opened LinearMaybe
  import opened LinearSequence_s
  export
    provides LinearSequence_s
    provides NativeTypes
    provides seq_alloc_init, lseqs, imagine_lseq, lseq_has, lseq_length, lseq_length_uint64, lseq_peek
    provides lseq_alloc, lseq_free, lseq_swap, lseq_take, lseq_give
    provides AllocAndCopy, AllocAndMoveLseq, ImagineInverse, SeqResize, InsertSeq, InsertLSeq
    provides share_seq
    reveals as_linear
    reveals lseq_full, linLast, lseq_has_all
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

  // function method seq_alloc_init_iterate<A>(length:uint64, a:A, i:uint64, linear sofar:seq<A>) : (linear s:seq<A>)
  //   requires i<=length;
  //   requires |sofar| == length as nat;
  //   requires forall j:nat | j < i as nat :: sofar[j] == a
  //   ensures |s| == length as nat;
  //   ensures forall j:nat | j < length as nat :: s[j] == a
  //   decreases length - i;
  // {
  //   if i == length then
  //     sofar
  //   else
  //     seq_alloc_init_iterate(length, a, i + 1, seq_set(sofar, i, a))
  // }

  function method seq_alloc_init<A>(length:uint64, a:A) : (linear s:seq<A>)
      ensures |s| == length as int
      ensures forall i:nat | i < |s| :: s[i] == a
  {
    seq_alloc(length, a)
  }

  function lseqs<A>(l:lseq<A>):(s:seq<A>)
    ensures rank_is_less_than(s, l)
  {
    var s := seq(|lseqs_raw(l)| as int, i requires 0<=i<|lseqs_raw(l)| as int => read(lseqs_raw(l)[i]));
    axiom_lseqs_rank(l, s);
    s
  }

  function imagine_lseq<A>(s:seq<A>):(l:lseq<A>)
    ensures lseqs(l) == s
    ensures forall i :: 0 <= i < |s| ==> lseq_has(l)[i]
  {
    imagine_lseq_raw(seq(|s|, i requires 0 <= i < |s| => give(s[i])))
  }

  lemma ImagineInverse<A>(l:lseq<A>)
    requires forall i :: 0 <= i < |lseqs(l)| ==> lseq_has(l)[i]
    ensures imagine_lseq(lseqs(l)) == l
  {
    lemma_lseqs_extensional(imagine_lseq(lseqs(l)), l);
  }

  function linLast<A>(l:lseq<A>) : A
    requires 0<|l|
  {
    lseqs(l)[|l| - 1]
  }

  function lseq_has<A>(l:lseq<A>):(s:seq<bool>)
      ensures |s| == |lseqs(l)|
  {
      seq(|lseqs_raw(l)| as int, i requires 0<=i<|lseqs_raw(l)| as int => has(lseqs_raw(l)[i]))
  }

  lemma lemma_lseqs_extensional<A>(l1:lseq<A>, l2:lseq<A>)
    requires |lseqs(l1)| == |lseqs(l2)|
    requires forall i :: 0 <= i < |lseqs(l1)| ==> lseqs(l1)[i] == lseqs(l2)[i] && lseq_has(l1)[i] == lseq_has(l2)[i]
    ensures l1 == l2
  {

    forall i | 0 <= i < |lseqs(l1)|
      ensures lseqs_raw(l1)[i] == lseqs_raw(l2)[i]
    {
      assert lseqs(l1)[i] == lseqs(l2)[i] && lseq_has(l1)[i] == lseq_has(l2)[i];
      axiom_extensional(lseqs_raw(l1)[i], lseqs_raw(l2)[i]);
    }
    axiom_lseqs_extensional(l1, l2);
  }

  predicate lseq_has_all<A>(l:lseq<A>)
  {
    forall i :: 0<=i<|l| ==> lseq_has(l)[i]
  }

  function method lseq_length_uint64<A>(shared s:lseq<A>) : (n:uint64)
    requires lseq_length(s) <= 0xffff_ffff_ffff_ffff
    ensures n as nat == |lseqs(s)|
  {
    lseq_length_raw(s)
  }

  function lseq_length<A>(s:lseq<A>):(n:nat)
      ensures n == |lseqs(s)|
  {
      |lseqs_raw(s)|
  }

  // function operator(| |)<A>(s:seq<A>):nat
  // {
  //     seq_length(s) as nat
  // }

  function operator(| |)<A>(s:lseq<A>):nat
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

  function method lseq_peek<A>(shared s:lseq<A>, i:uint64):(shared a:A)
      requires i as nat < |s| && i as nat in s
      ensures a == s[i as nat]
  {
      peek(lseq_share_raw(s, i))
  }

  method lseq_alloc<A>(length:uint64) returns(linear s:lseq<A>)
      ensures |s| == length as nat
      ensures forall i:nat | i < length as nat :: i !in s
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
  method lseq_swap<A>(linear s1:lseq<A>, i:uint64, linear a1:A) returns(linear s2:lseq<A>, linear a2:A)
      requires i as nat < |s1| && i as nat in s1
      ensures a2 == s1[i as nat]
      ensures lseq_has(s2) == lseq_has(s1)
      ensures lseqs(s2) == lseqs(s1)[i as nat := a1]
  {
      linear var x1:maybe<A> := give(a1);
      linear var (s2tmp, x2) := lseq_swap_raw_fun(s1, i, x1);
      s2 := s2tmp;
      a2 := unwrap(x2);
  }

  method lseq_take<A>(linear s1:lseq<A>, i:uint64) returns(linear s2:lseq<A>, linear a:A)
      requires i as nat < |s1| && i as nat in s1
      ensures a == s1[i as nat]
      ensures lseq_has(s2) == lseq_has(s1)[i as nat := false]
      ensures forall j:nat | j < |s1| && j != i as nat :: lseqs(s2)[j] == lseqs(s1)[j]
  {
      linear var x1:maybe<A> := empty();
      linear var (s2tmp, x2) := lseq_swap_raw_fun(s1, i, x1);
      s2 := s2tmp;
      a := unwrap(x2);
  }

  method lseq_give<A>(linear s1:lseq<A>, i:uint64, linear a:A) returns(linear s2:lseq<A>)
      requires i as nat < |s1|
      requires i as nat !in s1
      ensures lseq_has(s2) == lseq_has(s1)[i as nat := true]
      ensures lseqs(s2) == lseqs(s1)[i as nat := a]
  {
      linear var x1:maybe<A> := give(a);
      linear var (s2tmp, x2) := lseq_swap_raw_fun(s1, i, x1);
      s2 := s2tmp;
      var _ := discard(x2);
  }

  predicate lseq_full<A>(s: lseq<A>)
  {
      && (forall i | 0 <= i < |s| :: i in s)
  }

  // TODO(robj): "probably not as fast as a memcpy"
  method AllocAndCopy<A>(shared source: seq<A>, from: uint64, to: uint64)
    returns (linear dest: seq<A>)
    requires 0 <= from as nat <= to as nat <= |source|;
    ensures source[from..to] == dest
  {
    if (to == from) {
      dest := seq_empty();
    } else {
      dest := seq_alloc(to - from, seq_get(source, from));
    }
    var i:uint64 := 0;
    var count := to - from;
    while i < count
      invariant i <= count
      invariant |dest| == count as nat
      invariant forall j :: 0<=j<i ==> dest[j] == source[j + from];
    {
      dest := seq_set(dest, i, seq_get(source, i+from));
      i := i + 1;
    }
  }

  method AllocAndMoveLseq<A>(linear source: lseq<A>, from: uint64, to: uint64)
    returns (linear looted: lseq<A>, linear loot: lseq<A>)
    requires 0 <= from as nat <= to as nat <= |source|
    requires forall j :: from as nat <= j < to as nat ==> j in source
    ensures lseq_has_all(loot)
    ensures lseqs(loot) == lseqs(source)[from..to]
    ensures |looted| == |source|
    ensures forall j :: 0<=j<|source| && !(from as nat <= j < to as nat) ==> looted[j] == old(source)[j]
    ensures forall j :: 0<=j<|source|
      ==> lseq_has(looted)[j] == if from as nat <= j < to as nat then false else lseq_has(source)[j]
  {
    looted := source;
    ghost var count := (to - from) as nat;
    loot := lseq_alloc(to - from);
    var i:uint64 := from;
    assert to as nat <= |old(source)|;
    while i < to
      invariant from <= i <= to
      invariant |loot| == count
      invariant to as nat <= |looted|
      invariant forall j :: i <= j < to ==> lseq_has(looted)[j]
      invariant forall j :: 0 <= j < to-from ==> lseq_has(loot)[j] == (j < i-from)
      invariant lseqs(loot)[..i-from] == lseqs(old(source))[from..i]
      invariant |looted| == |old(source)|
      invariant forall j :: 0<=j<|source| && !(from as nat <= j < i as nat) ==> looted[j] == old(source)[j]
      invariant forall j :: 0<=j<|looted|
      ==> lseq_has(looted)[j] == if from as nat <= j < i as nat then false else lseq_has(old(source))[j]
    {
      linear var elt:A;
      looted, elt := lseq_take(looted, i);
      loot := lseq_give(loot, i-from, elt);
      i := i + 1;
    }
  }

  method {:extern "LinearExtern", "TrustedRuntimeSeqResize"} TrustedRuntimeSeqResize<A>(linear s: seq<A>, newlen: uint64)
    returns (linear s2: seq<A>)
    ensures |s2| == newlen as nat
    ensures forall j :: 0 <= j < newlen as nat && j < |s| ==> s2[j] == s[j]

  method {:extern "LinearExtern", "TrustedRuntimeLSeqResize"} TrustedRuntimeLSeqResize<A>(linear s: lseq<A>, newlen: uint64)
    returns (linear s2: lseq<A>)
    ensures |s2| == newlen as nat
    ensures forall j :: 0 <= j < newlen as nat && j < |s| ==> lseq_has(s2)[j] == lseq_has(s)[j]
    ensures forall j :: |s| <= j < newlen as nat ==> lseq_has(s2)[j] == false
    ensures forall j :: 0 <= j < newlen as nat && j < |s| ==> s2[j] == s[j]

  method SeqResize<A>(linear s: seq<A>, newlen: uint64, a: A) returns (linear s2: seq<A>)
    ensures |s2| == newlen as nat
    ensures forall j :: 0 <= j < newlen as nat ==> s2[j] == (if j < |s| then s[j] else a)
  {
    shared_seq_length_bound(s);
    var i:uint64 := seq_length(s);
    s2 := TrustedRuntimeSeqResize(s, newlen);
    while (i < newlen)
      invariant |s2| == newlen as nat
      invariant |s| <= |s2| ==> |s| <= i as nat <= |s2|
      invariant forall j :: 0 <= j < i as nat && j < |s2| ==> s2[j] == (if j < |s| then s[j] else a)
    {
      s2 := seq_set(s2, i, a);
      i := i + 1;
    }
  }

  method InsertSeq<A>(linear s: seq<A>, a: A, pos: uint64) returns (linear s2: seq<A>)
    requires |s| < Uint64UpperBound() - 1;
    requires 0 <= pos as int <= |s|;
    ensures s2 == s[..pos] + [a] + s[pos..];
  {
    var newlen: uint64 := seq_length(s) as uint64 + 1;
    s2 := TrustedRuntimeSeqResize(s, newlen);

    var i:uint64 := newlen - 1;
    while i > pos
      invariant i >= pos
      invariant |s2| == newlen as nat;
      invariant forall j :: 0 <= j <= i as nat - 1 ==> s2[j] == old(s)[j]
      invariant forall j :: i as nat +1 <= j < |s2| ==> s2[j] == old(s)[j-1]
    {
      var prevElt := seq_get(s2, i-1);
      s2 := seq_set(s2, i, prevElt);
      i := i - 1;
    }
    s2 := seq_set(s2, pos, a);
  }

  method InsertLSeq<A>(linear s: lseq<A>, linear a: A, pos: uint64) returns (linear s2: lseq<A>)
    requires lseq_has_all(s)  // robj points out that you only really need to has all the elements >=pos
    requires |s| < Uint64UpperBound() - 1;
    requires 0 <= pos as int <= |s|;
    ensures lseq_has_all(s2)
    ensures lseqs(s2) == lseqs(s)[..pos] + [a] + lseqs(s)[pos..];
  {
    var newlen: uint64 := lseq_length_raw(s) + 1;

    s2 := TrustedRuntimeLSeqResize(s, newlen);

    var i:uint64 := newlen - 1;
    while i > pos
      invariant i >= pos
      invariant |s2| == newlen as nat;
      // i is where we're writing next; it's the only hole in s2:
      invariant forall j :: 0 <= j < |s2| ==> lseq_has(s2)[j] == (j != i as nat)
      // Everything before i has its original value
      invariant forall j :: 0 <= j <= i as nat - 1 ==> s2[j] == old(s)[j]
      // Everything after i has the value of its original -1 neighbor
      invariant forall j :: i as nat +1 <= j < |s2| ==> s2[j] == old(s)[j-1]
    {
      linear var prevElt;
      s2, prevElt := lseq_take(s2, i-1);
      s2 := lseq_give(s2, i, prevElt);
      i := i - 1;
    }
    s2 := lseq_give(s2, pos, a);
  }

  // a wrapper object for borrowing immutable sequences. Necessary so that the C++ translation
  // can use its construction/destruction to track the reference to the borrowed sequence.
  linear datatype as_linear<A> = AsLinear(a:A)

  function method {:extern "LinearExtern", "share_seq"} share_seq<A>(shared a:as_linear<seq<A>>):(shared s:seq<A>)
    ensures s == a.a

  // Intended usage:
  //  linear var l := AsLinear(o);  // Give C++ a chance to increment the ref count on o.
  //  M(share_seq(l));              // borrow the seq in the call to M.
  //  linear var AsLinear(_) := l;  // Free the wrapper, giving C++ a chance to drop the ref count.

} // module LinearSequence_i
