include "LinearMaybe.s.dfy"
include "LinearSequence.s.dfy"

module LinearSequence_i {
  import opened NativeTypes
  import opened LinearMaybe
  import opened LinearSequence_s
  export
    provides LinearSequence_s
    provides NativeTypes
    provides seq_alloc_init, lseqs, imagine_lseq, lseq_has, lseq_length, lseq_peek
    provides lseq_alloc, lseq_free, lseq_swap, lseq_take, lseq_give
    provides AllocAndCopy, AllocAndMoveLseq, ImagineInverse, InsertSeq, InsertLSeq
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

  function method seq_alloc_init_iterate<A>(length:uint64, a:A, i:uint64, linear sofar:seq<A>) : (linear s:seq<A>)
    requires i<=length;
    requires |sofar| == length as nat;
    requires forall j:nat | j < i as nat :: sofar[j] == a
    ensures |s| == length as nat;
    ensures forall j:nat | j < length as nat :: s[j] == a
    decreases length - i;
  {
    if i == length then
      sofar
    else
      seq_alloc_init_iterate(length, a, i + 1, seq_set(sofar, i, a))
  }

  function method seq_alloc_init<A>(length:uint64, a:A) : (linear s:seq<A>)
      ensures |s| == length as int
      ensures forall i:nat | i < |s| :: s[i] == a
  {
    seq_alloc_init_iterate(length, a, 0, seq_alloc(length))
  }

  function lseqs<A>(l:lseq<A>):(s:seq<A>)
    ensures rank_is_less_than(s, l)
  {
    var s := seq(lseq_length_raw(l), (i:int) requires 0<=i<lseq_length_raw(l) as int => read(lseqs_raw(l)[i]));
    axiom_lseqs_rank(l, s);
    s
  }

  function imagine_lseq<A>(s:seq<A>):(l:lseq<A>)
    ensures lseqs(l) == s
  {
    imagine_lseq_raw(s)
  }

  lemma ImagineInverse<A>(l:lseq<A>)
    ensures imagine_lseq(lseqs(l)) == l
  {
    // TODO(jonh) uh, -- TODO(chris)?
  }

  function linLast<A>(l:lseq<A>) : A
    requires 0<|l|
  {
    lseqs(l)[|l| - 1]
  }

  function lseq_has<A>(l:lseq<A>):(s:seq<bool>)
      ensures |s| == |lseqs(l)|
  {
      seq(lseq_length_raw(l), (i:int) requires 0<=i<lseq_length_raw(l) as int => has(lseqs_raw(l)[i]))
  }

  predicate lseq_has_all<A>(l:lseq<A>)
  {
    forall i :: 0<=i<|l| ==> lseq_has(l)[i]
  }

  function method lseq_length<A>(shared s:lseq<A>):(n:uint64)
      ensures n as int == |lseqs(s)|
  {
      lseq_length_raw(s)
  }

  function method{:inline true} operator(| |)<A>(shared s:seq<A>):uint64
  {
      seq_length(s)
  }

  function method{:inline true} operator(| |)<A>(shared s:lseq<A>):uint64
  {
      lseq_length(s)
  }

  function{:inline true} operator([])<A>(s:lseq<A>, i:uint64):A
      requires i < |s|
  {
      lseqs(s)[i]
  }

  function{:inline true} operator(in)<A>(s:lseq<A>, i:uint64):bool
      requires i as int < |s| as int
  {
      lseq_has(s)[i]
  }

  function method lseq_peek<A>(shared s:lseq<A>, i:uint64):(shared a:A)
      requires i as nat < |s| as nat && i in s
      ensures a == s[i]
  {
      peek(lseq_share_raw(s, i))
  }

  method lseq_alloc<A>(length:uint64) returns(linear s:lseq<A>)
      ensures |s| == length
      ensures forall i | i < length :: i !in s
  {
      s := lseq_alloc_raw(length);
  }

  method lseq_free<A>(linear s:lseq<A>)
      requires forall i | i < |s| :: i !in s
  {
      assert forall i:uint64 {:trigger lseqs_raw(s)[i]} | i as int < |lseqs_raw(s)| :: i !in s;
      var _ := lseq_free_raw(s);
  }

  // can be implemented as in-place swap
  method lseq_swap<A>(linear s1:lseq<A>, i:uint64, linear a1:A) returns(linear s2:lseq<A>, linear a2:A)
      requires i < |s1| && i in s1
      ensures a2 == s1[i]
      ensures lseq_has(s2) == lseq_has(s1)
      ensures lseqs(s2) == lseqs(s1)[i as nat := a1]
  {
      linear var x1:maybe<A> := give(a1);
      linear var (s2', x2) := lseq_swap_raw_fun(s1, i, x1);
      s2 := s2';
      a2 := unwrap(x2);
  }

  method lseq_take<A>(linear s1:lseq<A>, i:uint64) returns(linear s2:lseq<A>, linear a:A)
      requires i < |s1| && i in s1
      ensures a == s1[i]
      ensures lseq_has(s2) == lseq_has(s1)[i as nat := false]
      ensures forall j:uint64 | j < |s1| && j != i :: lseqs(s2)[j] == lseqs(s1)[j]
  {
      linear var x1:maybe<A> := empty();
      linear var (s2', x2) := lseq_swap_raw_fun(s1, i, x1);
      s2 := s2';
      a := unwrap(x2);
  }

  method lseq_give<A>(linear s1:lseq<A>, i:uint64, linear a:A) returns(linear s2:lseq<A>)
      requires i < |s1|
      requires i !in s1
      ensures lseq_has(s2) == lseq_has(s1)[i as nat := true]
      ensures lseqs(s2) == lseqs(s1)[i as nat := a]
  {
      linear var x1:maybe<A> := give(a);
      linear var (s2', x2) := lseq_swap_raw_fun(s1, i, x1);
      s2 := s2';
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
    dest := seq_alloc(to - from);
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
    requires 0 <= from <= to <= |source|
    requires forall j :: from <= j < to ==> j in source
    ensures lseq_has_all(loot)
    ensures lseqs(loot) == lseqs(source)[from..to]
    ensures |looted| == |source|
    ensures forall j :: 0<=j<|source| && !(from <= j < to) ==> looted[j] == old(source)[j]
    ensures forall j :: 0<=j<|source|
      ==> lseq_has(looted)[j] == if from <= j < to then false else lseq_has(source)[j]
  {
    looted := source;
    ghost var count := (to - from) as nat;
    loot := lseq_alloc(to - from);
    var i:uint64 := from;
    assert to <= |old(source)|;
    while i < to
      invariant from <= i <= to
      invariant |loot| as nat == count
      invariant to <= |looted|
      invariant forall j :: i <= j < to ==> lseq_has(looted)[j]
      invariant forall j :: 0 <= j < to-from ==> lseq_has(loot)[j] == (j < i-from)
      invariant lseqs(loot)[..i-from] == lseqs(old(source))[from..i]
      invariant |looted| == |old(source)|
      invariant forall j :: 0<=j<|source| && !(from <= j < i) ==> looted[j] == old(source)[j]
      invariant forall j :: 0<=j<|looted|
      ==> lseq_has(looted)[j] == if from <= j < i then false else lseq_has(old(source))[j]
    {
      linear var elt:A;
      looted, elt := lseq_take(looted, i);
      loot := lseq_give(loot, i-from, elt);
      i := i + 1;
    }
  }

  method TrustedRuntimeSeqResize<A>(linear s: seq<A>, newlen: uint64)
    returns (linear s2: seq<A>)
    ensures |s2| == newlen as nat
    ensures forall j :: 0 <= j < newlen as nat && j < |s| ==> s2[j] == s[j]

  method TrustedRuntimeLSeqResize<A>(linear s: lseq<A>, newlen: uint64)
    returns (linear s2: lseq<A>)
    ensures |s2| == newlen 
    ensures forall j :: 0 <= j < newlen && j < |s| ==> lseq_has(s2)[j] == lseq_has(s)[j]
    ensures forall j :: |s| <= j < newlen ==> lseq_has(s2)[j] == false
    ensures forall j :: 0 <= j < newlen && j < |s| ==> s2[j] == s[j]

  method InsertSeq<A>(linear s: seq<A>, a: A, pos: uint64) returns (linear s2: seq<A>)
    requires |s| < Uint64UpperBound() - 1;
    requires 0 <= pos as int <= |s|;
    ensures s2 == s[..pos] + [a] + s[pos..];
  {
    var newlen: uint64 := seq_length(s) + 1;
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
    requires |s| as nat < Uint64UpperBound() - 1;
    requires 0 <= pos <= |s|;
    ensures lseq_has_all(s2)
    ensures lseqs(s2) == lseqs(s)[..pos] + [a] + lseqs(s)[pos..];
  {
    var newlen: uint64 := |s| as uint64 + 1;

    s2 := TrustedRuntimeLSeqResize(s, newlen);

    var i:uint64 := newlen - 1;
    while i > pos
      invariant i >= pos
      invariant |s2| == newlen;
      // i is where we're writing next; it's the only hole in s2:
      invariant forall j :: 0 <= j < |s2| ==> lseq_has(s2)[j] == (j != i)
      // Everything before i has its original value
      invariant forall j :: 0 <= j <= i - 1 ==> s2[j] == old(s)[j]
      // Everything after i has the value of its original -1 neighbor
      invariant forall j :: i + 1 <= j < |s2| ==> s2[j] == old(s)[j-1]
    {
      linear var prevElt;
      s2, prevElt := lseq_take(s2, i-1);
      s2 := lseq_give(s2, i, prevElt);
      i := i - 1;
    }
    s2 := lseq_give(s2, pos, a);
  }
} // module
