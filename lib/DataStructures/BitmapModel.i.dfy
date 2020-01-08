include "../Base/NativeTypes.s.dfy"
include "../Base/Option.s.dfy"
include "../Base/BitsetLemmas.i.dfy"
include "../Base/NativeArrays.s.dfy"
//
// Maintains a compact set of integers using a packed-uint64 bitmap
// representation.
//

module BitmapModel {
  import opened NativeTypes
  import opened Options
  import NativeArrays
  import BitsetLemmas

  type BitmapModelT = seq<bool>

  function Len(bm: BitmapModelT) : int
  {
    |bm|
  }

  function {:opaque} BitSet(bm: BitmapModelT, i: int) : (bm' : BitmapModelT)
  requires 0 <= i < Len(bm)
  ensures Len(bm') == Len(bm)
  {
    bm[i := true]
  }

  function {:opaque} BitUnset(bm: BitmapModelT, i: int) : (bm' : BitmapModelT)
  requires 0 <= i < Len(bm)
  ensures Len(bm') == Len(bm)
  {
    bm[i := false]
  }

  predicate {:opaque} IsSet(bm: BitmapModelT, i: int)
  requires 0 <= i < Len(bm)
  {
    bm[i]
  }

  function {:opaque} EmptyBitmap(n: int) : (bm : BitmapModelT)
  requires n >= 0
  ensures Len(bm) == n
  ensures forall i | 0 <= i < Len(bm) :: !IsSet(bm, i)
  {
    if n == 0 then [] else (
      var bm := EmptyBitmap(n-1) + [false];

      reveal_IsSet();
      assert forall i | 0 <= i < n - 1 :: !IsSet(EmptyBitmap(n-1), i);
      assert forall i | 0 <= i < n - 1 :: bm[i] == IsSet(bm, i);
      assert forall i | 0 <= i < n - 1 :: EmptyBitmap(n-1)[i] == IsSet(EmptyBitmap(n-1), i);
      assert forall i | 0 <= i < n - 1 :: bm[i] == EmptyBitmap(n-1)[i];
      assert forall i | 0 <= i < n - 1 :: !IsSet(bm, i);
      assert !IsSet(bm, n - 1);
      assert forall i | 0 <= i < n :: !IsSet(bm, i);

      bm
    )
  }

  function BitAllocIter(bm: BitmapModelT, i: int) : (res: Option<int>)
  requires 0 <= i <= |bm|
  decreases |bm| - i
  ensures res.Some? ==> 0 <= res.value < |bm|
  {
    if i == |bm| then (
      (None)
    ) else if !bm[i] then (
      Some(i)
    ) else (
      BitAllocIter(bm, i+1)
    ) 
  }

  function {:opaque} BitAlloc(bm: BitmapModelT) : (res: Option<int>)
  ensures res.Some? ==> 0 <= res.value < Len(bm)
  {
    BitAllocIter(bm, 0)
  }

  function {:opaque} BitUnion(a: BitmapModelT, b: BitmapModelT) : (res: BitmapModelT)
  requires Len(a) == Len(b)
  ensures Len(res) == Len(a)
  ensures forall i | 0 <= i < Len(res) :: IsSet(res, i) == (IsSet(a, i) || IsSet(b, i))
  {
    reveal_IsSet();
    if |a| == 0 then [] else (
      var res := BitUnion(a[..|a|-1], b[..|b|-1]) + [a[|a|-1] || b[|b|-1]];
      assert IsSet(res, |a|-1) == (IsSet(a, |a|-1) || IsSet(b, |a|-1));
      assert forall i | 0 <= i < Len(res)-1 :: IsSet(a, i) == IsSet(a[..|a|-1], i);
      assert forall i | 0 <= i < Len(res)-1 :: IsSet(b, i) == IsSet(b[..|a|-1], i);
      assert forall i | 0 <= i < Len(res)-1 :: IsSet(res, i) == (IsSet(a, i) || IsSet(b, i));
      assert forall i | 0 <= i < Len(res) :: IsSet(res, i) == (IsSet(a, i) || IsSet(b, i));
      res
    )
  }

  lemma LemmaBitAllocIterResult(bm: BitmapModelT, i: int)
  requires 0 <= i <= |bm|
  ensures var j := BitAllocIter(bm, i);
    && (j.Some? ==> (!IsSet(bm, j.value)))
  decreases |bm| - i
  {
    reveal_IsSet();
    if i == |bm| {
    } else if !bm[i] {
    } else {
      LemmaBitAllocIterResult(bm, i+1);
    }
  }

  lemma LemmaBitAllocResult(bm: BitmapModelT)
  ensures var j := BitAlloc(bm);
    && (j.Some? ==> (!IsSet(bm, j.value)))
  {
    reveal_BitAlloc();
    LemmaBitAllocIterResult(bm, 0);
  }

  lemma LemmaBitAllocIterResultStronger(bm: BitmapModelT, i: int)
  requires 0 <= i <= |bm|
  ensures var j := BitAllocIter(bm, i);
    && (j.Some? ==> (!IsSet(bm, j.value)))
    && (j.Some? ==> (forall k | i <= k < j.value :: IsSet(bm, k)))
    && (j.None? ==> (forall k | i <= k < Len(bm) :: IsSet(bm, k)))
  decreases |bm| - i
  {
    reveal_IsSet();
    if i == |bm| {
    } else if !bm[i] {
    } else {
      LemmaBitAllocIterResultStronger(bm, i+1);
    }
  }

  lemma LemmaBitAllocResultStronger(bm: BitmapModelT)
  ensures var j := BitAlloc(bm);
    && (j.Some? ==> (!IsSet(bm, j.value)))
    && (j.Some? ==> (forall i | 0 <= i < j.value :: IsSet(bm, i)))
    && (j.None? ==> (forall i | 0 <= i < Len(bm) :: IsSet(bm, i)))
  {
    reveal_BitAlloc();
    reveal_IsSet();
    LemmaBitAllocIterResultStronger(bm, 0);
  }
}
