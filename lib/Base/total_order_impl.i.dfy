include "NativeTypes.s.dfy"
include "total_order.i.dfy"

// Methods for total_orders go here because we don't want
// Integer_Order to have any methods, since we don't want to require
// backends to support compiling ints.
abstract module Total_Preorder_Impl {
  import opened Ord : Total_Preorder
  import opened NativeTypes

  method cmp(a: Element, b: Element) returns (c: int32)
    ensures c < 0 ==> lt(a, b) && !lt(b, a)
    ensures c > 0 ==> lt(b, a) && !lt(a, b)
    ensures c == 0 ==> lte(a, b) && lte(b, a)
}

abstract module Total_Order_Impl {
  import opened Ord : Total_Order
  import opened NativeTypes
    
  method cmp(a: Element, b: Element) returns (c: int32)
    ensures c < 0 ==> lt(a, b)
    ensures c > 0 ==> lt(b, a)
    ensures c == 0 ==> a == b
    
  method ComputeIsSorted(s: seq<Element>) returns (result: bool)
    requires |s| < Uint64UpperBound()
    ensures result == IsSorted(s)
  {
    if |s| as uint64 < 2 {
      return true;
    }
    
    var i: uint64 := 0;
    while i < |s| as uint64 - 1
      invariant i < |s| as uint64
      invariant IsSorted(s[..i+1])
    {
      var b := cmp(s[i], s[i+1]);
      if 0 < b {
        reveal_IsSorted();
        return false;
      }
      SortedAugment(s[..i+1], s[i+1]);
      assert s[..i+2] == s[..i+1] + [s[i+1]];
      i := i + 1;
    }
    assert s == s[..i+1];
    return true;
  }

  method ComputeIsStrictlySorted(s: seq<Element>) returns (result: bool)
    requires |s| < Uint64UpperBound()
    ensures result == IsStrictlySorted(s)
  {
    if |s| as uint64 < 2 {
      reveal_IsStrictlySorted();
      return true;
    }

    assert IsStrictlySorted(s[..1]) by {
      reveal_IsStrictlySorted();
    }
    
    var i: uint64 := 0;
    while i < |s| as uint64 - 1
      invariant i < |s| as uint64
      invariant IsStrictlySorted(s[..i+1])
    {
      var b := cmp(s[i], s[i+1]);
      if 0 <= b {
        reveal_IsStrictlySorted();
        return false;
      }
      StrictlySortedAugment(s[..i+1], s[i+1]);
      assert s[..i+2] == s[..i+1] + [s[i+1]];
      i := i + 1;
    }
    assert s == s[..i+1];
    return true;
  }
  
  method ArrayLargestLtePlus1Linear(run: array<Element>, start: uint64, end: uint64, needle: Element) returns (posplus1: uint64)
    requires 0 <= start as int <= end as int <= run.Length < Uint64UpperBound() / 2
    requires IsSorted(run[start..end]);
    ensures posplus1 as int == start as int + LargestLte(run[start..end], needle) + 1
  {
    var i: uint64 := start;
    var t;
    if i < end {
      t := cmp(run[i], needle);
    }
    while i < end && t <= 0
      invariant start <= i <= end
      invariant forall j :: start <= j < i ==> lte(run[j], needle)
      invariant i < end ==> (t <= 0 <==> lte(run[i], needle))
    {
      i := i + 1;
      if i < end {
        t := cmp(run[i], needle);
      }
    }
    forall j | i <= j < end
      ensures lt(needle, run[j])
    {
      reveal_IsSorted();
      assert lt(needle, run[i]);
      assert lte(run[i], run[j]);
    }
    LargestLteIsUnique(run[start..end], needle, i as int - start as int - 1);
    posplus1 := i;
  }

  method ArrayLargestLtePlus1(run: array<Element>, start: uint64, end: uint64, needle: Element) returns (posplus1: uint64)
    requires 0 <= start as int <= end as int <= run.Length < Uint64UpperBound() / 2
    requires IsSorted(run[start..end]);
    ensures posplus1 as int == start as int + LargestLte(run[start..end], needle) + 1
  {
    reveal_IsSorted();
    var lo := start;
    var hi := end + 1;
    while 1 < hi - lo 
      invariant start <= lo < hi <= end + 1
      invariant forall i :: start <= i < lo ==> lte(run[i], needle)
      invariant forall i :: hi - 1 <= i < end ==> lt(needle, run[i])
      decreases hi - lo
    {
      var mid := (lo + hi) / 2;
      var t := cmp(run[mid-1], needle);
      if t <= 0 {
        lo := mid;
      } else {
        hi := mid;
      }
    }
    var i: uint64 := lo;
    /*
    var t;
    if i < hi {
      t := cmp(run[i], needle);
    }
    while i < hi && t <= 0
      invariant start <= i <= end
      invariant forall j :: start <= j < i ==> lte(run[j], needle)
      invariant i < hi ==> (t <= 0 <==> lte(run[i], needle))
    {
      i := i + 1;
      if i < hi {
        t := cmp(run[i], needle);
      }
    }
    forall j | i <= j < end
      ensures lt(needle, run[j])
    {
      reveal_IsSorted();
      assert lt(needle, run[i]);
      assert lte(run[i], run[j]);
    }
    */
    LargestLteIsUnique(run[start..end], needle, i as int - start as int - 1);
    posplus1 := i;
  }
  
  method ArrayLargestLtPlus1(run: array<Element>, start: uint64, end: uint64, needle: Element) returns (posplus1: uint64)
    requires 0 <= start as int <= end as int <= run.Length < Uint64UpperBound() / 2
    requires IsSorted(run[start..end]);
    ensures posplus1 as int == start as int + LargestLt(run[start..end], needle) + 1
  {
    reveal_IsSorted();
    var lo := start;
    var hi := end + 1;
    while 1 < hi - lo 
      invariant start <= lo < hi <= end + 1
      invariant forall i :: start <= i < lo ==> lt(run[i], needle)
      invariant forall i :: hi - 1 <= i < end ==> lte(needle, run[i])
      decreases hi - lo
    {
      var mid := (lo + hi) / 2;
      var t := cmp(run[mid-1], needle);
      if t < 0 {
        lo := mid;
      } else {
        hi := mid;
        assert forall i :: hi - 1 <= i < end ==> lte(needle, run[i]); // observe?!?
      }
    }
    var i: uint64 := lo;
    /*
    var t;
    if i < hi {
      t := cmp(run[i], needle);
    }
    while i < hi && t < 0
      invariant start <= i <= end
      invariant forall j :: start <= j < i ==> lt(run[j], needle)
      invariant i < hi ==> (t < 0 <==> lt(run[i], needle))
    {
      i := i + 1;
      if i < hi {
        t := cmp(run[i], needle);
      }
    }
    */
    LargestLtIsUnique(run[start..end], needle, i as int - start as int - 1);
    posplus1 := i;
  }

  method ComputeLargestLte(run: seq<Element>, needle: Element) returns (res : int64)
    requires |run| < 0x4000_0000_0000_0000
    requires IsSorted(run)
    ensures res as int == LargestLte(run, needle)
  {
    var lo: int64 := 0;
    var hi: int64 := |run| as int64;
    while lo < hi
    invariant 0 <= lo as int <= hi as int <= |run|
    invariant 1 <= lo as int ==> lte(run[lo-1], needle)
    invariant hi as int < |run| ==> lt(needle, run[hi])
    invariant lo <= hi
    decreases hi - lo
    {
      var mid := (lo + hi) / 2;
      var c := cmp(run[mid], needle);
      if (c > 0) {
        hi := mid;
      } else {
        lo := mid+1;
      }
    }

    return lo - 1;
  }
    
  method ComputeLargestLt(run: seq<Element>, needle: Element) returns (res : int64)
    requires |run| < 0x4000_0000_0000_0000
    requires IsSorted(run)
    ensures res as int == LargestLt(run, needle)
  {
    var lo: int64 := 0;
    var hi: int64 := |run| as int64;
    while lo < hi
    invariant 0 <= lo as int <= hi as int <= |run|
    invariant 1 <= lo as int ==> lt(run[lo-1], needle)
    invariant hi as int < |run| ==> lte(needle, run[hi])
    decreases hi - lo
    {
      var mid := (lo + hi) / 2;
      var c := cmp(run[mid], needle);
      if (c < 0) {
        lo := mid+1;
      } else {
        hi := mid;
      }
    }

    return lo - 1;
  }

  method BatchLargestLte(run: seq<Element>, needles: seq<Element>) returns (results: seq<int64>)
    requires |run| < 0x4000_0000_0000_0000
    requires Ord.IsSorted(run)
    requires 0 < |needles| < Uint64UpperBound()
    requires Ord.IsSorted(needles)
    ensures |results| == |needles|
    ensures forall i | 0 <= i < |results| :: results[i] as int == Ord.LargestLte(run, needles[i])
  {
    var aresults := new int64[|needles| as uint64];
    
    var i: uint64 := 0;
    while i < |needles| as uint64
      invariant i as int <= |needles|
      invariant forall j | 0 <= j < i :: aresults[j] as int == Ord.LargestLte(run, needles[j])
    {
      aresults[i] := ComputeLargestLte(run, needles[i]);
      i := i + 1;
    }
    results := aresults[..];
  }
}

module Uint32_Order_Impl refines Total_Order_Impl {
  import opened Ord = Uint32_Order
  method cmp(a: Element, b: Element) returns (c: int32)
  {
    return if a < b then -1 else if a > b then 1 else 0;
  }
}

module Uint64_Preorder_Impl refines Total_Preorder_Impl {
  import opened Ord = Uint64_Order
  method cmp(a: Element, b: Element) returns (c: int32)
  {
    return if a < b then -1 else if a > b then 1 else 0;
  }
}

module Uint64_Order_Impl refines Total_Order_Impl {
  import opened Ord = Uint64_Order
  method cmp(a: Element, b: Element) returns (c: int32)
  {
    return if a < b then -1 else if a > b then 1 else 0;
  }
}

module Char_Order_Impl refines Total_Order_Impl {
  import opened Ord = Char_Order
  method cmp(a: Element, b: Element) returns (c: int32)
  {
    return if a < b then -1 else if a > b then 1 else 0;
  }
}

module Byte_Order_Impl refines Total_Order_Impl {
  import opened Ord = Byte_Order
  method cmp(a: Element, b: Element) returns (c: int32)
  {
    reveal_lte();
    return if a < b then -1 else if a > b then 1 else 0;
  }
}

module Lexicographic_Byte_Order_Impl refines Total_Order_Impl {
  import opened Ord = Lexicographic_Byte_Order
  method cmp(a: Element, b: Element) returns (c: int32)
    ensures c < 0 ==> lt(a, b)
    ensures c > 0 ==> lt(b, a)
    ensures c == 0 ==> a == b
  {
    c := NativeArrays.ByteSeqCmpByteSeq(a, b);
  }
}
