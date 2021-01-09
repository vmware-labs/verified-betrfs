include "../Lang/NativeTypes.s.dfy"
include "../Lang/LinearSequence.s.dfy"
include "../Lang/System/PackedInts.s.dfy"
include "../Base/Option.s.dfy"
include "../Base/total_order_impl.i.dfy"

module PackedStringArray {
  import opened NativeTypes
  import opened Options
  import opened NativePackedInts
  import opened NativeArrays
  import opened LinearSequence_s
  import opened Sequences
  import Uint32_Order
  import LexOrderImpl = Lexicographic_Byte_Order_Impl
  import LexOrder = LexOrderImpl.Ord
  import UpperLexOrderImpl = Upperbounded_Lexicographic_Byte_Order_Impl
  import UpperLexOrder = UpperLexOrderImpl.Ord

  type Key = LexOrder.Element
  
  datatype Psa = Psa(offsets: seq<uint32>, data: seq<NativeTypes.byte>)

  predicate WF(psa: Psa)
  {
    && |psa.offsets| < 0x1_0000_0000
    && |psa.data| < 0x1_0000_0000
    && (|psa.offsets| == 0 ==> |psa.data| == 0)
    && (0 < |psa.offsets| ==> |psa.data| == psa.offsets[|psa.offsets|-1] as int)
    && Uint32_Order.IsSorted(psa.offsets)
  }

  // TODO psa prefix is silly. Clean up.
  function method psaNumStrings(psa: Psa) : uint64
    requires |psa.offsets| < Uint64UpperBound()
  {
    |psa.offsets| as uint64
  }
  
  function method psaTotalLength(psa: Psa) : uint64
    requires |psa.data| < Uint64UpperBound()
  {
    |psa.data| as uint64
  }
  
  function method psaStart(psa: Psa, i: uint64) : (start : uint32)
  requires WF(psa)
  requires 0 <= i as int < |psa.offsets|
  ensures 0 <= start as int <= |psa.data|
  {
    if i == 0 then 0 else
      Uint32_Order.IsSortedImpliesLte(psa.offsets, i as int - 1, |psa.offsets| - 1);
      psa.offsets[i-1]
  }

    
  function method psaEnd(psa: Psa, i: uint64) : (end : uint32)
  requires WF(psa)
  requires 0 <= i as int < |psa.offsets|
  ensures psaStart(psa, i) as int <= end as int <= |psa.data|
  {
    ghost var _ := if i > 0 then
      Uint32_Order.IsSortedImpliesLte(psa.offsets, i as int - 1, i as int);
      false else false;
    Uint32_Order.IsSortedImpliesLte(psa.offsets, i as int, |psa.offsets| - 1);

    psa.offsets[i]
  }

  lemma psaStartLtePsaEnd(psa: Psa, i: uint64, j: uint64)
    requires WF(psa)
    requires 0 <= i as int <= j as int < |psa.offsets|
    ensures psaStart(psa, i) <= psaEnd(psa, j)
  {
    if i == 0 {
    } else {
      Uint32_Order.IsSortedImpliesLte(psa.offsets, i as int - 1, j as int);
    }
  }
  
  function method psaElement(psa: Psa, i: uint64) : Key
  requires WF(psa)
  requires 0 <= i as int < |psa.offsets|
  {
    psa.data[psaStart(psa, i) .. psaEnd(psa, i)]
  }

  function {:opaque} psaSeq(psa: Psa, i: int) : (res : seq<Key>)
  requires WF(psa)
  requires 0 <= i <= |psa.offsets|
  ensures |res| == i
  ensures forall j | 0 <= j < i :: res[j] == psaElement(psa, j as uint64)
  {
    if i == 0 then [] else psaSeq(psa, i-1) + [psaElement(psa, (i-1) as uint64)]
  }

  function I(psa: Psa) : seq<Key>
  requires WF(psa)
  {
    psaSeq(psa, |psa.offsets|)
  }

  function method EmptyPsa() : (result: Psa)
    ensures WF(result)
    ensures I(result) == []
  {
    assert Uint32_Order.IsSorted([]) by { Uint32_Order.reveal_IsSorted(); }
    Psa([], [])
  }
  
  function SizeOfPsa(psa: Psa) : int
  {
    4 + 4 * |psa.offsets| + |psa.data|
  }

  function method SizeOfPsaUint64(psa: Psa) : uint64
  requires WF(psa)
  {
    4 + 4 * |psa.offsets| as uint64 + |psa.data| as uint64
  }

  method CheckIsSorted(s: seq<uint32>) returns (b: bool)
  requires |s| < 0x1_0000_0000_0000_0000
  ensures b == Uint32_Order.IsSorted(s)
  {
    var i: uint64 := 1;
    if |s| < 2 {
      assert Uint32_Order.IsSorted(s) by { Uint32_Order.reveal_IsSorted(); }
      return true;
    }
    if 0 < |s| {
      assert Uint32_Order.IsSorted(s[..1]) by { Uint32_Order.reveal_IsSorted(); }
    }
    while i < |s| as uint64
      invariant i as int <= |s|
      invariant Uint32_Order.IsSorted(s[..i])
    {
      if s[i-1] > s[i] {
        assert !Uint32_Order.IsSorted(s) by { Uint32_Order.reveal_IsSorted(); }
        return false;
      }
      Uint32_Order.SortedAugment(s[..i], s[i]);
      assert s[..i+1] == s[..i] + [s[i]];
      i := i + 1;
    }
    assert s == s[..i];
    return true;
  }

  function method FirstElement(psa: Psa) : Key
  requires WF(psa)
  requires |psa.offsets| > 0
  {
    psaElement(psa, 0)
  }

  function method LastElement(psa: Psa) : Key
  requires WF(psa)
  requires |psa.offsets| > 0
  {
    psaElement(psa, |psa.offsets| as uint64 - 1)
  }

  function subtractConstant(nums: seq<uint32>, subtrahend: uint32) : (result: seq<uint32>)
    requires forall i :: 0 <= i < |nums| ==> subtrahend <= nums[i]
    ensures |result| == |nums|
    ensures forall i :: 0 <= i < |result| ==> result[i] == nums[i] - subtrahend
  {
    if |nums| == 0 then
      []
    else
      subtractConstant(DropLast(nums), subtrahend) + [Last(nums) - subtrahend]
  }

  method SubtractConstant(nums: seq<uint32>, subtrahend: uint32) returns (result: seq<uint32>)
    requires forall i :: 0 <= i < |nums| ==> subtrahend <= nums[i]
    requires |nums| < Uint64UpperBound()
    ensures result == subtractConstant(nums, subtrahend)
  {
    var arr := newArrayFill(|nums| as uint64, 0);
    var i: uint64 := 0;
    while i < |nums| as uint64
      invariant i <= |nums| as uint64
      invariant forall j :: j < i ==> arr[j] == nums[j] - subtrahend
    {
      arr[i] := nums[i] - subtrahend;
      i := i + 1;
    }
    result := arr[..];
  }
  
  function subOffsets(offsets: seq<uint32>, from: uint64, to: uint64) : (result: seq<uint32>)
    requires Uint32_Order.IsSorted(offsets)
    requires 0 <= from as int <= to as int <= |offsets|
  {
    var suboffsets := offsets[from..to];
    if from == 0 then
      suboffsets
    else
      assert forall i :: 0 <= i < |suboffsets| ==> offsets[from-1] <= suboffsets[i] by { Uint32_Order.reveal_IsSorted(); }
      subtractConstant(suboffsets, offsets[from-1])
  }

  method SubOffsets(offsets: seq<uint32>, from: uint64, to: uint64) returns (result: seq<uint32>)
    requires Uint32_Order.IsSorted(offsets)
    requires 0 <= from as int <= to as int <= |offsets|
    ensures result == subOffsets(offsets, from, to)
  {
    var suboffsets := offsets[from..to];
    if from == 0 {
      result := suboffsets;
    } else {
      assert forall i :: 0 <= i < |suboffsets| ==> offsets[from-1] <= suboffsets[i] by { Uint32_Order.reveal_IsSorted(); }
      result := SubtractConstant(suboffsets, offsets[from-1]);
    }
  }
  
  function psaSubSeqInternal(psa: Psa, from: uint64, to: uint64) : (result: Psa)
    requires WF(psa)
    requires 0 <= from <= to <= psaNumStrings(psa)
  {
    if from == to then
      EmptyPsa()
    else 
      var dataStart := psaStart(psa, from);
      var dataEnd := psaEnd(psa, to-1);
      psaStartLtePsaEnd(psa, from, to-1);
      Psa(subOffsets(psa.offsets, from, to), psa.data[dataStart..dataEnd])
  }

  lemma WFpsaSubSeq(psa: Psa, from: uint64, to: uint64)
    requires WF(psa)
    requires 0 <= from <= to <= psaNumStrings(psa)
    ensures WF(psaSubSeqInternal(psa, from, to))
    ensures I(psaSubSeqInternal(psa, from, to)) == I(psa)[from..to]
  {
    var subpsa := psaSubSeqInternal(psa, from, to);
    assert WF(subpsa) by { Uint32_Order.reveal_IsSorted(); }
    var isubpsa := I(subpsa);
    var ipsasub := I(psa)[from..to];
    assert |isubpsa| == |ipsasub|;
    forall i: uint64 | 0 <= i < |isubpsa| as uint64
      ensures isubpsa[i] == ipsasub[i]
    {
      var dataStart := psaStart(psa, from);
      var dataEnd := psaEnd(psa, to-1);
      var subStart := psaStart(subpsa, i);
      var subEnd := psaEnd(subpsa, i);
      // WTF.  Why isn't this a simple calc of sequence?  This proof seem very brittle.
      forall j  | 0 <= j < subEnd - subStart
        ensures 
        psa.data[dataStart..dataEnd][subStart..subEnd][j] ==
        psa.data[dataStart + subStart..dataStart + subEnd][j]
      {
        // For example of the brittleness of this proof, converting these asserts to a single calc causes the proof to fail.
        assert psa.data[dataStart..dataEnd][subStart..subEnd][j] == psa.data[dataStart..dataEnd][subStart + j];
        assert psa.data[dataStart..dataEnd][subStart..subEnd][j] == psa.data[dataStart + subStart + j];
        assert psa.data[dataStart + subStart..dataStart + subEnd][j] == psa.data[dataStart + subStart + j];
      }
    }
  }

  function psaSubSeq(psa: Psa, from: uint64, to: uint64) : (result: Psa)
    requires WF(psa)
    requires 0 <= from <= to <= psaNumStrings(psa)
    ensures WF(result)
    ensures I(result) == I(psa)[from..to]
  {
    WFpsaSubSeq(psa, from, to);
    psaSubSeqInternal(psa, from, to)
  }
  
  method PsaSubSeq(psa: Psa, from: uint64, to: uint64) returns (result: Psa)
    requires WF(psa)
    requires 0 <= from <= to <= psaNumStrings(psa)
    ensures result == psaSubSeq(psa, from, to)
    ensures WF(psaSubSeq(psa, from, to))
    ensures I(psaSubSeq(psa, from, to)) == I(psa)[from..to]
  {
    if from == to {
      result := EmptyPsa();
    } else {
      var dataStart := psaStart(psa, from);
      var dataEnd := psaEnd(psa, to-1);
      psaStartLtePsaEnd(psa, from, to-1);
      var newoffsets := SubOffsets(psa.offsets, from, to);
      result := Psa(newoffsets, psa.data[dataStart..dataEnd]);
      WFpsaSubSeq(psa, from, to);
    }
  }
  
  method PsaPrefix(psa: Psa, to: uint64) returns (result: Psa)
    requires WF(psa)
    requires 0 <= to <= psaNumStrings(psa)
    ensures WF(result)
    ensures I(result) == I(psa)[..to]
  {
    result := PsaSubSeq(psa, 0, to);
  }
  
  method PsaSuffix(psa: Psa, from: uint64) returns (result: Psa)
    requires WF(psa)
    requires 0 <= from <= psaNumStrings(psa)
    ensures WF(result)
    ensures I(result) == I(psa)[from..]
  {
    result := PsaSubSeq(psa, from, psaNumStrings(psa));
  }
  
  function psaDropLast(psa: Psa) : (result: Psa)
    requires WF(psa)
    requires 0 < psaNumStrings(psa)
    ensures WF(result)
    ensures I(result) == Sequences.DropLast(I(psa))
  {
    WFpsaSubSeq(psa, 0, psaNumStrings(psa)-1);
    psaSubSeq(psa, 0, psaNumStrings(psa)-1)
  }

  predicate psaCanAppend(psa: Psa, key: Key)
  {
    && |psa.offsets| < 0x1_0000_0000 - 1
    && |psa.data| + |key| < 0x1_0000_0000
  }
  
  method PsaCanAppend(psa: Psa, key: Key) returns (result: bool)
    requires WF(psa)
    requires |key| < 0x1_0000_0000
  {
    result :=
      && |psa.offsets| as uint64 < 0x1_0000_0000 - 1
      && |psa.data| as uint64 + |key| as uint64 < 0x1_0000_0000;
  }
  
  function psaAppend(psa: Psa, key: Key) : (result: Psa)
    requires WF(psa)
    requires psaCanAppend(psa, key)
    ensures WF(result)
  {
    var newdata := psa.data + key;
    Uint32_Order.SortedAugment(psa.offsets, |newdata| as uint32);
    Psa(psa.offsets + [|newdata| as uint32], newdata)
  }

  lemma psaAppendIAppend(psa: Psa, key: Key)
    requires WF(psa)
    requires psaCanAppend(psa, key)
    ensures I(psaAppend(psa, key)) == I(psa) + [key]
  {
    var ipsaa := I(psaAppend(psa, key));
    var aipsa := I(psa) + [key];
    assert |ipsaa| == |aipsa|;
    forall i | 0 <= i < |ipsaa|
      ensures ipsaa[i] == aipsa[i]
    {
    }
  }
  
  lemma psaAppendTotalLength(psa: Psa, key: Key)
    requires WF(psa)
    requires psaCanAppend(psa, key)
    ensures psaTotalLength(psaAppend(psa, key)) as int == psaTotalLength(psa) as int + |key|
  {
  }
  
  predicate psaCanAppendSeq(psa: Psa, strs: seq<Key>)
    requires WF(psa)
    decreases |strs|, 0
  {
    && |psa.offsets| + |strs| < 0x1_0000_0000
    && |psa.data| + FlattenLength(FlattenShape(strs)) < 0x1_0000_0000
  }

  lemma psaCanAppendOne(psa: Psa, str: Key)
    requires WF(psa)
    requires psaCanAppendSeq(psa, [str])
    ensures psaCanAppend(psa, str)
  {
    reveal_FlattenShape();
    reveal_FlattenLength();
  }
  
  function psaAppendSeq(psa: Psa, strs: seq<Key>) : (result: Psa)
    requires WF(psa)
    requires psaCanAppendSeq(psa, strs)
    ensures WF(result)
    ensures I(result) == I(psa) + strs
    ensures psaTotalLength(result) == psaTotalLength(psa) + FlattenLength(FlattenShape(strs)) as uint64
    decreases |strs|, 1
  {
    if |strs| == 0 then
      psa
    else
      assert strs == DropLast(strs) + [Last(strs)];
      FlattenShapeAdditive(DropLast(strs), [Last(strs)]);
      FlattenLengthAdditive(FlattenShape(DropLast(strs)), FlattenShape([Last(strs)]));
      assert FlattenLength(FlattenShape(DropLast(strs))) <= FlattenLength(FlattenShape(strs));
      assert |Last(strs)| == FlattenLength(FlattenShape([Last(strs)])) by {
        reveal_FlattenShape();
        reveal_FlattenLength();
      }
      psaAppendIAppend(psaAppendSeq(psa, DropLast(strs)), Last(strs));
      psaAppend(psaAppendSeq(psa, DropLast(strs)), Last(strs))
  }

  lemma psaCanAppendSeqAdditive(psa: Psa, strs1: seq<Key>, strs2: seq<Key>)
    requires WF(psa)
    ensures psaCanAppendSeq(psa, strs1 + strs2) <==>
    psaCanAppendSeq(psa, strs1) && psaCanAppendSeq(psaAppendSeq(psa, strs1), strs2)
  {
    FlattenShapeAdditive(strs1, strs2);
    FlattenLengthAdditive(FlattenShape(strs1), FlattenShape(strs2));
  }

  
  lemma psaAppendSeqAdditive(psa: Psa, strs1: seq<Key>, strs2: seq<Key>)
    requires WF(psa)
    requires psaCanAppendSeq(psa, strs1 + strs2) ||
    (psaCanAppendSeq(psa, strs1) && psaCanAppendSeq(psaAppendSeq(psa, strs1), strs2))
    ensures psaCanAppendSeq(psa, strs1 + strs2) &&
    (psaCanAppendSeq(psa, strs1) && psaCanAppendSeq(psaAppendSeq(psa, strs1), strs2))
    ensures psaAppendSeq(psa, strs1 + strs2) == psaAppendSeq(psaAppendSeq(psa, strs1), strs2)
  {
    psaCanAppendSeqAdditive(psa, strs1, strs2);
    if |strs2| == 0 {
      assert strs1 + strs2 == strs1;
    } else if |strs2| == 1 {
    } else {
      assert strs1 + DropLast(strs2) + [Last(strs2)] == strs1 + strs2;
      psaCanAppendSeqAdditive(psa, strs1 + DropLast(strs2), [Last(strs2)]);
    }
  }
  
  function psaFromSeq(strs: seq<Key>) : (result: Psa)
    requires psaCanAppendSeq(EmptyPsa(), strs)
    ensures WF(result)
    ensures I(result) == strs
  {
    psaAppendSeq(EmptyPsa(), strs)
  }

  lemma psaCanAppendI(psa: Psa)
    requires WF(psa)
    ensures psaCanAppendSeq(EmptyPsa(), I(psa))
    ensures psaAppendSeq(EmptyPsa(), I(psa)) == psa
    decreases psaNumStrings(psa)
  {
    var strs := I(psa);
    if psaNumStrings(psa) == 0 {
    } else if psaNumStrings(psa) == 1 {
      assert psaCanAppendSeq(EmptyPsa(), I(psa)) by {
        reveal_FlattenShape();
        reveal_FlattenLength();
      }
    } else {
      var prepsa := psaDropLast(psa);
      var prestrs := I(prepsa);
      var last := Last(strs);
      assert strs == prestrs + [last];
      psaCanAppendI(prepsa);
      assert psaCanAppendSeq(EmptyPsa(), strs) by {
        reveal_FlattenShape();
        reveal_FlattenLength();
      }
    }
  }
  
  method psaSeqTotalLength(strs: seq<Key>) returns (len: uint64)
    requires psaCanAppendSeq(EmptyPsa(), strs)
    ensures len == psaTotalLength(psaAppendSeq(EmptyPsa(), strs))
  {
    forall i | 0 <= i <= |strs|
      ensures psaCanAppendSeq(EmptyPsa(), strs[..i])
      ensures psaTotalLength(psaAppendSeq(EmptyPsa(), strs[..i])) <= psaTotalLength(psaAppendSeq(EmptyPsa(), strs))
    {
        assert strs == strs[..i] + strs[i..];
        psaAppendSeqAdditive(EmptyPsa(), strs[..i], strs[i..]);
    }

    var curlen: uint64 := 0;
    var i: uint64 := 0;
    while i < |strs| as uint64
      invariant i as int <= |strs|
      invariant curlen == psaTotalLength(psaAppendSeq(EmptyPsa(), strs[..i]))
    {
      assert strs[..i] == DropLast(strs[..i+1]);
      psaAppendTotalLength(psaAppendSeq(EmptyPsa(), strs[..i]), strs[i]);
      curlen := curlen + |strs[i]| as uint64;
      i := i + 1;
    }
    assert strs == strs[..|strs|];
    len := curlen;
  }

  method LargestLte(psa: Psa, key: Key) returns (result: int64)
    requires WF(psa)
    requires LexOrder.IsSorted(I(psa))
    ensures result as int == LexOrder.LargestLte(I(psa), key)
  {
    ghost var ipsa := I(psa);
    var lo: int64 := 0;
    var hi: int64 := psaNumStrings(psa) as int64;

    while lo < hi
      invariant 0 <= lo as int <= hi as int <= |ipsa|
      invariant forall j | 0 <= j < lo :: LexOrder.lte(ipsa[j], key)
      invariant forall j | hi <= j < |ipsa| as int64 :: LexOrder.lt(key, ipsa[j])
    {
      var mid: int64 := (lo + hi) / 2;
      var t := LexOrderImpl.cmp(psaElement(psa, mid as uint64), key);
      if t <= 0 {
        forall j | 0 <= j < mid + 1
          ensures LexOrder.lte(ipsa[j], key)
        {
          LexOrder.IsSortedImpliesLte(ipsa, j as int, mid as int);
        }
        lo := mid + 1;
      } else {
        forall j | mid <= j < |ipsa| as int64
          ensures LexOrder.lt(key, ipsa[j])
        {
          LexOrder.IsSortedImpliesLte(ipsa, mid as int, j as int);
        }
        hi := mid;
      }
    }
    LexOrder.LargestLteIsUnique(ipsa, key, hi as int - 1);
    result := hi - 1;
  }

  method BinarySearchIndexOfFirstKeyGtePivot(psa: Psa, key: UpperLexOrder.Element)
  returns (idx: uint64)
  requires WF(psa)
  ensures idx as int
    == UpperLexOrder.binarySearchIndexOfFirstKeyGte(UpperLexOrder.ToElements(I(psa)), key)
  {
    UpperLexOrder.reveal_binarySearchIndexOfFirstKeyGte();
    var lo: uint64 := 0;
    var hi: uint64 := psaNumStrings(psa) + 1;

    while lo + 1 < hi
    invariant 0 <= lo as int < hi as int <= |I(psa)| + 1
    invariant lo > 0 ==> UpperLexOrder.lt(UpperLexOrder.Element(I(psa)[lo-1]), key)
    invariant hi as int <= |I(psa)| ==> UpperLexOrder.lte(key, UpperLexOrder.Element(I(psa)[hi-1]))
    invariant UpperLexOrder.binarySearchIndexOfFirstKeyGte(UpperLexOrder.ToElements(I(psa)), key)
        == UpperLexOrder.binarySearchIndexOfFirstKeyGteIter(UpperLexOrder.ToElements(I(psa)), key, lo as int, hi as int)
    {
      var mid := (lo + hi) / 2;
      var c := UpperLexOrderImpl.cmp(key, UpperLexOrder.Element(psaElement(psa, mid-1)));
      if c > 0 {
        lo := mid;
      } else {
        hi := mid;
      }
    }
    return lo;
  }

  method BinarySearchIndexOfFirstKeyGte(psa: Psa, key: Key)
  returns (idx: uint64)
  requires WF(psa)
  ensures idx as int
    == LexOrder.binarySearchIndexOfFirstKeyGte(I(psa), key)
  {
    LexOrder.reveal_binarySearchIndexOfFirstKeyGte();
    var lo: uint64 := 0;
    var hi: uint64 := psaNumStrings(psa) + 1;

    while lo + 1 < hi
    invariant 0 <= lo as int < hi as int <= |I(psa)| + 1
    invariant lo > 0 ==> LexOrder.lt(I(psa)[lo-1], key)
    invariant hi as int <= |I(psa)| ==> LexOrder.lte(key, I(psa)[hi-1])
    invariant LexOrder.binarySearchIndexOfFirstKeyGte(I(psa), key)
        == LexOrder.binarySearchIndexOfFirstKeyGteIter(I(psa), key, lo as int, hi as int)
    {
      var mid := (lo + hi) / 2;
      var c := LexOrderImpl.cmp(key, psaElement(psa, mid-1));
      if c > 0 {
        lo := mid;
      } else {
        hi := mid;
      }
    }
    return lo;
  }

  method BinarySearchIndexOfFirstKeyGt(psa: Psa, key: Key)
  returns (idx: uint64)
  requires WF(psa)
  ensures idx as int
    == LexOrder.binarySearchIndexOfFirstKeyGt(I(psa), key)
  {
    LexOrder.reveal_binarySearchIndexOfFirstKeyGt();
    var lo: uint64 := 0;
    var hi: uint64 := psaNumStrings(psa) + 1;

    while lo + 1 < hi
    invariant 0 <= lo as int < hi as int <= |I(psa)| + 1
    invariant lo > 0 ==> LexOrder.lte(I(psa)[lo-1], key)
    invariant hi as int <= |I(psa)| ==> LexOrder.lt(key, I(psa)[hi-1])
    invariant LexOrder.binarySearchIndexOfFirstKeyGt(I(psa), key)
        == LexOrder.binarySearchIndexOfFirstKeyGtIter(I(psa), key, lo as int, hi as int)
    {
      var mid := (lo + hi) / 2;
      var c := LexOrderImpl.cmp(key, psaElement(psa, mid-1));
      if c >= 0 {
        lo := mid;
      } else {
        hi := mid;
      }
    }
    return lo;
  }

  // TODO these could be written in terms of the above
  // less-restrictive binary search methods:
  
  method IndexOfFirstKeyGte(psa: Psa, key: Key) returns (idx: uint64)
    requires WF(psa)
    requires LexOrder.IsSorted(I(psa))
    ensures 0 <= idx as int <= |I(psa)|
    ensures idx as int == LexOrder.IndexOfFirstGte(I(psa), key)
  {
    ghost var ipsa := I(psa);
    
    var lo: uint64 := 0;
    var hi: uint64 := psaNumStrings(psa);

    while lo < hi
      invariant 0 <= lo as int <= |ipsa|
      invariant 0 <= hi as int <= |ipsa|
      invariant forall i | 0 <= i < lo as int :: LexOrder.lt(ipsa[i], key)
      invariant forall i | hi as int <= i < |ipsa| :: LexOrder.lte(key, ipsa[i])
      //decreases hi as int - lo as int
    {
      var mid: uint64 := (lo + hi) / 2;
      var c := LexOrderImpl.cmp(key, psaElement(psa, mid));
      if (c > 0) {
        forall j | 0 <= j < mid
          ensures LexOrder.lt(ipsa[j], key)
        {
          LexOrder.IsSortedImpliesLte(ipsa, j as int, mid as int);
        }
        lo := mid + 1;
      } else {
        forall j | mid as int <= j < |ipsa|
          ensures LexOrder.lte(key, ipsa[j])
        {
          LexOrder.IsSortedImpliesLte(ipsa, mid as int, j);
        }
        hi := mid;
      }
    }

    idx := lo;
    LexOrder.IndexOfFirstGteIsUnique(I(psa), key, idx as nat);
  }

  method IndexOfFirstKeyGt(psa: Psa, key: Key) returns (idx: uint64)
    requires WF(psa)
    requires LexOrder.IsSorted(I(psa))
    ensures 0 <= idx as int <= |I(psa)|
    ensures idx as int == LexOrder.IndexOfFirstGt(I(psa), key)
  {
    ghost var ipsa := I(psa);
    
    var lo: uint64 := 0;
    var hi: uint64 := psaNumStrings(psa);

    while lo < hi
      invariant 0 <= lo as int <= |ipsa|
      invariant 0 <= hi as int <= |ipsa|
      invariant forall i | 0 <= i < lo as int :: LexOrder.lte(ipsa[i], key)
      invariant forall i | hi as int <= i < |ipsa| :: LexOrder.lt(key, ipsa[i])
      //decreases hi as int - lo as int
    {
      var mid: uint64 := (lo + hi) / 2;
      var c := LexOrderImpl.cmp(key, psaElement(psa, mid));
      if (c >= 0) {
        forall j | 0 <= j < mid
          ensures LexOrder.lte(ipsa[j], key)
        {
          LexOrder.IsSortedImpliesLte(ipsa, j as int, mid as int);
        }
        lo := mid + 1;
      } else {
        forall j | mid as int <= j < |ipsa|
          ensures LexOrder.lt(key, ipsa[j])
        {
          LexOrder.IsSortedImpliesLte(ipsa, mid as int, j);
        }
        hi := mid;
      }
    }

    idx := lo;
    LexOrder.IndexOfFirstGtIsUnique(I(psa), key, idx as nat);
  }

  //~ method PivotIndexes(keys: Psa, pivots: seq<Key>) returns (pivotIdxs: seq<uint64>)
  //~   requires WF(keys)
  //~  requires LexOrder.IsSorted(I(keys))
  //~   requires |I(keys)| < Uint64UpperBound()
  //~   requires |pivots| < Uint64UpperBound() - 1
  //~   ensures |pivotIdxs| == |pivots| + 1
  //~  ensures forall i | 0 <= i < |pivots| :: pivotIdxs[i] as nat == LexOrder.IndexOfFirstGte(I(keys), pivots[i])
  //~   ensures Last(pivotIdxs) as nat == |I(keys)|
  //~ {s
  //~   var results := new uint64[|pivots| as uint64 + 1];
  //~   var i : uint64 := 0;
  //~   while i < |pivots| as uint64
  //~     invariant i <= |pivots| as uint64
  //~     invariant forall j | 0 <= j < i :: results[j] as nat == LexOrder.IndexOfFirstGte(I(keys), pivots[j])
  //~   {
  //~     results[i] := IndexOfFirstKeyGte(keys, pivots[i]);
  //~     i := i + 1;
  //~   }

  //~   results[|pivots| as uint64] := psaNumStrings(keys);
  //~   pivotIdxs := results[..];
  //~s }

  linear datatype DynamicPsa = DynamicPsa(
    nstrings: uint64,
    offsets: seq<uint32>,
    data: seq<byte>)
  {
    predicate WF()
    {
      && |offsets| < Uint64UpperBound()
      && |data| < 0x1_0000_0000 
      && nstrings as int <= |offsets|
      && nstrings < 0x1_0000_0000
      && (0 < nstrings ==> offsets[nstrings-1] as int < 0x1_0000_0000)
      && (0 < nstrings ==> offsets[nstrings-1] as int <= |data|)
      && Uint32_Order.IsSorted(offsets[..nstrings])
    }

    shared function method toPsa() : Psa
      requires WF()
    {
      if 0 == nstrings then
        EmptyPsa()
      else 
        Psa(offsets[..nstrings], data[..offsets[nstrings-1]])
    }

    shared method TotalLength() returns (result: uint64)
      requires WF()
      ensures result == psaTotalLength(toPsa())
    {
      if nstrings == 0 {
        result := 0;
      } else {
        result := offsets[nstrings-1] as uint64;
      }
    }

    shared function method weight() : uint64
      requires WF()
    {
      4 * nstrings + if nstrings == 0 then 0 else offsets[nstrings-1] as uint64
    }

    predicate canAppend(str: Key)
      requires WF()
    {
      && psaCanAppend(toPsa(), str)
      && nstrings < |offsets| as uint64
      && psaTotalLength(toPsa()) + |str| as uint64 <= |data| as uint64
    }
    
    shared method CanAppendWORealloc(str: Key) returns (result: bool)
      requires WF()
      requires |str| < 0x1_0000_0000
      ensures result ==> psaCanAppend(toPsa(), str)
    {
      var tl := TotalLength();
      result := 
        && nstrings < |offsets| as uint64
        && nstrings < 0x1_0000_0000 - 1
        && tl + |str| as uint64 <= |data| as uint64;
    }
    
    linear inout method append(str: Key)
      requires old_self.WF()
      requires old_self.canAppend(str)
      ensures self.WF()
      ensures self.toPsa() == psaAppend(old_self.toPsa(), str)
      ensures |self.offsets| == |old_self.offsets|;
      ensures |self.data| == |old_self.data|;
    {
      var start: uint32 := if self.nstrings == 0 then 0 else self.offsets[self.nstrings-1];
      var offset := start + |str| as uint32;
      inout self.offsets := self.offsets[self.nstrings as int := offset];
      // [yizhou7][FIXME] : this is likely wrong/inefficient
      inout self.data := self.data[..start] + str + self.data[offset..];
      // CopySeqIntoArray(str, 0, data, start as uint64, |str| as uint64);

      inout self.nstrings := self.nstrings + 1;
      Uint32_Order.reveal_IsSorted();
    }

    linear inout method realloc_offsets(new_offsets_len: uint64)
      requires old_self.WF()
      requires old_self.nstrings <= new_offsets_len
      ensures self.WF()
      ensures self.toPsa() == old_self.toPsa()
      ensures |self.offsets| == new_offsets_len as int
      ensures self.data == old_self.data
    {
      if new_offsets_len >= |self.offsets| as uint64 {
        var len := new_offsets_len - |self.offsets| as uint64;
        var padding := new uint32[len];
        inout self.offsets := self.offsets + padding[..];
      } else {
        inout self.offsets := self.offsets[..new_offsets_len];
      }

      assert self.offsets[..self.nstrings] == old_self.offsets[..old_self.nstrings];
    }
    
    linear inout method realloc_data(new_data_len: uint64)
      requires old_self.WF()
      requires new_data_len < 0x1_0000_0000 
      requires 0 < old_self.nstrings ==> old_self.offsets[old_self.nstrings-1] as uint64 <= new_data_len
      ensures self.WF()
      ensures self.toPsa() == old_self.toPsa()
      ensures self.offsets == old_self.offsets
      ensures |self.data| == new_data_len as int
    {
      var data_len := if 0 == self.nstrings then 0 else self.offsets[self.nstrings-1];
      if new_data_len >= |self.data| as uint64 {
        var len := new_data_len - |self.data| as uint64;
        var padding := new byte[len];
        inout self.data := self.data + padding[..];
      } else {
        inout self.data := self.data[..new_data_len];
      }
    }

    linear inout method realloc_to_accomodate(str: Key)
      requires old_self.WF()
      requires psaCanAppend(old_self.toPsa(), str)
      ensures self.WF()
      ensures self.toPsa() == old_self.toPsa()
      ensures self.canAppend(str)
    {
      var nstrings := self.nstrings;

      if nstrings == |self.offsets| as uint64 {
        if 0x8000_0000 <= nstrings {
          inout self.realloc_offsets(0xffff_ffff);
        } else {
          inout self.realloc_offsets(2*nstrings + 1);
        }
      }
      var data_len: uint32 := if nstrings == 0 then 0 else self.offsets[nstrings-1];
      assert data_len as uint64 == psaTotalLength(self.toPsa());

      var new_len: uint64 := data_len as uint64 + |str| as uint64;
      if |self.data| as uint64 < new_len {
        if 0x1_0000_0000 <= 2 * new_len {
          inout self.realloc_data(0xffff_ffff);
        } else {
          inout self.realloc_data(2*new_len);
        }
      }
    }
    
    linear inout method Append(str: Key)
      requires old_self.WF()
      requires psaCanAppend(old_self.toPsa(), str)
      ensures self.WF()
      ensures self.toPsa() == psaAppend(old_self.toPsa(), str)
    {
      inout self.realloc_to_accomodate(str);
      inout self.append(str);
    }

    linear inout method appendSeq(strs: seq<Key>)
      requires old_self.WF()
      requires psaCanAppendSeq(old_self.toPsa(), strs)
      requires old_self.nstrings as int + |strs| <= |old_self.offsets|
      requires psaTotalLength(psaAppendSeq(old_self.toPsa(), strs)) as int <= |old_self.data|
      ensures self.WF()
      ensures self.toPsa() == psaAppendSeq(old_self.toPsa(), strs)
    {
      forall i | 0 <= i <= |strs|
        ensures psaCanAppendSeq(old_self.toPsa(), strs[..i])
        ensures psaTotalLength(psaAppendSeq(old_self.toPsa(), strs[..i])) <= psaTotalLength(psaAppendSeq(old_self.toPsa(), strs))
      {
        assert strs == strs[..i] + strs[i..];
        psaAppendSeqAdditive(old_self.toPsa(), strs[..i], strs[i..]);
      }
      
      var i: uint64 := 0;
      while i < |strs| as uint64
        invariant i as int <= |strs|
        invariant self.WF()
        invariant self.nstrings as int + |strs[i..]| <= |self.offsets|;
        invariant psaTotalLength(self.toPsa()) as int <= psaTotalLength(psaAppendSeq(old_self.toPsa(), strs)) as int <= |self.data|
        invariant self.toPsa() == psaAppendSeq(old_self.toPsa(), strs[..i]);
      {
        assert psaTotalLength(self.toPsa()) <= psaTotalLength(psaAppendSeq(old_self.toPsa(), strs));
        assert strs[..i+1] == strs[..i] + [strs[i]];
        assert psaTotalLength(self.toPsa()) as int + |strs[i]| <= psaTotalLength(psaAppendSeq(old_self.toPsa(), strs)) as int;

        inout self.append(strs[i]);
        i := i + 1;
      }
      assert strs[..|strs|] == strs;
    }
    
    linear inout method realloc_to_accomodate_seq(shared strs: seq<Key>)
      requires old_self.WF()
      requires psaCanAppendSeq(old_self.toPsa(), strs)
      ensures self.WF()
      ensures self.toPsa() == old_self.toPsa()
      ensures self.nstrings as int + |strs| <= |self.offsets|
      ensures psaTotalLength(psaAppendSeq(self.toPsa(), strs)) as int <= |self.data|
    {
      forall i | 0 <= i <= |strs|
        ensures psaCanAppendSeq(self.toPsa(), strs[..i])
        ensures psaTotalLength(psaAppendSeq(self.toPsa(), strs[..i])) <= psaTotalLength(psaAppendSeq(self.toPsa(), strs))
      {
        assert strs == strs[..i] + strs[i..];
        psaAppendSeqAdditive(self.toPsa(), strs[..i], strs[i..]);
      }

      var new_offsets_len := self.nstrings + seq_length(strs) as uint64;
      if |self.offsets| as uint64 < new_offsets_len {
        inout self.realloc_offsets(new_offsets_len);
      }

      var total_len: uint64 := if self.nstrings == 0 then 0 else self.offsets[self.nstrings-1] as uint64;

      var i: uint64 := 0;
      while i < seq_length(strs) as uint64
        invariant i as int <= |strs|
        invariant total_len == psaTotalLength(psaAppendSeq(self.toPsa(), strs[..i]))
      {
        assert strs[..i] == DropLast(strs[..i+1]);
        psaAppendTotalLength(psaAppendSeq(self.toPsa(), strs[..i]), strs[i]);
        total_len := total_len + |seq_get(strs, i)| as uint64;
        i := i + 1;
      }
  
      assert strs == strs[..|strs|];
      if |self.data| as uint64 < total_len {
        inout self.realloc_data(total_len);
      }
    }

    linear inout method AppendSeq(shared strs: seq<Key>)
      requires old_self.WF()
      requires psaCanAppendSeq(old_self.toPsa(), strs)
      ensures self.WF()
      ensures self.toPsa() == psaAppendSeq(old_self.toPsa(), strs)
    {
      inout self.realloc_to_accomodate_seq(strs);
      ghost var new_offsets := offsets;
      ghost var new_data := data;

      forall i | 0 <= i <= |strs|
        ensures psaCanAppendSeq(old_self.toPsa(), strs[..i])
        ensures psaTotalLength(psaAppendSeq(old_self.toPsa(), strs[..i])) <= psaTotalLength(psaAppendSeq(old_self.toPsa(), strs))
      {
        assert strs == strs[..i] + strs[i..];
        psaAppendSeqAdditive(old_self.toPsa(), strs[..i], strs[i..]);
      }

      var i: uint64 := 0;
      while i < seq_length(strs) as uint64
        invariant i as int <= |strs|
        invariant self.WF()
        invariant self.nstrings as int + |strs[i..]| <= |self.offsets|;
        invariant psaTotalLength(self.toPsa()) as int <= psaTotalLength(psaAppendSeq(old_self.toPsa(), strs)) as int <= |self.data|
        invariant self.toPsa() == psaAppendSeq(old_self.toPsa(), strs[..i]);
      {
        assert psaTotalLength(self.toPsa()) <= psaTotalLength(psaAppendSeq(old_self.toPsa(), strs));
        assert strs[..i+1] == strs[..i] + [strs[i]];
        assert psaTotalLength(self.toPsa()) as int + |strs[i]| <= psaTotalLength(psaAppendSeq(old_self.toPsa(), strs)) as int;

        inout self.append(seq_get(strs, i));
        i := i + 1;
      }
      assert strs[..|strs|] == strs;
    }
/*

    method Prefix(newlen: uint64)
      requires WF()
      requires newlen <= nstrings
      ensures WF()
      ensures toPsa() == psaSubSeq(old(toPsa()), 0, newlen)
      ensures offsets == old(offsets)
      ensures data == old(data)
      ensures Repr == old(Repr)
      modifies this
    {
      Uint32_Order.SortedSubsequence(offsets[..nstrings], 0, newlen as int);
      assert offsets[..newlen] == offsets[..nstrings][..newlen];
      if 0 < newlen {
        Uint32_Order.IsSortedImpliesLte(offsets[..nstrings], newlen as int - 1, nstrings as int - 1);
      }
      nstrings := newlen;
    }
    
    constructor PreSized(num_strings: uint32, total_len: uint32)
      ensures WF()
      ensures |offsets| == num_strings as int
      ensures data.Length == total_len as int
      ensures toPsa() == EmptyPsa()
      ensures fresh(Repr)
    {
      nstrings := 0;
      offsets := new uint32[num_strings];
      data := new byte[total_len];
      Repr := {this, offsets, data};
    }

    constructor FromSeq(strs: seq<Key>)
      requires psaCanAppendSeq(EmptyPsa(), strs)
      ensures WF()
      ensures |offsets| == |strs|
      ensures data.Length == psaTotalLength(psaFromSeq(strs)) as int
      ensures toPsa() == psaFromSeq(strs)
      ensures fresh(Repr)
    {
      nstrings := 0;
      offsets := new uint32[|strs| as uint64];
      var total_len := psaSeqTotalLength(strs);
      data := new byte[total_len];
      Repr := {this, offsets, data};
      new;
      appendSeq(strs);
    }
    */
  }

/*
  method FromSeq(strs: seq<Key>) returns (psa: Psa)
    requires psaCanAppendSeq(EmptyPsa(), strs)
    ensures WF(psa)
    ensures I(psa) == strs
  {
    var dpsa := new DynamicPsa.FromSeq(strs);
    psa := dpsa.toPsa();
  }

  method ToSeq(psa: Psa) returns (strs: seq<seq<NativeTypes.byte>>)
    requires WF(psa)
    ensures strs == I(psa)
  {
    var nstrings: uint64 := psaNumStrings(psa);
    var astrs := new seq<byte>[nstrings];

    var i: uint64 := 0;
    while i < nstrings
      invariant i <= nstrings
      invariant astrs[..i] == psaSeq(psa, i as int)
    {
      astrs[i] := psaElement(psa, i);
      i := i + 1;
    }
    strs := astrs[..];
  }
  
  lemma UniqueRepr(psa1: Psa, psa2: Psa)
    requires WF(psa1)
    requires WF(psa2)
    requires I(psa1) == I(psa2)
    ensures psa1 == psa2
    decreases |psa1.offsets|
  {
    if |psa1.offsets| == 0 {
    } else {
      var pre1 := psaDropLast(psa1);
      var pre2 := psaDropLast(psa2);
      UniqueRepr(pre1, pre2);
      var last := Last(I(psa1));
      assert psa1.data == pre1.data + last;
    }
  }
  */
}
