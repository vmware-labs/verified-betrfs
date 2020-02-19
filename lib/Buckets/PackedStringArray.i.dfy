include "../Base/NativeTypes.s.dfy"
include "../Base/PackedInts.s.dfy"
include "../Base/Option.s.dfy"
include "../Base/total_order.i.dfy"

module PackedStringArray {
  import opened NativeTypes
  import opened Options
  import opened NativePackedInts
  import opened NativeArrays
  import Uint32_Order
  import opened Sequences
  
  datatype Psa = Psa(offsets: seq<uint32>, data: seq<NativeTypes.byte>)

  predicate WF(psa: Psa)
  {
    && |psa.offsets| < 0x1_0000_0000
    && |psa.data| < 0x1_0000_0000
    && (|psa.offsets| == 0 ==> |psa.data| == 0)
    && (|psa.offsets| > 0 ==> |psa.data| == psa.offsets[|psa.offsets|-1] as int)
    && Uint32_Order.IsSorted(psa.offsets)
  }

  function method psaNumStrings(psa: Psa) : uint64
    requires |psa.offsets| < Uint64UpperBound()
  {
    |psa.offsets| as uint64
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

  lemma psaStartsLte(psa: Psa, i: uint64, j: uint64)
  requires WF(psa)
  requires 0 <= i as int <= j as int < |psa.offsets|
  ensures psaStart(psa, i) <= psaStart(psa, j)
  {
    if i == 0 {
    } else {
      Uint32_Order.IsSortedImpliesLte(psa.offsets, i as int - 1, j as int - 1);
    }
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
  
  function method psaElement(psa: Psa, i: uint64) : seq<byte>
  requires WF(psa)
  requires 0 <= i as int < |psa.offsets|
  {
    psa.data[psaStart(psa, i) .. psaEnd(psa, i)]
  }

  function {:opaque} psaSeq(psa: Psa, i: int) : (res : seq<seq<byte>>)
  requires WF(psa)
  requires 0 <= i <= |psa.offsets|
  ensures |res| == i
  ensures forall j | 0 <= j < i :: res[j] == psaElement(psa, j as uint64)
  {
    if i == 0 then [] else psaSeq(psa, i-1) + [psaElement(psa, (i-1) as uint64)]
  }

  function I(psa: Psa) : seq<seq<byte>>
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
  
  function SizeOfPsa(psa: Psa) : int {
    4 + 4 * |psa.offsets| + |psa.data|
  }

  function method SizeOfPsaUint64(psa: Psa) : uint64
  requires WF(psa)
  {
    4 + 4 * |psa.offsets| as uint64 + |psa.data| as uint64
  }

  function parse_Psa(data: seq<byte>) : (res : (Option<Psa>, seq<byte>))
  ensures res.0.Some? ==> WF(res.0.value)
  {
    if |data| >= 4 then (
      var len := unpack_LittleEndian_Uint32(data[0..4]);
      if |data| >= 4 + len as int * 4 then (
        var offsets := unpack_LittleEndian_Uint32_Seq(
            data[4 .. 4 + len as int * 4], len as int);
        var dataLen := if len == 0 then 0 else offsets[len-1];
        if Uint32_Order.IsSorted(offsets) && |data| >= 4 + len as int * 4 + dataLen as int then (
          var psa := Psa(offsets, data[4 + len as int * 4 .. 4 + len as int * 4 + dataLen as int]);
          (Some(psa), data[4 + len as int * 4 + dataLen as int ..])
        ) else (
          (None, [])
        )
      ) else (
        (None, [])
      )
    ) else (
      (None, [])
    )
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

  // TODO move these somewhere more reasonable

  lemma lemma_seq_suffix_slice<T>(s: seq<T>, i: int, j: int, k: int)
  requires 0 <= i <= |s|
  requires 0 <= j <= k <= |s| - i
  ensures s[i..][j..k] == s[i+j..i+k];
  {
  }

  lemma lemma_seq_slice_suffix<T>(s: seq<T>, i: int, j: int, k: int)
  requires 0 <= i <= j <= |s|
  requires 0 <= k <= j - i
  ensures s[i..j][k..] == s[i+k..j];
  {
  }

  lemma lemma_array_suffix_slice<T>(ar: array<T>, i: int, j: int, k: int)
  requires 0 <= i <= ar.Length
  requires 0 <= j <= k <= ar.Length - i
  ensures ar[i..][j..k] == ar[i+j..i+k];
  {
  }

  lemma lemma_seq_extensionality<T>(s: seq<T>, t: seq<T>)
  requires |s| == |t|
  requires forall i | 0 <= i < |s| :: s[i] == t[i]
  ensures s == t
  {
  }

  lemma lemma_seq_slice_slice<T>(s: seq<T>, i: int, j: int, k: int, l: int)
  requires 0 <= i <= j <= |s|
  requires 0 <= k <= l <= j - i
  ensures s[i..j][k..l] == s[i+k..i+l];
  {
    lemma_seq_extensionality(s[i..j][k..l], s[i+k..i+l]);
  }

  lemma lemma_array_slice_slice<T>(ar: array<T>, i: int, j: int, k: int, l: int)
  requires 0 <= i <= j <= ar.Length
  requires 0 <= k <= l <= j - i
  ensures ar[i..j][k..l] == ar[i+k..i+l];
  {
    lemma_seq_slice_slice(ar[..], i, j, k, l);
  }

  lemma lemma_seq_extensionality_slice<T>(s: seq<T>, t: seq<T>, a: int, b: int)
  requires 0 <= a <= b <= |s|
  requires b <= |t|
  requires forall i | a <= i < b :: s[i] == t[i]
  ensures s[a..b] == t[a..b]
  {
  }

  method Parse_Psa(data: seq<byte>, index:uint64)
  returns (psa: Option<Psa>, rest_index: uint64)
  requires index as int <= |data|
  requires |data| < 0x1_0000_0000_0000_0000
  ensures rest_index as int <= |data|
  ensures var (psa', rest') := parse_Psa(data[index..]);
      && psa == psa'
      && data[rest_index..] == rest'
  {
    if |data| as uint64 - index >= 4 {
      var len_uint32 := Unpack_LittleEndian_Uint32(data, index);
      var len := len_uint32 as uint64;
      lemma_seq_suffix_slice(data, index as int, 0, 4);
      if (|data| as uint64 - 4 - index) / 4 >= len {
        lemma_seq_suffix_slice(data, index as int, 4, (4+4*len) as int);
        var offsets := Unpack_LittleEndian_Uint32_Seq(data, index + 4, len);
        var dataLen := if len == 0 then 0 else offsets[len-1] as uint64;
        var is_sorted := CheckIsSorted(offsets);
        if is_sorted && |data| as uint64 - index - 4 - len * 4 >= dataLen {
          lemma_seq_suffix_slice(data, index as int, (4+4*len) as int, (4+4*len+dataLen) as int);
          psa := Some(Psa(offsets, data[index + 4 + len * 4 .. index + 4 + len * 4 + dataLen]));
          rest_index := index + 4 + len * 4 + dataLen;
        } else {
          psa := None; 
          rest_index := |data| as uint64;
        }
      } else {
        psa := None; 
        rest_index := |data| as uint64;
      }
    } else {
      psa := None; 
      rest_index := |data| as uint64;
    }
  }

  method Marshall_Psa(data: array<byte>, index: uint64, psa: Psa)
  requires 0 <= index
  requires index as int + SizeOfPsa(psa) <= data.Length
  requires data.Length < 0x1_0000_0000_0000_0000
  requires WF(psa)
  modifies data
  ensures forall i | 0 <= i < index as int :: data[i] == old(data[i])
  ensures forall i | index as int + SizeOfPsa(psa) <= i < data.Length :: data[i] == old(data[i])
  ensures parse_Psa(data[index .. index as int + SizeOfPsa(psa)]).0
       == Some(psa)
  {
    ghost var len := |psa.offsets| as uint64;
    ghost var dataLen := |psa.data| as uint64;
    ghost var data_seq0 := data[index .. index as int + SizeOfPsa(psa)];

    // Write number of offsets
    Pack_LittleEndian_Uint32_into_Array(|psa.offsets| as uint32, data, index);

    lemma_array_slice_slice(data, index as int, index as int + SizeOfPsa(psa), 0, 4);
    ghost var data_seq1 := data[index .. index as int + SizeOfPsa(psa)];
    assert unpack_LittleEndian_Uint32(data_seq1[0..4]) as int == |psa.offsets|;

    // Write offsets
    Pack_LittleEndian_Uint32_Seq_into_Array(psa.offsets, data, index + 4);

    lemma_array_slice_slice(data, index as int, index as int + SizeOfPsa(psa), 4, (4+4*len) as int);
    ghost var data_seq2 := data[index .. index as int + SizeOfPsa(psa)];
    lemma_seq_extensionality(data_seq1[0..4], data_seq2[0..4]);
    assert unpack_LittleEndian_Uint32(data_seq2[0..4]) as int == |psa.offsets|;
    assert unpack_LittleEndian_Uint32_Seq(data_seq2[4..4+4*len], len as int) == psa.offsets;

    // Write byte data
    CopySeqIntoArray(psa.data, 0, data,
        index + 4 + 4 * |psa.offsets| as uint64, |psa.data| as uint64);

    ghost var data_seq3 := data[index .. index as int + SizeOfPsa(psa)];
    lemma_seq_extensionality(data_seq2[0..4], data_seq3[0..4]);
    lemma_seq_extensionality_slice(data_seq2, data_seq3, 4, (4+4*len) as int);
    assert unpack_LittleEndian_Uint32(data_seq3[0..4]) as int == |psa.offsets|;
    assert unpack_LittleEndian_Uint32_Seq(data_seq3[4..4+4*len], len as int) == psa.offsets;
    lemma_array_slice_slice(data, index as int, index as int + SizeOfPsa(psa), (4+4*len) as int, (4+4*len+dataLen) as int);
    assert data_seq3[4+4*len..4+4*len+dataLen] == psa.data;
  }

  function method FirstElement(psa: Psa) : seq<byte>
  requires WF(psa)
  requires |psa.offsets| > 0
  {
    psaElement(psa, 0)
  }

  function method LastElement(psa: Psa) : seq<byte>
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

  function psaAppend(psa: Psa, key: seq<byte>) : (result: Psa)
    requires WF(psa)
    requires |psa.offsets| < 0x1_0000_0000 - 1
    requires |psa.data| + |key| < 0x1_0000_0000
    ensures WF(result)
  {
    var newdata := psa.data + key;
    Uint32_Order.SortedAugment(psa.offsets, |newdata| as uint32);
    Psa(psa.offsets + [|newdata| as uint32], newdata)
  }

  lemma psaAppendIAppend(psa: Psa, key: seq<byte>)
    requires WF(psa)
    requires |psa.offsets| < 0x1_0000_0000 - 1
    requires |psa.data| + |key| < 0x1_0000_0000
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
  
}
