include "../Base/NativeTypes.s.dfy"
include "../Base/PackedInts.s.dfy"
include "../Base/Option.s.dfy"
include "../Base/total_order.i.dfy"

module PackedStringArray {
  import opened NativeTypes
  import opened Options
  import opened PackedInts
  import opened NativeArrays
  import Uint32_Order
  
  datatype Psa = Psa(offsets: seq<uint32>, data: seq<byte>)

  predicate WF(psa: Psa)
  {
    && |psa.offsets| < 0x1_0000_0000
    && (|psa.offsets| == 0 ==> |psa.data| == 0)
    && (|psa.offsets| > 0 ==> |psa.data| == psa.offsets[|psa.offsets|-1] as int)
    && Uint32_Order.IsSorted(psa.offsets)
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
    var _ := if i > 0 then Uint32_Order.IsSortedImpliesLte(psa.offsets, i as int - 1, i as int); 0 else 0;
    Uint32_Order.IsSortedImpliesLte(psa.offsets, i as int, |psa.offsets| - 1);

    psa.offsets[i]
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
    assume false;
    var i: uint64 := 1;
    while i < |s| as uint64
    {
      if s[i-1] > s[i] {
        return false;
      }
      i := i + 1;
    }
    return true;
  }

  lemma lemma_seq_suffix_slice<T>(s: seq<T>, i: int, j: int, k: int)
  requires 0 <= i <= |s|
  requires 0 <= j <= k <= |s| - i
  ensures s[i..][j..k] == s[i+j..i+k];
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
}
