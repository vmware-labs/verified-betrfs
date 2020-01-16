include "../Base/NativeTypes.s.dfy"
include "../Base/PackedInts.s.dfy"
include "../Base/Option.s.dfy"
include "../Base/total_order.i.dfy"

module PackedStringArray {
  import opened NativeTypes
  import opened Options
  import opened PackedInts
  import Uint32_Order
  
  datatype Psa = Psa(offsets: seq<uint32>, data: seq<byte>)

  predicate WF(psa: Psa)
  {
    && (|psa.offsets| == 0 ==> |psa.data| == 0)
    && (|psa.offsets| > 0 ==> |psa.data| == psa.offsets[|psa.offsets|-1] as int)
    && Uint32_Order.IsSorted(psa.offsets)
  }

  function psaStart(psa: Psa, i: int) : (start : uint32)
  requires WF(psa)
  requires 0 <= i < |psa.offsets|
  ensures 0 <= start as int <= |psa.data|
  {
    if i == 0 then 0 else
      Uint32_Order.IsSortedImpliesLte(psa.offsets, i-1, |psa.offsets| - 1);
      psa.offsets[i-1]
  }

  function psaEnd(psa: Psa, i: int) : (end : uint32)
  requires WF(psa)
  requires 0 <= i < |psa.offsets|
  ensures psaStart(psa, i) as int <= end as int <= |psa.data|
  {
    var _ := if i > 0 then Uint32_Order.IsSortedImpliesLte(psa.offsets, i-1, i); 0 else 0;
    Uint32_Order.IsSortedImpliesLte(psa.offsets, i, |psa.offsets| - 1);

    psa.offsets[i]
  }

  function psaElement(psa: Psa, i: int) : seq<byte>
  requires WF(psa)
  requires 0 <= i < |psa.offsets|
  {
    psa.data[psaStart(psa, i) .. psaEnd(psa, i)]
  }

  function {:opaque} psaSeq(psa: Psa, i: int) : (res : seq<seq<byte>>)
  requires WF(psa)
  requires 0 <= i <= |psa.offsets|
  ensures |res| == i
  ensures forall j | 0 <= j < i :: res[j] == psaElement(psa, j)
  {
    if i == 0 then [] else psaSeq(psa, i-1) + [psaElement(psa, i-1)]
  }

  function I(psa: Psa) : seq<seq<byte>>
  requires WF(psa)
  {
    psaSeq(psa, |psa.offsets|)
  }

  function parse_Psa(data: seq<byte>) : (res : (Option<Psa>, seq<byte>))
  ensures res.0.Some? ==> WF(res.0.value)
  {
    if |data| >= 4 then (
      var len := unpackLittleEndianUint32(data[0..4]);
      if |data| >= 4 + len as int * 4 then (
        var offsets := unpackLittleEndianUint32Seq(
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
}
