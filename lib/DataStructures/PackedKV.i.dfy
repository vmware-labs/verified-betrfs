include "PackedStringArray.i.dfy"
include "../Base/total_order.i.dfy"
include "../../ByteBlockCacheSystem/KVList.i.dfy"

module PackedKV {
  import PackedStringArray
  import KVList
  import opened NativeTypes
  import Keyspace = Lexicographic_Byte_Order
  import opened KeyType
  import opened ValueType`Internal
  import opened ValueMessage
  import opened BucketsLib

  datatype Pkv = Pkv(
      keys: PackedStringArray.Psa,
      values: PackedStringArray.Psa)

  predicate ValidKeyByteString(s: seq<byte>)
  {
    |s| <= KeyType.MaxLen() as int
  }

  predicate ValidMessageByteString(s: seq<byte>)
  {
    |s| <= ValueType.MaxLen() as int
  }

  predicate ValidKeyLens(psa: PackedStringArray.Psa)
  requires PackedStringArray.WF(psa)
  {
    forall i | 0 <= i < |psa.offsets| ::
        PackedStringArray.psaEnd(psa, i) as int - PackedStringArray.psaStart(psa, i) as int <= KeyType.MaxLen() as int
  }

  predicate WF(pkv: Pkv) {
    && PackedStringArray.WF(pkv.keys)
    && PackedStringArray.WF(pkv.values)
    && ValidKeyLens(pkv.keys)
    && |pkv.keys.offsets| == |pkv.values.offsets|
  }

  function {:opaque} psaSeq_Keys(psa: PackedStringArray.Psa, i: int) : (res : seq<Key>)
  requires PackedStringArray.WF(psa)
  requires ValidKeyLens(psa)
  requires 0 <= i <= |psa.offsets|
  ensures |res| == i
  ensures forall j | 0 <= j < i :: res[j] == PackedStringArray.psaElement(psa, j)
  {
    if i == 0 then [] else psaSeq_Keys(psa, i-1) + [PackedStringArray.psaElement(psa, i-1)]
  }

  function IKeys(psa: PackedStringArray.Psa) : (res : seq<Key>)
  requires PackedStringArray.WF(psa)
  requires ValidKeyLens(psa)
  {
    psaSeq_Keys(psa, |psa.offsets|)
  }

  function method byteString_to_Message(s: seq<byte>) : Message
  requires |s| < 0x1_0000_0000
  {
    if |s| as uint64 <= ValueType.MaxLen() then (
      Define(s)
    ) else (
      // NOTE(travis)
      // It's just convenient to make this function total, so
      // we just do this if the byte string is invalid.
      Define(ValueType.DefaultValue())
    )
  }

  function {:opaque} psaSeq_Messages(psa: PackedStringArray.Psa, i: int) : (res : seq<Message>)
  requires PackedStringArray.WF(psa)
  requires 0 <= i <= |psa.offsets|
  ensures |res| == i
  ensures forall j | 0 <= j < i :: res[j] == byteString_to_Message(PackedStringArray.psaElement(psa, j))
  {
    if i == 0 then [] else psaSeq_Messages(psa, i-1) + [
        byteString_to_Message(PackedStringArray.psaElement(psa, i-1))]
  }

  function IMessages(psa: PackedStringArray.Psa) : (res : seq<Message>)
  requires PackedStringArray.WF(psa)
  {
    psaSeq_Messages(psa, |psa.offsets|)
  }

  function Imap(pkv: Pkv, i: int) : (bucket : Bucket)
  requires WF(pkv)
  requires 0 <= i <= |pkv.keys.offsets|
  ensures WFBucket(bucket)
  {
    reveal_WFBucket();

    if i == 0 then map[] else (
      var key : Key := PackedStringArray.psaElement(pkv.keys, i-1);
      var msg : Message := byteString_to_Message(PackedStringArray.psaElement(pkv.keys, i-1));
      Imap(pkv, i-1)[key := msg]
    )
  }

  function I(pkv: Pkv) : (bucket : Bucket)
  requires WF(pkv)
  ensures WFBucket(bucket)
  {
    Imap(pkv, |pkv.keys.offsets|)
  }

  method ComputeValidKeyLens(psa: PackedStringArray.Psa)
  returns (b: bool)
  requires PackedStringArray.WF(psa)
  ensures b == ValidKeyLens(psa)
  {
    assume false; 

    if |psa.offsets| as uint64 == 0 {
      return true;
    }
    if psa.offsets[0 as uint64] as uint64 > KeyType.MaxLen() {
      return false;
    }

    var i: uint64 := 1;
    while i < |psa.offsets| as uint64
    {
      if psa.offsets[i] as uint64 - psa.offsets[i-1] as uint64 > KeyType.MaxLen() {
        return false;
      }
      i := i + 1;
    }

    return true;
  }
}
