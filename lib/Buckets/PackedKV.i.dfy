include "PackedStringArray.i.dfy"
include "../Base/total_order.i.dfy"
include "KVList.i.dfy"

module PackedKV {
  import PackedStringArray
  import KVList
  import opened NativeTypes
  import Keyspace = Lexicographic_Byte_Order
  import opened KeyType
  import opened ValueType`Internal
  import opened ValueMessage
  import opened BucketsLib
  import opened Options

  datatype Pkv = Pkv(
      keys: PackedStringArray.Psa,
      messages: PackedStringArray.Psa)

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
        PackedStringArray.psaEnd(psa, i as uint64) as int - PackedStringArray.psaStart(psa, i as uint64) as int <= KeyType.MaxLen() as int
  }

  predicate WF(pkv: Pkv) {
    && PackedStringArray.WF(pkv.keys)
    && PackedStringArray.WF(pkv.messages)
    && ValidKeyLens(pkv.keys)
    && |pkv.keys.offsets| == |pkv.messages.offsets|
  }

  function {:opaque} psaSeq_Keys(psa: PackedStringArray.Psa, i: int) : (res : seq<Key>)
  requires PackedStringArray.WF(psa)
  requires ValidKeyLens(psa)
  requires 0 <= i <= |psa.offsets|
  ensures |res| == i
  ensures forall j | 0 <= j < i :: res[j] == PackedStringArray.psaElement(psa, j as uint64)
  {
    if i == 0 then [] else psaSeq_Keys(psa, i-1) + [PackedStringArray.psaElement(psa, (i-1) as uint64)]
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
  ensures forall j | 0 <= j < i :: res[j] == byteString_to_Message(PackedStringArray.psaElement(psa, j as uint64))
  {
    if i == 0 then [] else psaSeq_Messages(psa, i-1) + [
        byteString_to_Message(PackedStringArray.psaElement(psa, (i-1) as uint64))]
  }

  function IMessages(psa: PackedStringArray.Psa) : (res : seq<Message>)
  requires PackedStringArray.WF(psa)
  {
    psaSeq_Messages(psa, |psa.offsets|)
  }

  function IMapi(pkv: Pkv, i: int) : (bucket : BucketMap)
  requires WF(pkv)
  requires 0 <= i <= |pkv.keys.offsets|
  ensures WFBucketMap(bucket)
  {
    if i == 0 then map[] else (
      var key : Key := PackedStringArray.psaElement(pkv.keys, (i-1) as uint64);
      var msg : Message := byteString_to_Message(PackedStringArray.psaElement(pkv.keys, (i-1) as uint64));
      IMapi(pkv, i-1)[key := msg]
    )
  }

  function IMap(pkv: Pkv) : (bucket : BucketMap)
  requires WF(pkv)
  ensures WFBucketMap(bucket)
  {
    IMapi(pkv, |pkv.keys.offsets|)
  }

  predicate SortedKeys(pkv: Pkv)
  requires WF(pkv)
  {
    Keyspace.IsStrictlySorted(IKeys(pkv.keys))
  }

  function I(pkv: Pkv) : (bucket : Bucket)
  requires WF(pkv)
  ensures WFBucket(bucket)
  {
    // Note that this might not be WellMarshalled
    assume false;
    BucketMapWithSeq(IMap(pkv), IKeys(pkv.keys), IMessages(pkv.messages))
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

  function SizeOfPkv(pkv: Pkv) : int
  {
    PackedStringArray.SizeOfPsa(pkv.keys) + PackedStringArray.SizeOfPsa(pkv.messages)
  }

  function method SizeOfPkvUint64(pkv: Pkv) : uint64
  requires WF(pkv)
  {
    PackedStringArray.SizeOfPsaUint64(pkv.keys) + PackedStringArray.SizeOfPsaUint64(pkv.messages)
  }

  function method WeightPkv(pkv: Pkv) : uint64
  requires WF(pkv)
  {
    4 * |pkv.keys.offsets| as uint64 + |pkv.keys.data| as uint64 +
    4 * |pkv.messages.offsets| as uint64 + |pkv.messages.data| as uint64
  }

  function parse_Pkv(data: seq<byte>) : (res : (Option<Pkv>, seq<byte>))
  ensures res.0.Some? ==> WF(res.0.value)
  {
    var (keys, rest1) := PackedStringArray.parse_Psa(data);
    if keys.Some? then (
      if ValidKeyLens(keys.value) then (
        var (messages, rest2) := PackedStringArray.parse_Psa(rest1);
        if messages.Some?
            && |keys.value.offsets| == |messages.value.offsets| then (
          var res := Pkv(keys.value, messages.value);
          (Some(res), rest2)
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

  method Parse_Pkv(data: seq<byte>, index:uint64)
  returns (pkv: Option<Pkv>, rest_index: uint64)
  requires index as int <= |data|
  requires |data| < 0x1_0000_0000_0000_0000
  ensures rest_index as int <= |data|
  ensures var (pkv', rest') := parse_Pkv(data[index..]);
      && pkv == pkv'
      && data[rest_index..] == rest'
  {
    var keys, rest1 := PackedStringArray.Parse_Psa(data, index);
    if keys.Some? {
      // TODO we iterate twice, once to check sortedness, another
      // to check lengths, we could consolidate.
      var isValidKeyLens := ComputeValidKeyLens(keys.value);
      if isValidKeyLens {
        var messages, rest2 := PackedStringArray.Parse_Psa(data, rest1);
        if messages.Some?
            && |keys.value.offsets| as uint64 == |messages.value.offsets| as uint64 {
          pkv := Some(Pkv(keys.value, messages.value));
          rest_index := rest2;
        } else {
          pkv := None;
          rest_index := |data| as uint64;
        }
      } else {
        pkv := None;
        rest_index := |data| as uint64;
      }
    } else {
      pkv := None;
      rest_index := |data| as uint64;
    }
  }

  function method FirstKey(pkv: Pkv) : Key
  requires WF(pkv)
  requires |pkv.keys.offsets| > 0
  {
    PackedStringArray.FirstElement(pkv.keys)
  }

  function method LastKey(pkv: Pkv) : Key
  requires WF(pkv)
  requires |pkv.keys.offsets| > 0
  {
    PackedStringArray.LastElement(pkv.keys)
  }

  function method GetKey(pkv: Pkv, i: uint64) : Key
  requires WF(pkv)
  requires 0 <= i as int < |pkv.keys.offsets|
  {
    PackedStringArray.psaElement(pkv.keys, i)
  }

  function method GetMessage(pkv: Pkv, i: uint64) : Message
  requires WF(pkv)
  requires 0 <= i as int < |pkv.messages.offsets|
  {
    byteString_to_Message(PackedStringArray.psaElement(pkv.messages, i))
  }

  method BinarySearchQuery(pkv: Pkv, key: Key)
  returns (msg: Option<Message>)
  requires WF(pkv)
  ensures msg == bucketBinarySearchLookup(I(pkv), key)
  {
    assume false;

    var lo: uint64 := 0;
    var hi: uint64 := |pkv.keys.offsets| as uint64;

    while lo < hi
    {
      var mid: uint64 := (lo + hi) / 2;
      var c := Keyspace.cmp(key, GetKey(pkv, mid));
      if c == 0 {
        msg := Some(GetMessage(pkv, mid));
        return;
      } else if (c < 0) {
        hi := mid;
      } else {
        lo := mid + 1;
      }
    }

    msg := None;
  }

  method ComputeIsSorted(pkv: Pkv)
  returns (b: bool)
  {
    assume false;
    var i: uint64 := 1;
    while i < |pkv.keys.offsets| as uint64
    {
      var c := Keyspace.cmp(GetKey(pkv, i-1), GetKey(pkv, i));
      if c >= 0 {
        return false;
      }
      i := i + 1;
    }
    return true;
  }
}
