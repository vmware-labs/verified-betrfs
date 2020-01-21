include "PackedStringArray.i.dfy"
include "../Base/total_order.i.dfy"

module PackedKV {
  import Keyspace = Lexicographic_Byte_Order

  datatype Pkv = Pkv(
      keys: PackedStringArray.Psa,
      values: PackedStringArray.Psa)

  predicate ValidKeyByteString(s: seq<byte>)
  {
    |s| <= KeyType.MaxLen()
  }

  predicate ValidMessageByteString(s: seq<byte>)
  {
    |s| <= ValueWithDefault.MaxLen()
  }

  predicate ValidKeyByteStringSeq(s: seq<seq<byte>>)
  {
    forall i | 0 <= i < |s| :: ValidKeyByteString(s[i])
  }

  predicate ValidMessageByteStringSeq(s: seq<seq<byte>>)
  {
    forall i | 0 <= i < |s| :: ValidMessageByteString(s[i])
  }

  predicate WF(pkv: Pkv) {
    && PackedStringArray.WF(pkv.keys)
    && PackedStringArray.WF(pkv.values)
  }
}
