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

  predicate ValidKeyLens(psa: PackedStringArray.Psa)
  {
    forall i | 0 <= i < |psa.offsets| ::
        PackedStringArray.psaEnd(psa, i) - PackedStringArray.psaStart(psa, i) <= KeyType.MaxLen()
  }

  predicate WF(pkv: Pkv) {
    && PackedStringArray.WF(pkv.keys)
    && PackedStringArray.WF(pkv.values)
    && ValidKeyLens(pkv.keys)
    && ValidMessageLens(pkv.messages)
  }
}
