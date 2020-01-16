include "PackedStringArray.i.dfy"

module PackedKV {
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

  predicate WF(pkv: Pkv) {
    && PackedStringArray.WF(pkv.keys)
    && PackedStringArray.WF(pkv.values)
  }
}
