include "NativeTypes.s.dfy"

module {:extern} TotalOrderNative {
  import opened NativeTypes

  class Arrays
  {
    static predicate lt(a: seq<byte>, b: seq<byte>)
    {
      if |a| == 0 && |b| == 0 then false
      else if |a| == 0 then true
      else if |b| == 0 then false
      else if a[0] < b[0] then true
      else if a[0] > b[0] then false
      else lt(a[1..], b[1..])
    }

    static method{:axiom} ByteSeqCmpByteSeq(s1: seq<byte>, s2: seq<byte>)
        returns (c : int32)
        ensures c < 0 ==> lt(s1, s2)
        ensures c > 0 ==> lt(s2, s1)
        ensures c == 0 ==> s1 == s2
  }
}
