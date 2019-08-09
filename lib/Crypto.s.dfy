include "NativeTypes.s.dfy"

module {:extern} Crypto {
  import opened NativeTypes

  function method {:axiom} Sha256(t: seq<byte>) : (hash : seq<byte>)
  ensures |hash| == 32
}
