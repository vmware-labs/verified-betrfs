include "NativeTypes.s.dfy"

module {:extern} Crypto {
  import opened NativeTypes

  function method {:axiom} Sha256(t: seq<byte>) : (hash : seq<byte>)
  ensures |hash| == 32

  function method {:axiom} Crc32(t: seq<byte>) : (hash : seq<byte>)
  ensures |hash| == 32

  method {:axiom} Crc32Array(t: array<byte>, start: uint64, len: uint64)
  returns (hash : seq<byte>)
  requires 0 <= start
  requires start as int + len as int <= t.Length
  ensures hash == Crc32(t[start .. start as int + len as int])
}
