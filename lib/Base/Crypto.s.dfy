include "../Lang/NativeTypes.s.dfy"

module {:extern} Crypto {
  import opened NativeTypes

  function method {:extern "Crypto_Compile", "Sha256"} Sha256(t: seq<byte>) : (hash : seq<byte>)
  ensures |hash| == 32

  // NOTE: The CRC-32C checksum is a 4-byte checksum; the value returned
  // by this function is padded up to 32 bytes.
  // TODO: don't do this, just return 4 bytes instead.
  function method {:extern "Crypto_Compile", "Crc32C"} Crc32C(t: seq<byte>) : (hash : seq<byte>)
  ensures |hash| == 32

  method {:extern "Crypto_Compile", "Crc32CArray"} Crc32CArray(t: array<byte>, start: uint64, len: uint64)
  returns (hash : seq<byte>)
  requires 0 <= start
  requires start as int + len as int <= t.Length
  ensures hash == Crc32C(t[start .. start as int + len as int])
}
