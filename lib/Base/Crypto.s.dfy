include "../Lang/NativeTypes.s.dfy"
include "../Crypto/CRC32CImpl.i.dfy"

// Our disk model relies on assumptions relating to our checksum
// algorithm, CRC-32 (namely that a block with a valid checksum cannot
// become corrupted to another block with a valid checksum).
// Thus, we need the CRC-32 algorithm in our TCB. The validity of our
// disk model is dependent upon its mathematical properties.

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

module CryptoTest {
  import opened CRC32_C_Impl
  import opened Crypto
  import opened NativeTypes

  method p(x: seq<byte>)
  {
    print "[";
    var i: uint64 := 0;
    while i < |x| as uint64
    {
      print (x[i] as uint64);
      print ", ";
      i := i + 1;
    }
    print "]\n";
  }

  method test() {
    //var x: seq<byte> := [61,6,1,3,5,1,3,4,5,7,9,12,178,15,23,5,6,1,34,4,2,11,32,3,1,5];
    //var x: seq<byte> := [0xff, 0xff, 0xff, 0xff];
    var x: seq<byte> := [0, 0, 0, 0x80];

    var y := Crc32C(x);
    var z := compute_crc32(x);
    p(y);
    p(z);

    x := [];
    y := Crc32C(x);
    z := compute_crc32(x);
    p(y);
    p(z);

    x := [1];
    y := Crc32C(x);
    z := compute_crc32(x);
    p(y);
    p(z);

    x := [1,2,3,4,5];
    y := Crc32C(x);
    z := compute_crc32(x);
    p(y);
    p(z);

    x := [1,2,3,4,5,6,7,8];
    y := Crc32C(x);
    z := compute_crc32(x);
    p(y);
    p(z);

    x := [0xff,0xff,0xff,0xff,0,0,0,0x80];
    y := Crc32C(x);
    z := compute_crc32(x);
    p(y);
    p(z);

    x := [0xff,0xff,0xff,0xff,0,0,0,0,0x80];
    y := Crc32C(x);
    z := compute_crc32(x);
    p(y);
    p(z);

    x := [0xff,0xff,0xff,0xff,0,0,0,0,0,0x80];
    y := Crc32C(x);
    z := compute_crc32(x);
    p(y);
    p(z);

    x := [0xff,0xff,0xff,0xff,0,0,0,0,0,0,0x80];
    y := Crc32C(x);
    z := compute_crc32(x);
    p(y);
    p(z);

  }
}
