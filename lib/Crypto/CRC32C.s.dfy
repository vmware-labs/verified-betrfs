include "../Lang/System/F2_X.s.dfy"

// Our disk model relies on assumptions relating to our checksum
// algorithm, CRC-32 (namely that a block with a valid checksum cannot
// become corrupted to another block with a valid checksum).
// Thus, we need the CRC-32 algorithm in our TCB. The validity of our
// disk model is dependent upon its mathematical properties.

module CRC32_C {
	export S provides crc32_c_padded, NativeTypes
	export Internal reveals *
	export extends S

  import opened Bits_s
  import opened F2_X_s
  import opened NativeTypes

  function bits_of_bytes(s: seq<byte>) : (res : seq<bool>)
  ensures |res| == 8 * |s|
  {
    if |s| == 0 then
      []
    else
      bits_of_bytes(s[0..|s|-1]) + bits_of_int(s[|s|-1] as int, 8) 
  }

  function byte_of_bits(m: seq<bool>) : byte
  requires |m| == 8
  {
      (if m[0] then 0x01 else 0)
    + (if m[1] then 0x02 else 0)
    + (if m[2] then 0x04 else 0)
    + (if m[3] then 0x08 else 0)
    + (if m[4] then 0x10 else 0)
    + (if m[5] then 0x20 else 0)
    + (if m[6] then 0x40 else 0)
    + (if m[7] then 0x80 else 0)
  }

  function {:opaque} crc32_c(s: seq<byte>) : (checksum : seq<byte>)
  ensures |checksum| == 4
  {
    var bitstream := zeroes(32) + reverse(bits_of_bytes(s));
    var bitstream1 := xor(bitstream, zeroes(|bitstream|-32) + ones(32));
    var m := mod_F2_X(bitstream1, bits_of_int(0x1_1EDC_6F41, 33));
    var m1 := xor(reverse(m), ones(32));
    [
      byte_of_bits(m1[0..8]),
      byte_of_bits(m1[8..16]),
      byte_of_bits(m1[16..24]),
      byte_of_bits(m1[24..32])
    ]
  }

  function crc32_c_padded(s: seq<byte>) : (checksum : seq<byte>)
  ensures |checksum| == 32
  {
    crc32_c(s) + seq(28, i => 0)
  }
}
