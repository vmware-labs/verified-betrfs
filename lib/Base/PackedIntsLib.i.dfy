include "PackedInts.s.dfy"

module PackedIntsLib {
  import opened NativePackedInts
  import opened NativeTypes

  function method {:opaque} pack_LittleEndian_Uint32(i: uint32)
      : (s : seq<byte>)
  ensures |s| == 4
  ensures unpack_LittleEndian_Uint32(s) == i
  {
    var d0 := i % 256;
    var i1 := (i - d0) / 256;
    var d1 := i1 % 256;
    var i2 := (i1 - d1) / 256;
    var d2 := i2 % 256;
    var i3 := (i2 - d2) / 256;
    var d3 := i3 % 256;
    reveal_unpack_LittleEndian_Uint32();
    /*assert i == d0
        + (d1 * 0x1_00)
        + (d2 * 0x1_00_00)
        + (d3 * 0x1_00_00_00);*/
    [d0 as byte, d1 as byte, d2 as byte, d3 as byte]
  }
}
