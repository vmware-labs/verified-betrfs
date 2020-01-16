include "../Base/NativeTypes.s.dfy"

module PackedInts {
  import opened NativeTypes

  function {:opaque} unpackLittleEndianUint32(s: seq<byte>) : uint32
  requires |s| == 4
  {
    (s[0] as uint32)
    + (s[1] as uint32 * 0x1_00)
    + (s[2] as uint32 * 0x1_00_00)
    + (s[3] as uint32 * 0x1_00_00_00)
  }

  function {:opaque} unpackLittleEndianUint64(s: seq<byte>) : uint64
  requires |s| == 8
  {
    (s[0] as uint64)
    + (s[1] as uint64 * 0x1_00)
    + (s[2] as uint64 * 0x1_00_00)
    + (s[3] as uint64 * 0x1_00_00_00)
    + (s[4] as uint64 * 0x1_00_00_00_00)
    + (s[5] as uint64 * 0x1_00_00_00_00_00)
    + (s[6] as uint64 * 0x1_00_00_00_00_00_00)
    + (s[7] as uint64 * 0x1_00_00_00_00_00_00_00)
  }

  function {:opaque} unpackLittleEndianUint32Seq(
      packed: seq<byte>,
      len: int) : (unpacked: seq<uint32>)
  requires |packed| == len * 4
  ensures |unpacked| == len
  ensures forall i | 0 <= i < len ::
      unpacked[i] == unpackLittleEndianUint32(packed[4*i .. 4*i + 4])
  {
    assert forall i | 0 <= i < len - 1 ::
      packed[4*i .. 4*i + 4] == packed[..4*(len-1)][4*i .. 4*i + 4];

    if len == 0 then [] else (
      unpackLittleEndianUint32Seq(packed[..4*(len-1)], len-1)
        + [unpackLittleEndianUint32(packed[4*(len-1)..4*len])]
    )
  }

  function {:opaque} unpackLittleEndianUint64Seq(
      packed: seq<byte>,
      len: int) : (unpacked: seq<uint64>)
  requires |packed| == len * 8
  ensures |unpacked| == len
  ensures forall i | 0 <= i < len ::
      unpacked[i] == unpackLittleEndianUint64(packed[8*i .. 8*i + 8])
  {
    assert forall i | 0 <= i < len - 1 ::
      packed[8*i .. 8*i + 8] == packed[..8*(len-1)][8*i .. 8*i + 8];

    if len == 0 then [] else (
      unpackLittleEndianUint64Seq(packed[..8*(len-1)], len-1)
        + [unpackLittleEndianUint64(packed[8*(len-1)..8*len])]
    )
  }

}
