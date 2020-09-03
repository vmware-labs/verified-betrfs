include "../Base/NativeTypes.s.dfy"

// Language augmentation providing access to byte-level integer casting.

module {:extern} NativePackedInts {
  import opened NativeTypes

  function {:opaque} unpack_LittleEndian_Uint32(s: seq<byte>) : uint32
  requires |s| == 4
  {
    (s[0] as uint32)
    + (s[1] as uint32 * 0x1_00)
    + (s[2] as uint32 * 0x1_00_00)
    + (s[3] as uint32 * 0x1_00_00_00)
  }

  function {:opaque} unpack_LittleEndian_Uint64(s: seq<byte>) : uint64
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

  function {:opaque} unpack_LittleEndian_Uint32_Seq(
      packed: seq<byte>,
      len: int) : (unpacked: seq<uint32>)
  requires |packed| == len * 4
  ensures |unpacked| == len
  ensures forall i | 0 <= i < len ::
      unpacked[i] == unpack_LittleEndian_Uint32(packed[4*i .. 4*i + 4])
  {
    assert forall i | 0 <= i < len - 1 ::
      packed[4*i .. 4*i + 4] == packed[..4*(len-1)][4*i .. 4*i + 4];

    if len == 0 then [] else (
      unpack_LittleEndian_Uint32_Seq(packed[..4*(len-1)], len-1)
        + [unpack_LittleEndian_Uint32(packed[4*(len-1)..4*len])]
    )
  }

  function {:opaque} unpack_LittleEndian_Uint64_Seq(
      packed: seq<byte>,
      len: int) : (unpacked: seq<uint64>)
  requires |packed| == len * 8
  ensures |unpacked| == len
  ensures forall i | 0 <= i < len ::
      unpacked[i] == unpack_LittleEndian_Uint64(packed[8*i .. 8*i + 8])
  {
    assert forall i | 0 <= i < len - 1 ::
      packed[8*i .. 8*i + 8] == packed[..8*(len-1)][8*i .. 8*i + 8];

    if len == 0 then [] else (
      unpack_LittleEndian_Uint64_Seq(packed[..8*(len-1)], len-1)
        + [unpack_LittleEndian_Uint64(packed[8*(len-1)..8*len])]
    )
  }

  method {:extern "NativePackedInts_Compile", 
      "Unpack__LittleEndian__Uint32"} 
  Unpack_LittleEndian_Uint32(packed: seq<byte>, idx: uint64)
  returns (i: uint32)
  requires 0 <= idx
  requires idx as int + 4 <= |packed|
  requires |packed| < 0x1_0000_0000_0000_0000
  ensures i == unpack_LittleEndian_Uint32(packed[idx .. idx + 4])

  method {:extern "NativePackedInts_Compile", 
      "Unpack__LittleEndian__Uint64"} 
  Unpack_LittleEndian_Uint64(packed: seq<byte>, idx: uint64)
  returns (i: uint64)
  requires 0 <= idx
  requires idx as int + 8 <= |packed|
  requires |packed| < 0x1_0000_0000_0000_0000
  ensures i == unpack_LittleEndian_Uint64(packed[idx .. idx + 8])

  method {:extern "NativePackedInts_Compile", 
      "Pack__LittleEndian__Uint32__into__Array"} 
  Pack_LittleEndian_Uint32_into_Array(i: uint32, ar: array<byte>, idx: uint64)
  requires 0 <= idx
  requires idx as int + 4 <= ar.Length
  requires ar.Length < 0x1_0000_0000_0000_0000
  modifies ar
  ensures forall j | 0 <= j < idx :: ar[j] == old(ar[j])
  ensures unpack_LittleEndian_Uint32(ar[idx .. idx + 4]) == i
  ensures forall j | idx as int + 4 <= j < ar.Length :: ar[j] == old(ar[j])

  method {:extern "NativePackedInts_Compile", 
      "Pack__LittleEndian__Uint64__into__Array"}
  Pack_LittleEndian_Uint64_into_Array(i: uint64, ar: array<byte>, idx: uint64)
  requires 0 <= idx
  requires idx as int + 8 <= ar.Length
  requires ar.Length < 0x1_0000_0000_0000_0000
  modifies ar
  ensures forall j | 0 <= j < idx :: ar[j] == old(ar[j])
  ensures unpack_LittleEndian_Uint64(ar[idx .. idx + 8]) == i
  ensures forall j | idx as int + 8 <= j < ar.Length :: ar[j] == old(ar[j])

  method {:extern "NativePackedInts_Compile", 
      "Unpack__LittleEndian__Uint32__Seq"}
  Unpack_LittleEndian_Uint32_Seq(packed: seq<byte>, idx: uint64, len: uint64)
  returns (unpacked: seq<uint32>)
  requires 0 <= idx
  requires idx as int + 4 * len as int <= |packed|
  requires |packed| < 0x1_0000_0000_0000_0000
  ensures unpacked == unpack_LittleEndian_Uint32_Seq(packed[idx .. idx + 4*len], len as int)

  method {:extern "NativePackedInts_Compile", 
      "Unpack__LittleEndian__Uint64__Seq"}
  Unpack_LittleEndian_Uint64_Seq(packed: seq<byte>, idx: uint64, len: uint64)
  returns (unpacked: seq<uint64>)
  requires 0 <= idx
  requires idx as int + 8 * len as int <= |packed|
  requires |packed| < 0x1_0000_0000_0000_0000
  ensures unpacked == unpack_LittleEndian_Uint64_Seq(packed[idx .. idx + 8*len], len as int)

  method {:extern "NativePackedInts_Compile", 
      "Pack__LittleEndian__Uint32__Seq__into__Array"}
  Pack_LittleEndian_Uint32_Seq_into_Array(unpacked: seq<uint32>, ar: array<byte>, idx: uint64)
  requires 0 <= idx
  requires idx as int + 4 * |unpacked| <= ar.Length
  requires ar.Length < 0x1_0000_0000_0000_0000
  modifies ar
  ensures forall j | 0 <= j < idx :: ar[j] == old(ar[j])
  ensures unpack_LittleEndian_Uint32_Seq(ar[idx .. idx as int + 4*|unpacked|], |unpacked|) == unpacked
  ensures forall j | idx as int + 4 * |unpacked| <= j < ar.Length :: ar[j] == old(ar[j])

  method {:extern "NativePackedInts_Compile", 
      "Pack__LittleEndian__Uint64__Seq__into__Array"}
  Pack_LittleEndian_Uint64_Seq_into_Array(unpacked: seq<uint64>, ar: array<byte>, idx: uint64)
  requires 0 <= idx
  requires idx as int + 8 * |unpacked| <= ar.Length
  requires ar.Length < 0x1_0000_0000_0000_0000
  modifies ar
  ensures forall j | 0 <= j < idx :: ar[j] == old(ar[j])
  ensures unpack_LittleEndian_Uint64_Seq(ar[idx .. idx as int + 8*|unpacked|], |unpacked|) == unpacked
  ensures forall j | idx as int + 8 * |unpacked| <= j < ar.Length :: ar[j] == old(ar[j])
}
