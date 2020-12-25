include "../NativeTypes.s.dfy"
  
// Language augmentation providing access to byte-level integer casting.

abstract module NativePackedInt {
  import opened NativeTypes
    
  type Integer

  function method Size() : uint64
    ensures 0 < Size()
    
  function unpack(s: seq<byte>) : Integer
    requires |s| == Size() as nat

  function {:opaque} unpack_Seq(packed: seq<byte>, len: nat) : (unpacked: seq<Integer>)
    requires |packed| == len * Size() as nat
    ensures |unpacked| == len
    ensures forall i | 0 <= i < len :: unpacked[i] == unpack(packed[i * Size() as nat.. (i+1) * Size() as nat])
  {
    if len == 0 then
      []
    else (
      var prefix := unpack_Seq(packed[..Size() as nat * (len-1)], len-1);
      var last := unpack(packed[Size() as nat * (len-1)..Size() as nat * len]);
      var result := prefix + [ last ];
      assert forall i | 0 <= i < |prefix| :: packed[..Size() as nat * (len-1)][i * Size() as nat.. (i+1) * Size() as nat] == packed[i * Size() as nat.. (i+1) * Size() as nat];
      result
    )
  }

  method Unpack(packed: seq<byte>, idx: uint64) returns (i: Integer)
    requires idx as nat + Size() as nat <= |packed|
    requires |packed| < Uint64UpperBound()
    ensures i == unpack(packed[idx .. idx as nat + Size() as nat])

  method Pack_into_ByteSeq(i: Integer, linear inout s: seq<byte>, idx: uint64)
    requires idx as int + Size() as nat <= |old_s|
    requires |old_s| < Uint64UpperBound()
    ensures |s| == |old_s|
    ensures forall j | 0 <= j < idx :: s[j] == old_s[j]
    ensures unpack(s[idx .. idx as nat + Size() as nat]) == i
    ensures forall j | idx as nat + Size() as nat <= j < |s| :: s[j] == old_s[j]

  method Unpack_Seq(packed: seq<byte>, idx: uint64, len: uint64) returns (unpacked: seq<Integer>)
    requires idx as nat + Size() as nat * len as nat <= |packed|
    requires |packed| < Uint64UpperBound()
    ensures unpacked == unpack_Seq(packed[idx .. idx as nat + Size() as nat * len as nat], len as nat)

  method Pack_Seq_into_ByteSeq(value: seq<Integer>, linear inout packed: seq<byte>, idx: uint64)
    requires idx as nat + |value| * Size() as nat <= |old_packed|
    ensures |packed| == |old_packed|
    ensures forall i | 0 <= i < idx :: packed[i] == old_packed[i]
    ensures unpack_Seq(packed[idx..idx as nat + |value| * Size() as nat], |value|) == value
    ensures forall i | idx as nat + |value| * Size() as nat <= i < |packed| :: packed[i] == old_packed[i]
}

module NativePackedByte refines NativePackedInt{
  type Integer = byte
    
  function method Size() : uint64 { 1 }
    
  function {:opaque} unpack(s: seq<byte>) : Integer
  {
    s[0]
  }

  method {:extern} Unpack(packed: seq<byte>, idx: uint64) returns (i: Integer)
  method {:extern} Pack_into_ByteSeq(i: Integer, linear inout s: seq<byte>, idx: uint64)
  method {:extern} Unpack_Seq(packed: seq<byte>, idx: uint64, len: uint64) returns (unpacked: seq<Integer>)
  method {:extern} Pack_Seq_into_ByteSeq(value: seq<Integer>, linear inout packed: seq<byte>, idx: uint64)
}

module NativePackedUint32 refines NativePackedInt{
  type Integer = uint32

  function method Size() : uint64 { 4 }
    
  function {:opaque} unpack(s: seq<byte>) : Integer
  {
    (s[0] as uint32)
    + (s[1] as uint32 * 0x1_00)
    + (s[2] as uint32 * 0x1_00_00)
    + (s[3] as uint32 * 0x1_00_00_00)
  }

  method {:extern} Unpack(packed: seq<byte>, idx: uint64) returns (i: Integer)
  method {:extern} Pack_into_ByteSeq(i: Integer, linear inout s: seq<byte>, idx: uint64)
  method {:extern} Unpack_Seq(packed: seq<byte>, idx: uint64, len: uint64) returns (unpacked: seq<Integer>)
  method {:extern} Pack_Seq_into_ByteSeq(value: seq<Integer>, linear inout packed: seq<byte>, idx: uint64)
}

module NativePackedUint64 refines NativePackedInt{
  type Integer = uint64

  function method Size() : uint64 { 8 }
    
  function {:opaque} unpack(s: seq<byte>) : Integer
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

  method {:extern} Unpack(packed: seq<byte>, idx: uint64) returns (i: Integer)
  method {:extern} Pack_into_ByteSeq(i: Integer, linear inout s: seq<byte>, idx: uint64)
  method {:extern} Unpack_Seq(packed: seq<byte>, idx: uint64, len: uint64) returns (unpacked: seq<Integer>)
  method {:extern} Pack_Seq_into_ByteSeq(value: seq<Integer>, linear inout packed: seq<byte>, idx: uint64)
}

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

  // method {:extern "NativePackedInts_Compile", 
  //     "Pack__LittleEndian__Uint32__into__Seq"} 
  // Pack_LittleEndian_Uint32_into_Seq(i: uint32, linear inout s: seq<byte>, idx: uint64)
  // requires 0 <= idx
  // requires idx as int + 4 <= |old_s|
  // requires |old_s| < 0x1_0000_0000_0000_0000
  // ensures |s| == |old_s|
  // ensures forall j | 0 <= j < idx :: s[j] == old_s[j]
  // ensures unpack_LittleEndian_Uint32(s[idx .. idx + 4]) == i
  // ensures forall j | idx as int + 4 <= j < |s| :: s[j] == old_s[j]

  // method {:extern "NativePackedInts_Compile", 
  //     "Pack__LittleEndian__Uint64__into__Seq"} 
  // Pack_LittleEndian_Uint64_into_Seq(i: uint64, linear inout s: seq<byte>, idx: uint64)
  // requires 0 <= idx
  // requires idx as int + 8 <= |old_s|
  // requires |old_s| < 0x1_0000_0000_0000_0000
  // ensures |s| == |old_s|
  // ensures forall j | 0 <= j < idx :: s[j] == old_s[j]
  // ensures unpack_LittleEndian_Uint64(s[idx .. idx + 8]) == i
  // ensures forall j | idx as int + 8 <= j < |s| :: s[j] == old_s[j]

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
