include "GenericMarshalling.i.dfy"

module MarshalledAccessors {
  import opened GenericMarshalling`Internal
  import opened NativeTypes
  import opened NativePackedInts
  import opened Sequences

  method Uint32ArrayLength(data: seq<byte>, start: uint64) returns (length: uint64)
    requires |data| < Uint64UpperBound()
    requires start as int <= |data|
    requires parse_Uint32Array(data[start..]).0.Some?
    ensures length as int == |parse_Uint32Array(data[start..]).0.value.va|
  {
    length := Unpack_LittleEndian_Uint64(data[start..], 0);
  }

  method Uint32ArraySize(data: seq<byte>, start: uint64) returns (size: uint64)
    requires |data| < Uint64UpperBound()
    requires start as int <= |data|
    requires parse_Uint32Array(data[start..]).0.Some?
    ensures size as int == SizeOfV(parse_Uint32Array(data[start..]).0.value)
  {
    var length := Uint32ArrayLength(data, start);
    size := 8 + 4 * length;
  }
  
  method Uint32ArrayElement(data: seq<byte>, start: uint64, i: uint64) returns (element: uint32)
    requires |data| < Uint64UpperBound()
    requires start as int <= |data|
    requires parse_Uint32Array(data[start..]).0.Some?
    requires i as int < |parse_Uint32Array(data[start..]).0.value.va|
    ensures element == parse_Uint32Array(data[start..]).0.value.va[i]
  {
    var idx := 8 + i * 4;
    element := Unpack_LittleEndian_Uint32(data, start + idx);

    ghost var len := |parse_Uint32Array(data[start..]).0.value.va|;
    
    calc {
      element;
      unpack_LittleEndian_Uint32(data[start + idx..start + idx + 4]);
      { lemma_seq_suffix_slice(data, start as int, idx as int, idx as int + 4); }
      unpack_LittleEndian_Uint32(data[start..][idx..idx + 4]);
      unpack_LittleEndian_Uint32(data[start..][8 + i * 4..8 + i * 4 + 4]);
      { lemma_seq_suffix_slice(data[start..], 8, i as int * 4, i as int * 4 + 4); }
      unpack_LittleEndian_Uint32(data[start..][8..][i * 4..i * 4 + 4]);
      { lemma_seq_extensionality_slice(data[start..][8..], data[start..][8..][..len*4], i as int * 4, i as int * 4 + 4); }
      unpack_LittleEndian_Uint32(data[start..][8..][..len*4][i * 4..i * 4 + 4]);
      unpack_LittleEndian_Uint32_Seq(data[start..][8..][0..4*len], len as int)[i];
      { lemma_seq_suffix_slice(data[start..], 8, 0, 4*len); }
      unpack_LittleEndian_Uint32_Seq(data[start..][8..8+4*len], len as int)[i];
      parse_Uint32Array(data[start..]).0.value.va[i];
    }
  }

  method ByteArraySlice(data: seq<byte>, start: uint64, from: uint64, to: uint64)
    returns (s: seq<byte>)
    requires |data| < Uint64UpperBound()
    requires start as int <= |data|
    requires parse_ByteArray(data[start..]).0.Some?
    requires from as int <= to as int <= |parse_ByteArray(data[start..]).0.value.b|
    ensures s == parse_ByteArray(data[start..]).0.value.b[from..to]
  {
    s := data[start + 8 + from..start + 8+ to];
  }    
}
