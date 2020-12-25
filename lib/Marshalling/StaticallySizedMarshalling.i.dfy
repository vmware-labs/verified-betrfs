include "../Lang/NativeTypes.s.dfy"
include "../Lang/System/PackedInts.s.dfy"
include "../Base/Option.s.dfy"

module StaticallySizedMarshalling {
  import opened NativeTypes
  import opened NativePackedInts
  import opened Options
  
  datatype StaticallySizedGrammar =
    | SSGUint32
    | SSGUint64
    | SSGByteArray(len: nat)
    | SSGUint32Array(len: nat)
    | SSGUint64Array(len: nat)
    | SSGTuple(t: seq<StaticallySizedGrammar>)
    | SSGTaggedUnion(cases: seq<StaticallySizedGrammar>)
    | SSGPadded(size: nat, delt: DynamicallySizedGrammar)   // size: max size in bytes
    
  datatype DynamicallySizedGrammar =
    | GByteArray
    | GUint32Array
    | GUint64Array
    | GArray(elt:DynamicallySizedGrammar)
    | GSSArray(selt: StaticallySizedGrammar)
    | GTuple(t:seq<DynamicallySizedGrammar>)
    | GTaggedUnion(cases:seq<DynamicallySizedGrammar>)

  datatype StaticallySizedValue = 
    | SSVUint32(v:uint32)
    | SSVUint64(u:uint64)
    | SSVArray(a:seq<StaticallySizedValue>)
    | SSVTuple(t:seq<StaticallySizedValue>)
    | SSVByteArray(b:seq<byte>)
    | SSVUint32Array(va:seq<uint32>)
    | SSVUint64Array(ua:seq<uint64>)
    | SSVCase(c:uint64, casev:StaticallySizedValue)
    | SSVPadded(size: uint64, padv:DynamicallySizedValue)

  datatype DynamicallySizedValue =
    | StaticallySizedValue(v: StaticallySizedValue)
    | VArray(a:seq<DynamicallySizedValue>)
    | VSSArray(sa:seq<StaticallySizedValue>)
    | VTuple(t:seq<DynamicallySizedValue>)
    | VByteArray(b:seq<byte>)
    | VUint32Array(va:seq<uint32>)
    | VUint64Array(ua:seq<uint64>)
    | VCase(c:uint64, val:DynamicallySizedValue)

  function SizeOfStaticallySizedGrammarSeq(grammars: seq<StaticallySizedGrammar>) : nat
  {
    if |grammars| == 0 then 0
    else SizeOfStaticallySizedGrammarSeq(grammars[..|grammars|-1]) + SizeOfStaticallySizedGrammar(grammars[|grammars|-1])
  }

  function MaxStaticallySizedGrammar(grammars: seq<StaticallySizedGrammar>) : nat
  {
    if |grammars| == 0 then 0
    else
      var prefixMax := SizeOfStaticallySizedGrammarSeq(grammars[..|grammars|-1]);
      var last := SizeOfStaticallySizedGrammar(grammars[|grammars|-1]);
      if prefixMax < last then last
      else prefixMax
  }

  function SizeOfStaticallySizedGrammar(grammar: StaticallySizedGrammar) : nat
  {
    match grammar
      case SSGUint32 => 4
      case SSGUint64 => 8
      case SSGByteArray(len)   => len
      case SSGUint32Array(len) => 4 * len
      case SSGUint64Array(len) => 8 * len
      case SSGTuple(t) =>  SizeOfStaticallySizedGrammarSeq(t)
      case SSGTaggedUnion(cases) => MaxStaticallySizedGrammar(cases)
      case SSGPadded(size, delt) => size
  }

  function SizeOfVSeq(vals: seq<DynamicallySizedValue>, grammar: DynamicallySizedGrammar) : nat
    requires forall i | 0 <= i < |vals| :: ValInGrammar(vals[i], grammar)
    decreases grammar, vals, 1
  {
    if |vals| == 0 then 0
    else SizeOfVSeq(vals[..|vals|-1], grammar) + SizeOfV(vals[|vals|-1], grammar)
  }

  function SizeOfVGSeq(vals: seq<DynamicallySizedValue>, grammars: seq<DynamicallySizedGrammar>) : nat
    requires |vals| == |grammars|
    requires forall i | 0 <= i < |vals| :: ValInGrammar(vals[i], grammars[i])
    decreases grammars, vals, 1
  {
    if |vals| == 0 then 0
    else SizeOfVGSeq(vals[..|vals|-1], grammars[..|grammars|-1]) + SizeOfV(vals[|vals|-1], grammars[|grammars|-1])
  }

  function SizeOfV(val:DynamicallySizedValue, grammar: DynamicallySizedGrammar) : nat
    requires ValInGrammar(val, grammar)
    decreases grammar, val, 1
  {
    match grammar
      case GByteArray          => |val.b|
      case GUint32Array        => 4 * |val.va|
      case GUint64Array        => 8 * |val.ua|
      case GArray(elt)         => 8 + 8 * |val.a| + SizeOfVSeq(val.a, elt)
      case GSSArray(selt)      => |val.sa| * SizeOfStaticallySizedGrammar(selt)
      case GTuple(t)           => 8 * |t| + SizeOfVGSeq(val.t, t)
      case GTaggedUnion(cases) => 8 + SizeOfV(val.val, cases[val.c])
  }
  
  predicate StaticallySizedValInStaticallySizedGrammar(val:StaticallySizedValue, grammar:StaticallySizedGrammar)
    decreases grammar, val, 1
  {
    match grammar
      case SSGUint32 => val.SSVUint32?
      case SSGUint64 => val.SSVUint64?
      case SSGByteArray(len)   => val.SSVByteArray? && |val.b| == len
      case SSGUint32Array(len) => val.SSVUint32Array? && |val.va| == len
      case SSGUint64Array(len) => val.SSVUint64Array? && |val.ua| == len

      case SSGTuple(t) =>
        && val.SSVTuple?
        && |val.t| == |t|
        && forall i :: 0 <= i < |t| ==> StaticallySizedValInStaticallySizedGrammar(val.t[i], t[i])
        
      case SSGTaggedUnion(cases) =>
        && val.SSVCase?
        && (val.c as int) < |cases|
        && StaticallySizedValInStaticallySizedGrammar(val.casev, cases[val.c])
        
      case SSGPadded(size, delt) =>
        && val.SSVPadded?
        && ValInGrammar(val.padv, delt)
        && SizeOfV(val.padv, delt) <= size
  }

  predicate ValInGrammar(val:DynamicallySizedValue, grammar:DynamicallySizedGrammar)
    decreases grammar, val, 0
  {
    match grammar
      case GArray(elt) => val.VArray? && forall v :: v in val.a ==> ValInGrammar(v, elt)
      case GSSArray(selt) => val.VSSArray? && forall v :: v in val.sa ==> StaticallySizedValInStaticallySizedGrammar(v, selt)
      case GTuple(t) =>
        && val.VTuple?
        && |t| == |val.t|
        && forall i :: 0 <= i < |t| ==> ValInGrammar(val.t[i], t[i])
      case GByteArray => val.VByteArray?
      case GUint32Array => val.VUint32Array?
      case GUint64Array => val.VUint64Array?
      case GTaggedUnion(cases) =>
        && val.VCase?
        && (val.c as int) < |cases| &&
        ValInGrammar(val.val, cases[val.c])
  }

  function parse_Uint32(data:seq<byte>, offset: nat) : (Option<StaticallySizedValue>, nat)
    requires |data| < 0x1_0000_0000_0000_0000;
  {
    if offset + Uint32Size() as nat <= |data| then
      (Some(SSVUint32(unpack_LittleEndian_Uint32(data[offset..offset+Uint32Size() as nat]))), offset + Uint32Size() as nat)
    else
      (None, offset)
  }

  function parse_Uint64(data:seq<byte>, offset: nat) : (Option<StaticallySizedValue>, nat)
    requires |data| < 0x1_0000_0000_0000_0000;
  {
    if offset + Uint64Size() as nat <= |data| then
      (Some(SSVUint64(unpack_LittleEndian_Uint64(data[offset..offset+Uint64Size() as nat]))), offset + Uint64Size() as nat)
    else
      (None, offset)
  }

  method ParseUint32(data:seq<byte>, index:uint64) returns (value: Option<StaticallySizedValue>, rest_index:uint64)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires (index as int) <= |data|
    ensures (value, rest_index as nat) == parse_Uint32(data, index as nat)
  {
    if |data| as uint64 - index >= Uint32Size() {
      var result := Unpack_LittleEndian_Uint32(data, index);
      value := Some(SSVUint32(result));
      rest_index := index + Uint32Size();
    } else {
      value := None;
      rest_index := index;
    }
  }

  method ParseUint64(data:seq<byte>, index:uint64) returns (value: Option<StaticallySizedValue>, rest_index:uint64)
    requires |data| < 0x1_0000_0000_0000_0000;
    requires (index as int) <= |data|
    ensures (value, rest_index as nat) == parse_Uint64(data, index as nat)
  {
    if |data| as uint64 - index >= Uint64Size() {
      var result := Unpack_LittleEndian_Uint64(data, index);
      value := Some(SSVUint64(result));
      rest_index := index + Uint64Size();
    } else {
      value := None;
      rest_index := index;
    }
  }


  
}
