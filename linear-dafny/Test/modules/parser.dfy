// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Simplifying the example to use int instead of NativeTypes.byte makes the problem disappear
module NativeTypes {
  newtype{:nativeType "byte"} byte = i:int | 0 <= i < 0x100
}
abstract module NativePackedInt {
  import opened NativeTypes
  type Integer
  function unpack(s: seq<byte>) : Integer
}

module NativePackedUint32 refines NativePackedInt {
  type Integer = int
}

// Marshalling
abstract module Marshalling {
  import opened NativeTypes
  type UnmarshalledType
  function parse(data: seq<byte>) : UnmarshalledType
}

// Integer marshalling
module IntegerMarshalling(Int: NativePackedInt) refines Marshalling {
  type UnmarshalledType = Int.Integer
  function parse(data: seq<byte>) : UnmarshalledType
  {
    Int.unpack(data)
  }
}


// Sequence marshalling
abstract module SeqMarshalling(ElementMarshalling: Marshalling) refines Marshalling {
  type Element = ElementMarshalling.UnmarshalledType
  type UnmarshalledType = seq<Element>
}
abstract module UniformSizedElementSeqMarshallingCommon(elementMarshalling: Marshalling) refines SeqMarshalling(elementMarshalling) {
  function parse_prefix(data: seq<byte>) : (result: UnmarshalledType)
    ensures result == [ elementMarshalling.parse(data) ]
}
module IntegerSeqMarshalling(Int: NativePackedInt) refines UniformSizedElementSeqMarshallingCommon(IntegerMarshalling(Int)) {
}

// Works
module Uint32SeqMarshalling { //refines IntegerSeqMarshalling(NativePackedUint32) {
  import X = IntegerSeqMarshalling(NativePackedUint32)
}

// Creates a type mismatch, presumably due to _Compile issues
module Uint32SeqMarshalling2 refines IntegerSeqMarshalling(NativePackedUint32) {

}
