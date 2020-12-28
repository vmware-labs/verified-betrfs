include "../Lang/NativeTypes.s.dfy"
include "../Lang/System/PackedInts.s.dfy"
include "../Lang/LinearSequence.i.dfy"
include "../Base/Option.s.dfy"
include "../Base/mathematics.i.dfy"

/////////////////////////////////////////
// The most general marshalling interface
/////////////////////////////////////////

abstract module Marshalling {
  import opened NativeTypes
  import opened Options
  
  type UnmarshalledType

  // "mseq" == "machine seq"
  type mseq<T> = s : seq<T> | |s| < Uint64UpperBound()

  predicate parsable(data: mseq<byte>)

  function parse(data: mseq<byte>) : UnmarshalledType
    requires parsable(data)

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
    ensures parsable(data) <==> ovalue.Some?
    ensures parsable(data) ==> ovalue.value == parse(data)
    
  // FIXME: robj: Would like to provide this as default implementations,
  // but overriding in in refining modules gives an error about
  // assigning to p.
  method Parsable(data: mseq<byte>) returns (p: bool)
    ensures p == parsable(data)
  // {
  //   var ovalue := TryParse(data);
  //   p := ovalue.Some?;
  // }
  
  // FIXME: robj: Would like to provide this as default
  // implementations, but overriding in in refining modules gives an
  // error about assigning to p.
  method Parse(data: mseq<byte>) returns (value: UnmarshalledType)
    requires parsable(data)
    ensures value == parse(data)
  // {
  //   var ovalue := TryParse(data);
  //   value := ovalue.value;
  // }

  predicate marshallable(value: UnmarshalledType)
    
  function size(value: UnmarshalledType) : nat
    requires marshallable(value)

  method Size(value: UnmarshalledType) returns (sz: uint64)
    requires marshallable(value)
    requires size(value) < Uint64UpperBound()
    ensures sz as nat == size(value)

  // FIXME: robj: data should be linear inout doesn't work with module
  // refinement.
  method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
    returns (linear newdata: mseq<byte>, end: uint64)
    requires marshallable(value)
    requires start as nat + size(value) <= |data|
    ensures end as nat == start as nat + size(value)
    ensures |newdata| == |data|
    ensures forall i | 0 <= i < start :: newdata[i] == data[i]
    ensures forall i | end <= i < |newdata| as uint64 :: newdata[i] == data[i]
    ensures parsable(newdata[start..end])
    ensures parse(newdata[start..end]) == value
}

////////////////////////////////////////////////////
// Marshalling implementation for a packable integer
////////////////////////////////////////////////////

abstract module IntegerMarshalling refines Marshalling {
  import Int : NativePackedInt
    
  type UnmarshalledType = Int.Integer

  predicate parsable(data: mseq<byte>)
  {
    Int.Size() as nat <= |data|
  }

  function parse(data: mseq<byte>) : UnmarshalledType
  {
    Int.unpack(data[..Int.Size()])
  }
      
  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    if Int.Size() <= |data| as uint64 {
      var value := Int.Unpack(data, 0);
      ovalue := Some(value);
    } else {
      ovalue := None;
    }
  }

  method Parsable(data: mseq<byte>) returns (p: bool)
  {
    p := Int.Size() <= |data| as uint64;
  }
  
  method Parse(data: mseq<byte>) returns (value: UnmarshalledType)
  {
    value := Int.Unpack(data, 0);
  }

  predicate marshallable(value: UnmarshalledType) {
    true
  }
      
  function size(value: UnmarshalledType) : nat
  {
    Int.Size() as nat
  }
  
  method Size(value: UnmarshalledType) returns (sz: uint64)
  {
    sz := Int.Size();
  }
  
  method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
    returns (linear newdata: mseq<byte>, end: uint64)
  {
      newdata := data;
      Int.Pack_into_ByteSeq(value, inout newdata, start);
      end := start + Int.Size();
      assert newdata[start..end][..Int.Size()] == newdata[start..start + Int.Size()];
  }
}

module Uint32Marshalling refines IntegerMarshalling {
  import Int = NativePackedUint32
}

module Uint64Marshalling refines IntegerMarshalling {
  import Int = NativePackedUint64
}

//////////////////////////////////////////////////////////////////////
// Interface for marshalling sequences
//
// This adds support for querying the length of the sequence and
// getting the marshalled representation of an element of the sequence
// without having to parse the whole thing.
//////////////////////////////////////////////////////////////////////

abstract module SeqMarshalling refines Marshalling {
  import ElementMarshalling : Marshalling

  type Element = ElementMarshalling.UnmarshalledType
  type UnmarshalledType = mseq<Element>

  predicate lengthable(data: mseq<byte>)
    ensures parsable(data) ==> lengthable(data)
    
  method TryLength(data: mseq<byte>) returns (olen: Option<uint64>)
    ensures lengthable(data) <==> olen.Some?
    ensures parsable(data) ==> olen.value as nat == |parse(data)|

  method Lengthable(data: mseq<byte>) returns (l: bool)
    ensures l == lengthable(data)
    
  method Length(data: mseq<byte>) returns (len: uint64)
    requires lengthable(data)
    ensures parsable(data) ==> len as nat == |parse(data)|


  predicate gettable(data: mseq<byte>, idx: nat)
    ensures parsable(data) && idx < |parse(data)| ==> gettable(data, idx)
    
  method TryGet(data: mseq<byte>, idx: uint64) returns (oedata: Option<mseq<byte>>)
    ensures oedata.Some? <==> gettable(data, idx as nat)
    ensures parsable(data) && |parse(data)| <= idx as nat ==> oedata.None?
    ensures parsable(data) && idx as nat < |parse(data)| ==> ElementMarshalling.parsable(oedata.value)
    ensures parsable(data) && idx as nat < |parse(data)| ==> ElementMarshalling.parse(oedata.value) == parse(data)[idx]

  method Gettable(data: mseq<byte>, idx: uint64) returns (g: bool)
    ensures g == gettable(data, idx as nat)


  method Get(data: mseq<byte>, idx: uint64) returns (edata: mseq<byte>)
    requires gettable(data, idx as nat)
    ensures parsable(data) && idx as nat < |parse(data)| ==> ElementMarshalling.parsable(edata)
    ensures parsable(data) && idx as nat < |parse(data)| ==> ElementMarshalling.parse(edata) == parse(data)[idx]
}

/////////////////////////////////////////////////////////////////
// Implementation for marshalling a sequence of packable integers
//
// We could just use the UniformSized marshalling code further below,
// but that would marshall each integer one at a time, which would
// (presumably) be slower.
/////////////////////////////////////////////////////////////////

abstract module IntegerSeqMarshalling refines SeqMarshalling {
  import ElementMarshalling = IntegerMarshalling
  import Int = ElementMarshalling.Int
  import opened Mathematics
    
  predicate lengthable(data: mseq<byte>)
  {
    true
  }

  function length(data: mseq<byte>) : nat
  {
    |data| / Int.Size() as nat
  }
  
  method TryLength(data: mseq<byte>) returns (olen: Option<uint64>)
  {
    assert |data| / Int.Size() as nat <= |data|;
    olen := Some(|data| as uint64 / Int.Size());
  }

  method Lengthable(data: mseq<byte>) returns (l: bool)
  {
    l := true;
  }
  
  method Length(data: mseq<byte>) returns (len: uint64)
  {
    assert |data| / Int.Size() as nat <= |data|;
    len := |data| as uint64 / Int.Size();
  }

  predicate parsable(data: mseq<byte>)
  {
    true
  }

  function parse(data: mseq<byte>) : UnmarshalledType
  {
    var length := length(data);
    Int.unpack_Seq(data[..length * Int.Size() as nat], length)
  }

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var length := Length(data);
    var value := Int.Unpack_Seq(data, 0, length);
    assert |value| < Uint64UpperBound();
    ovalue := Some(value);
  }

  method Parsable(data: mseq<byte>) returns (p: bool)
  {
    p := true;
  }

  method Parse(data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var length := Length(data);
    value := Int.Unpack_Seq(data, 0, length);
  }
  
  predicate gettable(data: mseq<byte>, idx: nat)
  {
    idx < length(data)
  }

  lemma GetCorrect(data: mseq<byte>, idx: uint64)
    requires idx as nat < length(data)
    ensures idx as nat * Int.Size() as nat + Int.Size() as nat <= |data|
    ensures ElementMarshalling.parse(data[idx * Int.Size()..idx * Int.Size() + Int.Size()]) == parse(data)[idx]
  {
    //assert idx as nat + 1 <= length(data);
    assert (idx as nat + 1) * Int.Size() as nat <= length(data) * Int.Size() as nat;
    assert length(data) * Int.Size() as nat <= (|data| / Int.Size() as nat) * Int.Size() as nat;
    calc {
      ElementMarshalling.parse(data[idx * Int.Size()..idx as nat * Int.Size() as nat + Int.Size() as nat]);
      Int.unpack(data[idx * Int.Size()..(idx + 1) * Int.Size()][..Int.Size()]);
      Int.unpack(data[idx * Int.Size()..(idx + 1) * Int.Size()][0..Int.Size()]);
      { assert data[idx * Int.Size()..(idx + 1) * Int.Size()][..Int.Size()] == data[idx * Int.Size()..idx * Int.Size() + Int.Size()]; }
      Int.unpack(data[idx * Int.Size()..idx * Int.Size() + Int.Size()]);
      Int.unpack(data[idx as nat * Int.Size() as nat.. (idx as nat + 1) * Int.Size() as nat]);
      { assert data[..length(data) * Int.Size() as nat][idx as nat * Int.Size() as nat.. (idx as nat + 1) * Int.Size() as nat] == data[idx as nat * Int.Size() as nat.. (idx as nat + 1) * Int.Size() as nat]; }
      Int.unpack(data[..length(data) * Int.Size() as nat][idx as nat * Int.Size() as nat.. (idx as nat + 1) * Int.Size() as nat]);
      Int.unpack_Seq(data[..length(data) * Int.Size() as nat], length(data))[idx];
      parse(data)[idx];
    }
  }
  
  method TryGet(data: mseq<byte>, idx: uint64) returns (oedata: Option<mseq<byte>>)
  {
    var len := Length(data);
    if idx < len {
      GetCorrect(data, idx);
      oedata := Some(data[idx * Int.Size()..idx * Int.Size() + Int.Size()]);
    } else {
      oedata := None;
    }
  }
  
  method Gettable(data: mseq<byte>, idx: uint64) returns (g: bool)
  {
    var len := Length(data);
    g := idx < len;
  }

  method Get(data: mseq<byte>, idx: uint64) returns (edata: mseq<byte>)
  {
    var len := Length(data);
    if idx < len {
      GetCorrect(data, idx);
      edata := data[idx * Int.Size()..idx * Int.Size() + Int.Size()];
    } else {
      edata := [];
    }
  }

  method FastGet(data: mseq<byte>, idx: uint64) returns (element: Element)
    requires idx as nat < length(data)
    ensures element == parse(data)[idx]
  {
    GetCorrect(data, idx);
    element := Int.Unpack(data, idx * Int.Size());
    assert data[idx * Int.Size()..idx * Int.Size() + Int.Size()] == data[idx * Int.Size()..idx * Int.Size() + Int.Size()][..Int.Size()];
  }

  predicate marshallable(value: UnmarshalledType) {
    true
  }

  function size(value: UnmarshalledType) : nat {
    |value| * Int.Size() as nat
  }

  method Size(value: UnmarshalledType) returns (sz: uint64) {
    sz := |value| as uint64 * Int.Size();
  }

  method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
    returns (linear newdata: mseq<byte>, end: uint64)
  {
    newdata := data;
    Int.Pack_Seq_into_ByteSeq(value, inout newdata, start);
    var sz := Size(value);
    end := start + sz;

    MulDivCancel(|value|, Int.Size() as nat);
    ghost var ndata := newdata[start..end];
    ghost var nlength := length(ndata);
    assert newdata[start..end][..nlength * Int.Size() as nat] == newdata[start..start as nat + nlength * Int.Size() as nat];
  }
}

// FIXME: Can't instantiate these with current limitations of module
// system.

// module Uint32SeqMarshalling refines IntegerSeqMarshalling {
// }

// module Uint64SeqMarshalling refines IntegerSeqMarshalling {
//   import Int = NativePackedUint64
// }

//////////////////////////////////////////////////////////////////////
// Implementation of marshalling a sequence of items that all have the
// same marshalled size.
//////////////////////////////////////////////////////////////////////

abstract module UniformSizedElementSeqMarshalling refines SeqMarshalling {
  import opened Mathematics

  function method UniformSize() : uint64
    ensures 0 < UniformSize()

  predicate lengthable(data: mseq<byte>)
  {
    true
  }

  function length(data: mseq<byte>) : nat
  {
    |data| / UniformSize() as nat
  }

  method TryLength(data: mseq<byte>) returns (olen: Option<uint64>)
  {
    assert |data| / UniformSize() as nat <= |data|;
    olen := Some(|data| as uint64 / UniformSize());
  }

  method Lengthable(data: mseq<byte>) returns (l: bool)
  {
    l := true;
  }

  method Length(data: mseq<byte>) returns (len: uint64)
    ensures len as nat == length(data)
  {
    assert |data| / UniformSize() as nat <= |data|;
    len := |data| as uint64 / UniformSize();
  }

  function method ElementData(data: mseq<byte>, idx: uint64) : mseq<byte>
    requires idx as nat < length(data)
  {
    DivMulOrder(length(data), UniformSize() as nat);
    assert (idx as nat + 1) * UniformSize() as nat <= |data|;
    assert (idx as nat + 1) * UniformSize() as nat == idx as nat * UniformSize() as nat + UniformSize() as nat;
    data[idx * UniformSize()..idx * UniformSize() + UniformSize()]
  }

  predicate parsable(data: mseq<byte>) {
    forall idx | 0 <= idx < length(data) :: ElementMarshalling.parsable(ElementData(data, idx as uint64))
  }

  function parse_prefix(data: mseq<byte>, len: nat) : (result: UnmarshalledType)
    requires parsable(data)
    requires len <= length(data)
    ensures |result| == len
    ensures forall i | 0 <= i < len :: result[i] == ElementMarshalling.parse(ElementData(data, i as uint64))
  {
    if len == 0 then
      []
    else
      var prefix := parse_prefix(data, len - 1);
      var last := ElementMarshalling.parse(ElementData(data, len as uint64 - 1));
      prefix + [last]
  }

  function parse(data: mseq<byte>) : (result: UnmarshalledType)
  {
    var len := length(data);
    parse_prefix(data, len)
  }

  predicate gettable(data: mseq<byte>, idx: nat)
  {
    idx < length(data)
  }
  
  method TryGet(data: mseq<byte>, idx: uint64) returns (oedata: Option<mseq<byte>>)
  {
    var len := Length(data);
    if idx < len {
      oedata := Some(ElementData(data, idx));
    } else {
      oedata := None;
    }
  }

  method Gettable(data: mseq<byte>, idx: uint64) returns (g: bool)
  {
    var len := Length(data);
    g := idx < len;
  }

  method Get(data: mseq<byte>, idx: uint64) returns (edata: mseq<byte>)
  {
    edata := ElementData(data, idx);
  }


  predicate marshallable(value: UnmarshalledType)
  {
    && (forall i | 0 <= i < |value| :: ElementMarshalling.marshallable(value[i]))
    && (forall i | 0 <= i < |value| :: ElementMarshalling.size(value[i]) == UniformSize() as nat)
  }

  lemma marshallable_prefix(value: UnmarshalledType, len: nat)
    requires marshallable(value)
    requires 0 <= len <= |value|
    ensures marshallable(value[..len])
  {
  }

  function size(value: UnmarshalledType) : nat
  {
    |value| * UniformSize() as nat
  }

  method Size(value: UnmarshalledType) returns (sz: uint64)
  {
    sz := |value| as uint64 * UniformSize();
  }

  lemma parsing_extend(data: mseq<byte>, edata: mseq<byte>)
    requires parsable(data)
    requires |data| == length(data) * UniformSize() as nat
    requires ElementMarshalling.parsable(edata)
    requires |edata| == UniformSize() as nat
    ensures parsable(data + edata)
    ensures parse(data + edata) == parse(data) + [ ElementMarshalling.parse(edata) ]
  {
    var extension := data + edata;
    calc {
      length(extension);
      |extension| / UniformSize() as nat;
      (|data| + UniformSize() as nat) / UniformSize() as nat;
      |data| / UniformSize() as nat + UniformSize() as nat / UniformSize() as nat;
      |data| / UniformSize() as nat + 1;
      length(data) + 1;
    }
    forall idx | 0 <= idx < length(extension)
      ensures ElementMarshalling.parsable(ElementData(extension, idx as uint64))
      ensures idx < length(data) ==> parse(extension)[idx] == parse(data)[idx]
      ensures idx == length(data) ==> parse(extension)[idx] == ElementMarshalling.parse(edata)
    {
      if idx < length(data) {
        assert (idx + 1) * UniformSize() as nat <= length(data) * UniformSize() as nat;
        assert ElementData(extension, idx as uint64) == ElementData(data, idx as uint64);
      } else {
        assert ElementData(extension, idx as uint64) == edata;
      }
    }
  }
  
  method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
    returns (linear newdata: mseq<byte>, end: uint64)
  {
    newdata := data;
    var i: uint64 := 0;
    end := start;
    while i < |value| as uint64
      invariant i <= |value| as uint64
      invariant |newdata| == |data|
      invariant end as nat == start as nat + size(value[..i])
      invariant forall j | 0 <= j < start :: newdata[j] == data[j]
      invariant forall j | end as nat <= j < |data| :: newdata[j] == data[j]
      invariant parsable(newdata[start..end])
      invariant parse(newdata[start..end]) == value[..i]
    {
      ghost var oldend := end;
      ghost var olddata := newdata[start..end];
      assert i as nat + 1 <= |value|;
      assert start as nat + (i as nat + 1) * UniformSize() as nat <= start as nat + |value| * UniformSize() as nat;

      newdata, end := ElementMarshalling.Marshall(value[i], newdata, end);
      i := i + 1;

      assert newdata[start..oldend] == olddata;
      parsing_extend(newdata[start..oldend], newdata[oldend..end]);
      assert newdata[start..end] == newdata[start..oldend] + newdata[oldend..end];
      assert value[..i] == value[..i-1] + [ value[i-1] ];
    }
    assert value == value[..|value|];
  }
}

////////////////////////////////////////////////////////
// Interface for appending items to marshalled sequences
////////////////////////////////////////////////////////

abstract module AppendableSeqMarshalling refines SeqMarshalling {
  predicate appendable(data: mseq<byte>, newItemSize: nat)

  method Appendable(data: mseq<byte>, newItemSize: uint64) returns (app: bool)
    ensures app == appendable(data, newItemSize as nat)

  method Append(elt: Element, linear data: mseq<byte>, start: uint64, end: uint64)
    returns (linear newdata: mseq<byte>)
    requires ElementMarshalling.marshallable(elt)
    requires start as nat <= end as nat <= |data| 
    requires appendable(data[start..end], ElementMarshalling.size(elt))
    ensures |newdata| == |data|
    ensures forall i | 0 <= i < start :: newdata[i] == data[i]
    ensures forall i | end as nat <= i < |newdata| :: newdata[i] == data[i]
    ensures parsable(data) ==> parsable(newdata)
    ensures parsable(data) ==> parse(newdata) == parse(data) + [ elt ]
}

abstract module AppendableIntegerSeqMarshalling refines AppendableSeqMarshalling {
  import ISM = IntegerSeqMarshalling
  import ElementMarshalling = ISM.ElementMarshalling
  import Int = ElementMarshalling.Int
  import LengthMarshalling : IntegerMarshalling
  import LengthInt = LengthMarshalling.Int
  import opened Mathematics
  import opened LinearSequence_s
  import opened LinearSequence_i
  
  // We put this in an internal helper function so we can use it in the
  // definition of parsable (and hence parse) without causing a
  // recursion problem.
  predicate lengthable'(data: mseq<byte>) {
    && LengthInt.Size() as nat <= |data|
    && LengthInt.fitsInUint64(LengthMarshalling.parse(data[..LengthInt.Size()]))
  }

  function length(data: mseq<byte>) : nat
    requires lengthable'(data)
  {
    LengthInt.toInt(LengthMarshalling.parse(data[..LengthInt.Size()]))
  }

  predicate parsable(data: mseq<byte>) {
    && lengthable'(data)
    && var len := length(data);
    && LengthInt.Size() as nat + len * Int.Size() as nat <= |data|
  }

  function parse(data: mseq<byte>) : UnmarshalledType {
    var len := length(data);
    ISM.parse(data[LengthInt.Size()..LengthInt.Size() as nat + len * Int.Size() as nat])
  }

  lemma parse_length(data: mseq<byte>)
    requires parsable(data)
    ensures |parse(data)| == length(data)
  {
    MulDivCancel(length(data), Int.Size() as nat);
  }
  
  predicate lengthable(data: mseq<byte>) {
    lengthable'(data)
  }
  
  method TryLength(data: mseq<byte>) returns (olen: Option<uint64>)
    ensures olen.Some? ==> olen.value as nat == length(data)
  {
    if LengthInt.Size() <= |data| as uint64 {
      var len := LengthMarshalling.Parse(data[..LengthInt.Size()]);
      if LengthInt.fitsInUint64(len) {
        olen := Some(LengthInt.toUint64(len));
        if parsable(data) {
          parse_length(data);
        }
      } else {
        olen := None;
      }
    } else {
      olen := None;
    }
  }

  method Lengthable(data: mseq<byte>) returns (l: bool) {
    if LengthInt.Size() <= |data| as uint64 {
      var len := LengthMarshalling.Parse(data[..LengthInt.Size()]);
      l := LengthInt.fitsInUint64(len);
    } else {
      l := false;
    }
  }

  method Length(data: mseq<byte>) returns (len: uint64)
    ensures len as nat == length(data)
  {
    var ilen := LengthMarshalling.Parse(data[..LengthInt.Size()]);
    len := LengthInt.toUint64(ilen);
    if parsable(data) {
      parse_length(data);
    }
  }

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>) {
    var olen := TryLength(data);
    if olen == None {
      return None;
    }
    var len := olen.value;
    InequalityMoveDivisor(len as nat, |data| - LengthInt.Size() as nat, Int.Size() as nat);
    if len <= (|data| as uint64 - LengthInt.Size()) / Int.Size() {
      var sdata := data[LengthInt.Size()..LengthInt.Size() + len * Int.Size()];
      var parsed := ISM.Parse(sdata);
      ovalue := Some(parsed);
    } else {
      return None;
    }
  }

  method Parsable(data: mseq<byte>) returns (p: bool) {
    var olen := TryLength(data);
    if olen == None {
      return false;
    }
    var len := olen.value;
    InequalityMoveDivisor(len as nat, |data| - LengthInt.Size() as nat, Int.Size() as nat);
    return len <= (|data| as uint64 - LengthInt.Size()) / Int.Size();
  }

  method Parse(data: mseq<byte>) returns (value: UnmarshalledType) {
    var len := Length(data);
    var sdata := data[LengthInt.Size()..LengthInt.Size() + len * Int.Size()];
    value := ISM.Parse(sdata);
  }

  predicate gettable(data: mseq<byte>, idx: nat) {
    && parsable(data)
    && idx < |parse(data)|
  }

  method TryGet(data: mseq<byte>, idx: uint64) returns (oedata: Option<mseq<byte>>) {
    var olen := TryLength(data);
    if olen == None {
      return None;
    }
    var len := olen.value;
    InequalityMoveDivisor(len as nat, |data| - LengthInt.Size() as nat, Int.Size() as nat);
    if len <= (|data| as uint64 - LengthInt.Size()) / Int.Size() {
      var sdata := data[LengthInt.Size()..LengthInt.Size() + len * Int.Size()];
      oedata := ISM.TryGet(sdata, idx);
    } else {
      return None;
    }
  }

  predicate appendable(data: mseq<byte>, newItemSize: nat) {
    && newItemSize == Int.Size() as nat
    && lengthable(data)
    && var len := length(data);
    && var maxlen := ISM.length(data[LengthInt.Size()..]);
    len < maxlen
  }

  method Appendable(data: mseq<byte>, newItemSize: uint64) returns (app: bool) {
    var olen := TryLength(data);
    if olen == None || newItemSize != Int.Size() {
      return false;
    }
    var len := olen.value;
    var sdata := data[LengthInt.Size()..];
    var maxlen := ISM.Length(sdata);
    return len < maxlen;
  }

  // Ugh
  method SharedLength(shared data: mseq<byte>, start: uint64, end: uint64) returns (len: uint64)
    requires start as nat <= end as nat <= |data|
    requires lengthable(data[start..end])
    ensures parsable(data[start..end]) ==> len as nat == |parse(data[start..end])|
  {
    linear var linear_marshalled_length := AllocAndCopy(data, start, start + LengthInt.Size());
    var marshalled_length := seq_unleash(linear_marshalled_length);
    var ilen := LengthInt.Unpack(marshalled_length, 0);
    len := LengthInt.toUint64(ilen);
  }
  
  method Append(elt: Element, linear data: mseq<byte>, start: uint64, end: uint64)
    returns (linear newdata: mseq<byte>)
  {
    var len := SharedLength(data, start, end);
    var newend;
    newdata, newend := ElementMarshalling.Marshall(elt, data, start + LengthInt.Size() + len * Int.Size());
    assume false;
    len := len + 1;
    var ilen: LengthMarshalling.UnmarshalledType := LengthInt.fromUint64(len);
    newdata, newend := LengthMarshalling.Marshall(ilen, newdata, start);
  }
}

//////////////////////////////////////////////////////////////////////
// Implementation of marshalling a general sequence of items
//////////////////////////////////////////////////////////////////////

abstract module VariableSizedElementSeqMarshalling refines SeqMarshalling {
  import LengthMarshalling : IntegerMarshalling
  import BoundarySeqMarshalling : IntegerSeqMarshalling

  // INTERNAL FUNCTIONS
  
  function sizeOfLengthField() : nat {
    LengthMarshalling.Int.Size() as nat
  }

  predicate lengthable'(data: mseq<byte>)
  {
    && sizeOfLengthField() <= |data|
    && 0 <= LengthMarshalling.Int.toInt(LengthMarshalling.parse(data[..sizeOfLengthField()]))
  }

  function length'(data: mseq<byte>) : nat
    requires lengthable'(data)
  {
    LengthMarshalling.Int.toInt(LengthMarshalling.parse(data[..sizeOfLengthField()]))
  }

  datatype Structure = Structure(boundaries: mseq<BoundarySeqMarshalling.Int.Integer>, elements: mseq<byte>)

  function sizeOfTable(len: nat) : nat {
    len * BoundarySeqMarshalling.Int.Size() as nat
  }
  
  predicate tableable(data: mseq<byte>) {
    && lengthable'(data)
    && var len := length'(data);
    && sizeOfLengthField() + sizeOfTable(len) <= |data|
  }

  function tabledata(data: mseq<byte>) : seq<byte>
    requires tableable(data)
  {
    var len := length'(data);
    data[sizeOfLengthField()..sizeOfLengthField() + sizeOfTable(len)]
  }

  function table(data: mseq<byte>) : BoundarySeqMarshalling.UnmarshalledType
    requires tableable(data)
  {
    var td := tabledata(data);
    BoundarySeqMarshalling.parse(td)
  }

  function elementsData(data: mseq<byte>) : mseq<byte>
    requires tableable(data)
  {
    var len := length'(data);
    data[sizeOfLengthField()..]
  }
  
  function partialParse(data: mseq<byte>) : (result: Structure)
    requires tableable(data)
  {
    Structure(table(data), elementsData(data))
  }

  predicate structGettable(struct: Structure, idx: nat) {
    && idx < |struct.boundaries|
    && var start := BoundarySeqMarshalling.Int.toInt(struct.boundaries[idx]);
    && var end := if idx == 0 then |struct.elements| else BoundarySeqMarshalling.Int.toInt(struct.boundaries[idx-1]);
    && 0 <= start <= end <= |struct.elements|
  }

  function structGet(struct: Structure, idx: nat) : mseq<byte>
    requires structGettable(struct, idx)
  {
    var start := BoundarySeqMarshalling.Int.toInt(struct.boundaries[idx]);
    var end := if idx == 0 then |struct.elements| else BoundarySeqMarshalling.Int.toInt(struct.boundaries[idx-1]);
    struct.elements[start..end]
  }
  
  // function get(data: mseq<byte>, idx: nat) : mseq<byte>
  //   requires gettable(data, idx)
  // {
  //   structGet(partialParse(data), idx)
  // }
  
//   method TryGet(data: mseq<byte>, idx: uint64) returns (oedata: Option<mseq<byte>>)
//   {
//     var ostruct := PartialParse(data);
//     if ostruct == None || |ostruct.value.boundaries| as uint64 <= idx {
//       return None;
//     }
//     var struct := ostruct.value;
    
//     var start := BoundarySeqMarshalling.Int.toUint64(struct.boundaries[idx]);
//     var end := |struct.elements| as uint64;
//     if 0 < idx {
//       end := BoundarySeqMarshalling.Int.toUint64(struct.boundaries[idx]);
//     }

//     if start <= end <= |struct.elements| as uint64 {
//       oedata := Some(struct.elements[start..end]);
//     } else {
//       oedata := None;
//     }

//   }

//   method Gettable(data: mseq<byte>, idx: uint64) returns (g: bool)
//   {
//     var oedata := TryGet(data, idx);
//     return oedata.Some?;
//   }

//   method Get(data: mseq<byte>, idx: uint64) returns (edata: mseq<byte>)
//   {
//     var oedata := TryGet(data, idx);
//     return oedata.value;
//   }

  predicate structParsable(struct: Structure) {
    && (forall i | 0 <= i < |struct.boundaries| :: structGettable(struct, i))
    && (forall i | 0 <= i < |struct.boundaries| :: ElementMarshalling.parsable(structGet(struct, i)))
  }

  function structParse(struct: Structure, prefixLen: nat) : mseq<Element>
    requires prefixLen <= |struct.boundaries|
    requires structParsable(struct)
  {
    if prefixLen == 0 then
      []
    else
      structParse(struct, prefixLen - 1) + [ ElementMarshalling.parse(structGet(struct, prefixLen - 1)) ]
  }

  predicate parsable(data: mseq<byte>) {
    && tableable(data)
    && var struct := partialParse(data);
    && structParsable(struct)
  }
  
  function parse(data: mseq<byte>) : UnmarshalledType {
    var struct := partialParse(data);
    structParse(struct, |struct.boundaries|)
  }

//   method PartialParse(data: mseq<byte>) returns (oresult : Option<Structure>)
//     ensures oresult.Some? <==> tableable(data)
//     ensures tableable(data) ==> oresult.value == partialParse(data)
//   {
//     var olen := TryLength(data);
//     if olen == None {
//       return None;
//     }
//     var len := olen.value;
    
//     var tbdata := data[LengthMarshalling.Int.Size()..LengthMarshalling.Int.Size() + len * BoundarySeqMarshalling.Int.Size()];
//     var table := BoundarySeqMarshalling.Parse(tbdata);
//     var esdata := data[LengthMarshalling.Int.Size()..];
//     oresult := Some(Structure(table, esdata));
//   }

  
//   method TryLength(data: mseq<byte>) returns (olen: Option<uint64>)
//   {
//     if LengthMarshalling.Int.Size() <= |data| as uint64 {
//       var l := LengthMarshalling.Parse(data[..LengthMarshalling.Int.Size()]);
//       olen := Some(LengthMarshalling.Int.toUint64(l));
//     } else {
//       olen := None;
//     }
//   }

//   method Lengthable(data: mseq<byte>) returns (l: bool)
//   {
//     l := LengthMarshalling.Int.Size() <= |data| as uint64;
//   }

//   method Length(data: mseq<byte>) returns (len: uint64)
//     ensures len as nat == length(data)
//   {
//     var l := LengthMarshalling.Parse(data[..LengthMarshalling.Int.Size()]);
//     len := LengthMarshalling.Int.toUint64(l);
//   }

    
//   predicate gettable(data: mseq<byte>, idx: nat)
//   {
//     && tableable(data)
//     && var struct := partialParse(data);
//     && structGettable(struct, idx)
//   }

}
