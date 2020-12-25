include "../Lang/NativeTypes.s.dfy"
include "../Lang/System/PackedInts.s.dfy"
//include "../Lang/LinearSequence.s.dfy"
include "../Base/Option.s.dfy"
include "../Base/mathematics.i.dfy"

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

abstract module IntegerSeqMarshalling refines SeqMarshalling {
  import ElementMarshalling = IntegerMarshalling
  import Int = ElementMarshalling.Int
    
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
    var dlen := |data| as uint64;
    olen := Some(dlen / Int.Size());
  }

  method Lengthable(data: mseq<byte>) returns (l: bool)
  {
    l := true;
  }
  
  method Length(data: mseq<byte>) returns (len: uint64)
  {
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
      ElementMarshalling.parse(data[idx * Int.Size()..idx * Int.Size() + Int.Size()]);
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
}

// FIXME: Can't instantiate these with current limitations of module
// system.

// module Uint32SeqMarshalling refines IntegerSeqMarshalling {
// }

// module Uint64SeqMarshalling refines IntegerSeqMarshalling {
//   import Int = NativePackedUint64
// }


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


