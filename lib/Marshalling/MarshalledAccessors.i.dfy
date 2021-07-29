include "../Lang/NativeTypes.s.dfy"
include "../Lang/System/PackedInts.s.dfy"
include "../Lang/LinearSequence.i.dfy"
include "../Base/Option.s.dfy"
include "../Base/mathematics.i.dfy"
include "../Base/sequences.i.dfy"
include "Math.i.dfy"
include "NLarith.i.dfy"

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

abstract module IntegerMarshalling(Int: NativePackedInt) refines Marshalling {
  import opened LinearSequence_s

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
      var value := Int.Cast(data, 0);
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
    value := Int.Cast(data, 0);
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

module Uint32Marshalling refines IntegerMarshalling(NativePackedUint32) {
}

module Uint64Marshalling refines IntegerMarshalling(NativePackedUint64) {
}

//////////////////////////////////////////////////////////////////////
// Interface for marshalling sequences
//
// This adds support for querying the length of the sequence and
// getting the marshalled representation of an element of the sequence
// without having to parse the whole thing.
//////////////////////////////////////////////////////////////////////

abstract module SeqMarshalling(ElementMarshalling: Marshalling) refines Marshalling {
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

//////////////////////////////////////////////////////////////////////
// Common parts of implementation of marshalling a sequence of items
// that all have the same marshalled size.
//
// We omit the actual parsing and marshalling implementations so that
// we can use the optimized integer packing code.
//////////////////////////////////////////////////////////////////////

abstract module UniformSizedElementSeqMarshallingCommon(elementMarshalling: Marshalling)
refines SeqMarshalling(elementMarshalling) {
  import opened Mathematics
  import opened LinearSequence_i
  import opened LinearSequence_s
  import Seq = Sequences
  import opened Math
  import NLarith

  function method UniformSize() : uint64
    ensures 0 < UniformSize()

  predicate lengthable(data: mseq<byte>)
  {
    true
  }

  function length(data: mseq<byte>) : nat
    ensures length(data) <=  length(data) * UniformSize() as nat <= |data|
  {
    NLarith.DivLe(|data|, UniformSize() as nat);
    DivMulOrder(|data|, UniformSize() as nat);
    assert (|data| / UniformSize() as nat) * 1 == |data| / UniformSize() as nat;
    if 1 < UniformSize() then
      PosMulPreservesOrder(1, UniformSize() as nat, |data| / UniformSize() as nat);
      |data| / UniformSize() as nat
    else 
      |data| / UniformSize() as nat
  }

  method TryLength(data: mseq<byte>) returns (olen: Option<uint64>)
  {
    NLarith.DivLe(|data|, UniformSize() as nat);
    olen := Some(|data| as uint64 / UniformSize());
  }

  method Lengthable(data: mseq<byte>) returns (l: bool)
  {
    l := true;
  }

  method Length(data: mseq<byte>) returns (len: uint64)
    ensures len as nat == length(data)
  {
    NLarith.DivLe(|data|, UniformSize() as nat);
    len := |data| as uint64 / UniformSize();
  }

  lemma index_bounds_facts(data: mseq<byte>, idx: nat)
    requires idx < length(data)
    ensures 0 <= idx * UniformSize() as nat < idx * UniformSize() as nat + UniformSize() as nat == (idx + 1) * UniformSize() as nat <= |data|
  {
    NatMulNatIsNat(idx, UniformSize() as nat);
    PosMulPreservesOrder(idx, idx + 1, UniformSize() as nat);
    NLarith.DistributeLeft(idx, 1, UniformSize() as nat);
    if idx + 1 < length(data) {
      PosMulPreservesOrder(idx + 1, length(data), UniformSize() as nat);
    }
  }

  function method ElementData(data: mseq<byte>, idx: uint64) : mseq<byte>
    requires idx as nat < length(data)
    ensures |ElementData(data, idx)| == UniformSize() as nat
  {
    index_bounds_facts(data, idx as nat);
    data[idx * UniformSize()..idx * UniformSize() + UniformSize()]
  }

  predicate parsable(data: mseq<byte>) {
    forall idx | 0 <= idx < length(data) :: elementMarshalling.parsable(ElementData(data, idx as uint64))
  }

  function parse_prefix(data: mseq<byte>, len: nat) : (result: UnmarshalledType)
    requires parsable(data)
    requires len <= length(data)
    ensures |result| == len
    ensures forall i | 0 <= i < len :: result[i] == elementMarshalling.parse(ElementData(data, i as uint64))
  {
    if len == 0 then
      []
    else
      var prefix := parse_prefix(data, len - 1);
      var last := elementMarshalling.parse(ElementData(data, len as uint64 - 1));
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
    && (forall i | 0 <= i < |value| :: elementMarshalling.marshallable(value[i]))
    && (forall i | 0 <= i < |value| :: elementMarshalling.size(value[i]) == UniformSize() as nat)
  }

  lemma marshallable_prefix(value: UnmarshalledType, len: nat)
    requires marshallable(value)
    requires 0 <= len <= |value|
    ensures marshallable(value[..len])
  {
  }

  function size(value: UnmarshalledType) : nat
  {
    NatMulNatIsNat(|value|, UniformSize() as nat);
    |value| * UniformSize() as nat
  }

  method Size(value: UnmarshalledType) returns (sz: uint64)
  {
    sz := |value| as uint64 * UniformSize();
  }

  lemma parsing_extend(data: mseq<byte>, edata: mseq<byte>)
    requires parsable(data)
    requires |data| == length(data) * UniformSize() as nat
    requires elementMarshalling.parsable(edata)
    requires |edata| == UniformSize() as nat
    requires |data + edata| < Uint64UpperBound()
    ensures parsable(data + edata)
    ensures parse(data + edata) == parse(data) + [ elementMarshalling.parse(edata) ]
  {
    var extension := data + edata;
    lemma_div_ind(|data|, UniformSize() as nat);
    forall idx | 0 <= idx < length(data)
      ensures ElementData(extension, idx as uint64) == ElementData(data, idx as uint64);
    {
      index_bounds_facts(data, idx);
      Seq.lemma_seq_slice_slice(extension, 0, |data|, idx * UniformSize() as nat, idx * UniformSize() as nat + UniformSize() as nat);
    }
    assert ElementData(extension, length(data) as uint64) == edata;
    assert parse(extension)[..length(data)] == parse(data);
  }

  predicate settable(data: mseq<byte>, idx: nat, value: Element) {
    && idx < length(data)
    && elementMarshalling.marshallable(value)
    && elementMarshalling.size(value) == UniformSize() as nat
  }

  method Settable(data: mseq<byte>, idx: uint64, value: Element) returns (s: bool)
    requires elementMarshalling.marshallable(value)
    requires elementMarshalling.size(value) < Uint64UpperBound()
    ensures s == settable(data, idx as nat, value)
  {
    var len := Length(data);
    var sz := elementMarshalling.Size(value);
    return idx < len && sz == UniformSize();
  }

  predicate setted(data: mseq<byte>, idx: nat, value: Element, newdata: mseq<byte>)
    requires settable(data, idx, value)
  {
    index_bounds_facts(data, idx);
    && |newdata| == |data|
    && (forall i | 0 <= i < idx * UniformSize() as nat :: newdata[i] == data[i])
    && (forall i | (idx+1) * UniformSize() as nat <= i < |data| :: newdata[i] == data[i])
    && elementMarshalling.parsable(newdata[idx * UniformSize() as nat..(idx+1) * UniformSize() as nat])
    && elementMarshalling.parse(newdata[idx * UniformSize() as nat..(idx+1) * UniformSize() as nat]) == value
  }

  lemma setted_parsing(data: mseq<byte>, idx: nat, value: Element, newdata: mseq<byte>)
    requires parsable(data)
    requires settable(data, idx, value)
    requires setted(data, idx, value, newdata)
    ensures lengthable(newdata)
    ensures length(newdata) == length(data)
    ensures parsable(newdata)
    ensures |parse(newdata)| == |parse(data)|
    ensures idx as nat < |parse(data)|
    ensures parse(newdata) == parse(data)[idx as nat := value]
  {
    assert length(newdata) == length(data);

    forall i | 0 <= i < length(newdata)
      ensures elementMarshalling.parsable(ElementData(newdata, i as uint64))
      ensures elementMarshalling.parse(ElementData(newdata, i as uint64)) == parse(data)[idx as nat := value][i]
    {
      index_bounds_facts(data, i);
      calc {
        ElementData(newdata, i as uint64);
        newdata[i * UniformSize() as nat..(i + 1) * UniformSize() as nat];
        { Seq.lemma_seq_slice_slice(newdata, 0, |data|, i * UniformSize() as nat, (i + 1) * UniformSize() as nat); }
        newdata[i * UniformSize() as nat..(i + 1) * UniformSize() as nat];
      }
      calc {
        ElementData(data, i as uint64);
        data[i * UniformSize() as nat..(i + 1) * UniformSize() as nat];
        { Seq.lemma_seq_slice_slice(data, 0, |data|, i * UniformSize() as nat, (i + 1) * UniformSize() as nat); }
        data[i * UniformSize() as nat..(i + 1) * UniformSize() as nat];
      }
      if i == idx as nat {
        assert elementMarshalling.parsable(ElementData(newdata, i as uint64));
      } else {
        forall j: nat | i * UniformSize() as nat <= j < (i+1) * UniformSize() as nat
          ensures j < |newdata|
          ensures newdata[j] == data[j]
          {
            if i < idx as nat {
              assert i + 1 <= idx;
              if i + 1 < idx {
                PosMulPreservesOrder(i + 1, idx, UniformSize() as nat);
              }
            } else {
              assert idx + 1 <= i;
              if idx + 1 < i {
                PosMulPreservesOrder(idx + 1, i, UniformSize() as nat);
              }
            }
          }
          Seq.lemma_seq_extensionality_slice(data, newdata, i * UniformSize() as nat, (i+1) * UniformSize() as nat);
      }
    }
    assert forall i | 0 <= i < length(newdata) :: parse(newdata)[i] == elementMarshalling.parse(ElementData(newdata, i as uint64));
  }

  method Set(linear data: mseq<byte>, start: uint64, end: uint64, idx: uint64, value: Element)
    returns (linear newdata: mseq<byte>)
    requires start as nat <= end as nat <= |data|
    requires settable(data[start..end], idx as nat, value)
    ensures |newdata| == |data|
    ensures forall i | 0 <= i < start :: newdata[i] == data[i]
    ensures forall i | end as nat <= i < |newdata| :: newdata[i] == data[i]
    ensures setted(data[start..end], idx as nat, value, newdata[start..end])
    ensures lengthable(newdata[start..end])
    ensures length(newdata[start..end]) == length(data[start..end])
    ensures parsable(data[start..end]) ==> parsable(newdata[start..end])
    ensures parsable(data[start..end]) ==> |parse(newdata[start..end])| == |parse(data[start..end])|
    ensures parsable(data[start..end]) ==> idx as nat < |parse(data[start..end])|
    ensures parsable(data[start..end]) ==> parse(newdata[start..end]) == parse(data[start..end])[idx as nat := value]
  {
    index_bounds_facts(data[start..end], idx as nat);

    var newend;
    newdata, newend := elementMarshalling.Marshall(value, data, start + idx * UniformSize());

    calc {
      newdata[start as nat..end][idx as nat * UniformSize() as nat..(idx as nat + 1) * UniformSize() as nat];
      { Seq.lemma_seq_slice_slice(newdata, start as nat, end as nat, idx as nat * UniformSize() as nat, (idx as nat + 1) * UniformSize() as nat); }
      newdata[start as nat + idx as nat * UniformSize() as nat..start as nat + (idx as nat + 1) * UniformSize() as nat];
    }
    assert setted(data[start..end], idx as nat, value, newdata[start..end]);
    if parsable(data[start..end]) {
      setted_parsing(data[start..end], idx as nat, value, newdata[start..end]);
    }
  }
}


/////////////////////////////////////////////////////////////////
// Implementation for marshalling a sequence of packable integers
//
// We could just use the UniformSized marshalling code further below,
// but that would marshall each integer one at a time, which would
// (presumably) be slower.
/////////////////////////////////////////////////////////////////

abstract module IntegerSeqMarshalling(Int: NativePackedInt)
refines UniformSizedElementSeqMarshallingCommon(IntegerMarshalling(Int)) {
  function method UniformSize() : uint64 {
    Int.Size()
  }

  lemma always_parsable(data: mseq<byte>)
    ensures parsable(data)
  {
    var len := length(data);
    forall i | 0 <= i < len
      ensures elementMarshalling.parsable(ElementData(data, i as uint64))
    {
      DivMulOrder(length(data), UniformSize() as nat);
      assert i + 1 <= length(data);
      if i + 1 < length(data) {
        PosMulPreservesOrder(i + 1, length(data), UniformSize() as nat);
      }
      assert (i + 1) * UniformSize() as nat <=  length(data) * UniformSize() as nat;
      assert length(data) * UniformSize() as nat <= |data|;
      assert (i + 1) * UniformSize() as nat <= |data|;
    }
  }

  lemma parse_is_unpack_Seq(data: mseq<byte>)
    requires parsable(data)
    ensures parse(data) == Int.unpack_Seq(data[..length(data) * Int.Size() as nat], length(data))
  {
    var len := length(data);
    var value := Int.unpack_Seq(data[..len * Int.Size() as nat], len);
    forall i | 0 <= i < |value|
      ensures value[i] == parse(data)[i]
    {
      index_bounds_facts(data, i);
      if i + 1 < len {
        PosMulPreservesOrder(i + 1, len, Int.Size() as nat);
      }
      Seq.lemma_seq_slice_slice(data, 0, Int.Size() as nat * len as nat, i * Int.Size() as nat, (i+1) * Int.Size() as nat);
      Seq.lemma_seq_slice_slice(data, i * UniformSize() as nat, (i + 1) * UniformSize() as nat, 0, Int.Size() as nat);
    }
  }

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var len := Length(data);
    var value := Int.Cast_Seq(data, 0, len);
    assert |value| < Uint64UpperBound();
    ovalue := Some(value);
    always_parsable(data);
    parse_is_unpack_Seq(data);
  }

  method Parsable(data: mseq<byte>) returns (p: bool)
  {
    always_parsable(data);
    p := true;
  }

  method Parse(data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var length := Length(data);
    value := Int.Cast_Seq(data, 0, length);
    parse_is_unpack_Seq(data);
  }

  method FastGet(data: mseq<byte>, idx: uint64) returns (element: Element)
    requires idx as nat < length(data)
    ensures parsable(data);
    ensures element == parse(data)[idx]
  {
    index_bounds_facts(data, idx as nat);
    always_parsable(data);
    element := Int.Cast(data, idx * Int.Size());
    assert data[idx * Int.Size()..idx * Int.Size() + Int.Size()] == data[idx * Int.Size()..idx * Int.Size() + Int.Size()][..Int.Size()];
  }

  method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
    returns (linear newdata: mseq<byte>, end: uint64)
  {
    newdata := data;
    Int.Pack_Seq_into_ByteSeq(value, inout newdata, start);
    var sz := Size(value);
    end := start + sz;

    always_parsable(newdata[start..end]);
    parse_is_unpack_Seq(newdata[start..end]);
    MulDivCancel(|value|, Int.Size() as nat);
    Seq.lemma_seq_slice_slice(newdata, start as nat, end as nat, 0, length(newdata[start..end]) * Int.Size() as nat);
  }
}

abstract module Uint32SeqMarshalling refines IntegerSeqMarshalling(NativePackedUint32) {
}

abstract module Uint64SeqMarshalling refines IntegerSeqMarshalling(NativePackedUint64) {
}

//////////////////////////////////////////////////////////////////////
// Implementation of marshalling a sequence of items that all have the
// same marshalled size.
//////////////////////////////////////////////////////////////////////

abstract module UniformSizedElementSeqMarshalling(Element_Marshalling: Marshalling)
refines UniformSizedElementSeqMarshallingCommon(Element_Marshalling) {

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>) {
    var len: uint64 := Length(data);
    if len == 0 {
      var empty: UnmarshalledType := [];
      return Some(empty);
    }

    // We get the first element by itself so we can call
    // seq_alloc_init below.
    var oelt := ElementMarshalling.TryParse(ElementData(data, 0));
    if oelt == None {
      return None;
    }
    linear var lresult := seq_alloc_init(len, oelt.value);

    var i: uint64 := 1;
    var parsing_failed := false;
    while i < len
      invariant i <= len
      invariant |lresult| == len as nat
      invariant forall j: nat | j < i as nat :: ElementMarshalling.parsable(ElementData(data, j as uint64))
      invariant forall j: nat | j < i as nat :: lresult[j] == ElementMarshalling.parse(ElementData(data, j as uint64))
    {
      oelt := ElementMarshalling.TryParse(ElementData(data, i));
      if oelt == None {
        parsing_failed := true;
        break;
      }
      mut_seq_set(inout lresult, i, oelt.value);
      i := i + 1;
    }

    var result: UnmarshalledType := seq_unleash(lresult);

    if parsing_failed {
      ovalue := None;
    } else {
      ovalue := Some(result);
    }
  }

  method Parsable(data: mseq<byte>) returns (p: bool)
  {
    var len: uint64 := Length(data);
    if len == 0 {
      return true;
    }

    var i: uint64 := 0;
    while i < len
      invariant i <= len
      invariant forall j: nat | j < i as nat :: ElementMarshalling.parsable(ElementData(data, j as uint64))
    {
      var p' := ElementMarshalling.Parsable(ElementData(data, i));
      if p' == false {
        return false;
      }
      i := i + 1;
    }
    return true;
  }

  method Parse(data: mseq<byte>) returns (value: UnmarshalledType) {
    var len: uint64 := Length(data);
    if len == 0 {
      var empty: UnmarshalledType := [];
      return empty;
    }

    // We get the first element by itself so we can call
    // seq_alloc_init below.
    var elt := ElementMarshalling.Parse(ElementData(data, 0));
    linear var lresult := seq_alloc_init(len, elt);

    var i: uint64 := 1;
    while i < len
      invariant i <= len
      invariant |lresult| == len as nat
      invariant forall j: nat | j < i as nat :: lresult[j] == ElementMarshalling.parse(ElementData(data, j as uint64))
    {
      elt := ElementMarshalling.Parse(ElementData(data, i));
      mut_seq_set(inout lresult, i, elt);
      i := i + 1;
    }

    var result: UnmarshalledType := seq_unleash(lresult);
    value := result;
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
      invariant end as nat == start as nat + size(value[..i]) <= |newdata|
      invariant forall j | 0 <= j < start :: newdata[j] == data[j]
      invariant forall j | end as nat <= j < |data| :: newdata[j] == data[j]
      invariant parsable(newdata[start..end])
      invariant parse(newdata[start..end]) == value[..i]
    {
      ghost var oldend := end;
      ghost var olddata := newdata[start..end];
      if i as nat + 1 < |value| {
        PosMulPreservesOrder(i as nat + 1, |value|, UniformSize() as nat);
      }

      NLarith.DistributeLeft(i as nat, 1, UniformSize() as nat);
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

////////////////////////////////////////////////////////////////////
// Marshalling of sequences of uniform-sized elements, with a length
// field up front so we can resize it.
////////////////////////////////////////////////////////////////////

abstract module
ResizableUniformSizedElementSeqMarshalling(LengthInt: NativePackedInt,
                                           elementMarshalling: Marshalling)
refines SeqMarshalling(elementMarshalling) {
  import LengthMarshalling = IntegerMarshalling(LengthInt)
  import USESM = UniformSizedElementSeqMarshallingCommon(elementMarshalling)
  import opened Mathematics
  import opened LinearSequence_s
  import opened LinearSequence_i
  import Seq = Sequences
  import NLarith

  function method sizeOfLengthField() : uint64 {
    LengthInt.Size()
  }

  function maxLength(data: mseq<byte>) : nat
    requires sizeOfLengthField() as nat <= |data|
  {
    USESM.length(data[sizeOfLengthField()..])
  }
  
  predicate lengthable'(data: mseq<byte>) {
    && sizeOfLengthField() as nat <= |data|
    && var ilen := LengthMarshalling.parse(data[..sizeOfLengthField()]);
    && LengthInt.fitsInUint64(ilen)
    && var len := LengthInt.toInt(ilen);
    && len <= maxLength(data)
  }

  function length(data: mseq<byte>) : nat
    requires lengthable'(data)
    ensures length(data) <=  length(data) * USESM.UniformSize() as nat <= |data| - sizeOfLengthField() as nat
  {
    var len := LengthInt.toInt(LengthMarshalling.parse(data[..sizeOfLengthField()]));
    PosMulPreservesLe(len, (|data| - sizeOfLengthField() as nat) / USESM.UniformSize() as nat, USESM.UniformSize() as nat);
    PosMulPreservesLe(1, USESM.UniformSize() as nat, len);
    len
  }

  predicate lengthable(data: mseq<byte>) {
    lengthable'(data)
  }

  lemma index_bounds_facts(data: mseq<byte>, idx: nat)
    requires sizeOfLengthField() as nat <= |data|
    requires idx < maxLength(data)
    ensures
    0 <=  sizeOfLengthField() as nat + idx * USESM.UniformSize() as nat
      <  sizeOfLengthField() as nat + idx * USESM.UniformSize() as nat + USESM.UniformSize() as nat
      == sizeOfLengthField() as nat + (idx + 1) * USESM.UniformSize() as nat
      <=  sizeOfLengthField() as nat + maxLength(data) * USESM.UniformSize() as nat
      <=  |data|
  {
    NatMulNatIsNat(idx, USESM.UniformSize() as nat);
    NLarith.DistributeLeft(idx, 1, USESM.UniformSize() as nat);
    if idx + 1 < maxLength(data) {
      PosMulPreservesOrder(idx + 1, maxLength(data), USESM.UniformSize() as nat);
    }
  }

  method TryLength(data: mseq<byte>) returns (olen: Option<uint64>)
    ensures olen.Some? ==> olen.value as nat == length(data)
  {
    if LengthInt.Size() <= |data| as uint64 {
      var l' := LengthMarshalling.Parse(data[..sizeOfLengthField()]);
      if LengthInt.fitsInUint64(l') {
        var l: uint64 := LengthInt.toUint64(l');
        var maxl := USESM.Length(data[sizeOfLengthField()..]);
        if l <= maxl {
          if l < maxl {
            index_bounds_facts(data, l as nat);
          }
          MulDivCancel(l as nat, USESM.UniformSize() as nat);
          NatMulNatIsNat(l as nat, USESM.UniformSize() as nat);
          olen := Some(l);
        } else {
          olen := None;
        }
      } else {
        olen := None;
      }
    } else {
      olen := None;
    }
  }

  method Lengthable(data: mseq<byte>) returns (l: bool) {
    var olen := TryLength(data);
    return olen.Some?;
  }

  method Length(data: mseq<byte>) returns (len: uint64)
    ensures len as nat == length(data)
  {
    var l := LengthMarshalling.Parse(data[..sizeOfLengthField()]);
    len := LengthInt.toUint64(l);
    if len as nat < maxLength(data) {
      index_bounds_facts(data, len as nat);
    }
    MulDivCancel(len as nat, USESM.UniformSize() as nat);
    NatMulNatIsNat(len as nat, USESM.UniformSize() as nat);
  }

  function method ElementData(data: mseq<byte>, idx: uint64) : mseq<byte>
    requires sizeOfLengthField() as nat <= |data|
    requires idx as nat < maxLength(data)
  {
    USESM.ElementData(data[sizeOfLengthField()..], idx)
  }

  predicate gettable(data: mseq<byte>, idx: nat) {
    && lengthable(data)
    && var len := length(data);
    && USESM.gettable(data[sizeOfLengthField() as nat..sizeOfLengthField() as nat + len * USESM.UniformSize() as nat], idx)
  }

  method TryGet(data: mseq<byte>, idx: uint64) returns (oedata: Option<mseq<byte>>) {
    var olen := TryLength(data);
    if olen == None {
      return None;
    }
    var len := olen.value;
    assert sizeOfLengthField() as nat + (len as nat) * (USESM.UniformSize() as nat) < Uint64UpperBound();
    oedata := USESM.TryGet(data[sizeOfLengthField()..sizeOfLengthField() + len * USESM.UniformSize()], idx);
    if parsable(data) {
      parse_length(data);
    }
  }

  method Gettable(data: mseq<byte>, idx: uint64) returns (g: bool) {
    var olen := TryLength(data);
    if olen == None {
      return false;
    }
    var len := olen.value;
    g := USESM.Gettable(data[sizeOfLengthField()..sizeOfLengthField() + len * USESM.UniformSize()], idx);
  }

  method Get(data: mseq<byte>, idx: uint64) returns (edata: mseq<byte>) {
    var len := Length(data);
    edata := USESM.Get(data[sizeOfLengthField()..sizeOfLengthField() + len * USESM.UniformSize()], idx);
  }

  predicate settable(data: mseq<byte>, idx: nat, value: Element) {
    && lengthable(data)
    && idx < length(data)
    && ElementMarshalling.marshallable(value)
    && ElementMarshalling.size(value) == USESM.UniformSize() as nat
  }

  method Settable(data: mseq<byte>, idx: uint64, value: Element) returns (s: bool)
    requires ElementMarshalling.marshallable(value)
    requires ElementMarshalling.size(value) < Uint64UpperBound()
    ensures s == settable(data, idx as nat, value)
  {
    var olen := TryLength(data);
    if olen == None {
      return false;
    }
    var len := olen.value;
    var sz := ElementMarshalling.Size(value);
    return idx < len && sz == USESM.UniformSize();
  }

  method Set(linear data: mseq<byte>, start: uint64, end: uint64, idx: uint64, value: Element)
    returns (linear newdata: mseq<byte>)
    requires start as nat <= end as nat <= |data|
    requires settable(data[start..end], idx as nat, value)
    ensures |newdata| == |data|
    ensures forall i | 0 <= i < start :: newdata[i] == data[i]
    ensures forall i | end as nat <= i < |newdata| :: newdata[i] == data[i]
    ensures lengthable(newdata[start..end])
    ensures length(newdata[start..end]) == length(data[start..end])
    ensures parsable(data[start..end]) ==> parsable(newdata[start..end])
    ensures parsable(data[start..end]) ==> |parse(newdata[start..end])| == |parse(data[start..end])|
    ensures parsable(data[start..end]) ==> idx as nat < |parse(data[start..end])|
    ensures parsable(data[start..end]) ==> parse(newdata[start..end]) == parse(data[start..end])[idx as nat := value]
  {
    var substart := start + sizeOfLengthField();
    USESM.index_bounds_facts(data[substart..end], idx as nat);

    var newend;
    newdata, newend := ElementMarshalling.Marshall(value, data, substart + idx * USESM.UniformSize());

    assert newdata[start..end][..sizeOfLengthField()] == data[start..end][..sizeOfLengthField()];

    if parsable(data[start..end]) {
      var len := length(data[start..end]);
      MulDivCancel(len, USESM.UniformSize() as nat);
      Seq.lemma_seq_slice_slice(newdata,
        start as nat,
        end as nat,
        sizeOfLengthField() as nat,
        sizeOfLengthField() as nat + len * USESM.UniformSize() as nat);
      Seq.lemma_seq_slice_slice(data,
        start as nat,
        end as nat,
        sizeOfLengthField() as nat,
        sizeOfLengthField() as nat + len * USESM.UniformSize() as nat);
      var subdata := data[start + sizeOfLengthField()..start as nat + sizeOfLengthField() as nat + len * USESM.UniformSize() as nat];
      USESM.index_bounds_facts(subdata, idx as nat);
      Seq.lemma_seq_slice_slice(newdata, 
        start as nat + sizeOfLengthField() as nat,
        start as nat + sizeOfLengthField() as nat + len * USESM.UniformSize() as nat,
        idx as nat * USESM.UniformSize() as nat,
        (idx as nat + 1) * USESM.UniformSize() as nat);
      USESM.setted_parsing(
        data[start..end][sizeOfLengthField()..sizeOfLengthField() as nat + len * USESM.UniformSize() as nat],
        idx as nat, value,
        newdata[start..end][sizeOfLengthField()..sizeOfLengthField() as nat + len * USESM.UniformSize() as nat]);
    }
  }

  lemma ElementDataSimplification(data: mseq<byte>, start: nat, end: nat, idx: nat)
    requires start <= end <= |data|
    requires sizeOfLengthField() as nat <= end - start
    requires idx < maxLength(data[start..end])
    ensures 0
            <= start + sizeOfLengthField() as nat + idx * USESM.UniformSize() as nat
            <= start + sizeOfLengthField() as nat + idx * USESM.UniformSize() as nat + USESM.UniformSize() as nat
            <= |data|
    ensures
    ElementData(data[start..end], idx as uint64)
    ==
    data
      [start + sizeOfLengthField() as nat + idx * USESM.UniformSize() as nat
       ..start + sizeOfLengthField() as nat + idx * USESM.UniformSize() as nat + USESM.UniformSize() as nat]
  {
    PosMulPreservesOrder(idx, idx + 1, USESM.UniformSize() as nat);
    NatMulNatIsNat(idx, USESM.UniformSize() as nat);
    NLarith.DistributeLeft(idx, 1, USESM.UniformSize() as nat);
    PosMulPreservesLe(idx + 1, maxLength(data[start..end]), USESM.UniformSize() as nat);

    Seq.lemma_seq_slice_slice(
      data,
      start, end,
      sizeOfLengthField() as nat, end - start);
    Seq.lemma_seq_slice_slice(
      data,
      start + sizeOfLengthField() as nat,
      end,
      idx * USESM.UniformSize() as nat,
      (idx + 1) * USESM.UniformSize() as nat);

    Seq.lemma_seq_slice_slice(
      data,
      start, end,
      sizeOfLengthField() as nat, sizeOfLengthField() as nat + maxLength(data[start..end]) * USESM.UniformSize() as nat);
    Seq.lemma_seq_slice_slice(
      data,
      start + sizeOfLengthField() as nat,
      start + sizeOfLengthField() as nat + maxLength(data[start..end]) * USESM.UniformSize() as nat,
      idx * USESM.UniformSize() as nat,
      (idx + 1) * USESM.UniformSize() as nat);
  }

  predicate resizable(data: mseq<byte>, newlen: nat) {
    && lengthable(data)
    && newlen <= maxLength(data)
    && LengthInt.fitsInInteger(newlen as uint64)
  }

  method Resizable(data: mseq<byte>, newlen: uint64)
    returns (r: bool)
    ensures r == resizable(data, newlen as nat)
  {
    var l := Lengthable(data);
    if l {
      var maxlen := USESM.Length(data[LengthInt.Size()..]);
      r := newlen <= maxlen && LengthInt.fitsInInteger(newlen);
    } else {
      r := false;
    }
  }

  method Resize(linear data: mseq<byte>, start: uint64, end: uint64, newlen: uint64)
    returns (linear newdata: mseq<byte>)
    requires start as nat <= end as nat <= |data|
    requires resizable(data[start..end], newlen as nat)
    requires forall i | 0 <= i < newlen :: ElementMarshalling.parsable(ElementData(data[start..end], i))
    ensures |newdata| == |data|
    ensures forall i | 0 <= i < start :: newdata[i] == data[i]
    ensures forall i | end as nat <= i < |newdata| :: newdata[i] == data[i]
    ensures lengthable(newdata[start..end])
    ensures length(newdata[start..end]) == newlen as nat
    ensures parsable(data[start..end]) ==> parsable(newdata[start..end])
    ensures parsable(data[start..end]) ==> |parse(newdata[start..end])| == newlen as nat
    ensures parsable(data[start..end]) ==> Seq.agree(parse(newdata[start..end]), parse(data[start..end]))
  {
    var newend;
    newdata, newend := LengthMarshalling.Marshall(LengthInt.fromUint64(newlen), data, start);

    assert newdata[start..end][..LengthInt.Size()] == newdata[start..start + LengthInt.Size()];
    LengthInt.fromtoInverses();

    if parsable(data[start..end]) {
      var len := length(data[start..end]);
      NatMulNatIsNat(newlen as nat, USESM.UniformSize() as nat);
      PosMulPreservesLe(newlen as nat, maxLength(data[start..end]), USESM.UniformSize() as nat);
      Seq.lemma_seq_slice_slice(newdata,
        start as nat,
        end as nat,
        sizeOfLengthField() as nat,
        sizeOfLengthField() as nat + newlen as nat * USESM.UniformSize() as nat);
      MulDivCancel(newlen as nat, USESM.UniformSize() as nat);
      forall i | 0 <= i < newlen as nat
        ensures ElementData(newdata[start..end], i as uint64) == ElementData(data[start..end], i as uint64);
      {
        MulDivCancel(newlen as nat, USESM.UniformSize() as nat);
        ElementDataSimplification(data, start as nat, end as nat, i);
        ElementDataSimplification(newdata, start as nat, end as nat, i);
        NatMulNatIsNat(i as nat, USESM.UniformSize() as nat);
        assert ElementData(newdata[start..end], i as uint64) == ElementData(data[start..end], i as uint64);
      }

      parsable_simplification(data[start..end]);
      parsable_simplification(newdata[start..end]);

      parse_simplification(data[start..end]);
      parse_simplification(newdata[start..end]);
    }
  }

  function USESMData(data: mseq<byte>) : mseq<byte>
    requires lengthable'(data)
  {
    data[sizeOfLengthField()..sizeOfLengthField() as nat + length(data) * USESM.UniformSize() as nat]
  }
  
  lemma ElementDataIsUSESMElementData(data: mseq<byte>, i: nat)
    requires lengthable'(data)
    requires i < length(data)
    ensures USESM.length(USESMData(data)) == length(data)
    ensures ElementData(data, i as uint64) == USESM.ElementData(USESMData(data), i as uint64)
  {
    var len := length(data);
    MulDivCancel(len, USESM.UniformSize() as nat);
    ElementDataSimplification(data, 0, |data|, i);
    NatMulNatIsNat(i, USESM.UniformSize() as nat);
    NLarith.DistributeLeft(i, 1, USESM.UniformSize() as nat);
    PosMulPreservesLe(i + 1, len, USESM.UniformSize() as nat);
    Seq.lemma_seq_slice_slice(data,
      sizeOfLengthField() as nat, sizeOfLengthField() as nat + len * USESM.UniformSize() as nat,
      i * USESM.UniformSize() as nat, i * USESM.UniformSize() as nat + USESM.UniformSize() as nat);
  }
  
  predicate parsable(data: mseq<byte>) {
    && lengthable'(data)
    && var len := length(data);
    && USESM.parsable(USESMData(data))
  }

  predicate parsable'(data: mseq<byte>) {
    && lengthable'(data)
    && var len := length(data);
    && forall i | 0 <= i < len :: ElementMarshalling.parsable(ElementData(data, i as uint64))
  }

  lemma parsable_simplification(data: mseq<byte>)
    ensures parsable(data) <==> parsable'(data)
  {
    if lengthable'(data) {
      var len := length(data);
      MulDivCancel(len, USESM.UniformSize() as nat);
      forall i | 0 <= i < length(data)
        ensures ElementData(data, i as uint64) == USESM.ElementData(USESMData(data), i as uint64)
      {
        ElementDataIsUSESMElementData(data, i);
      }
    }
  }
  
  function parse(data: mseq<byte>) : UnmarshalledType {
    var len := length(data);
    USESM.parse(USESMData(data))
  }

  function parse'(data: mseq<byte>) : UnmarshalledType
    requires parse.requires(data)
  {
    var len := length(data);
    parsable_simplification(data);
    var result: seq<Element> := seq(len, i requires 0 <= i < len => ElementMarshalling.parse(ElementData(data, i as uint64)));
    assert |result| < Uint64UpperBound();
    result
  }

  lemma parse_simplification(data: mseq<byte>)
    requires parsable(data) || parsable'(data)
    ensures parsable(data) && parsable'(data)
    ensures parse(data) == parse'(data)
  {
    parsable_simplification(data);
    parse_length(data);
    forall i | 0 <= i < length(data)
      ensures ElementData(data, i as uint64) == USESM.ElementData(USESMData(data), i as uint64)
    {
      ElementDataIsUSESMElementData(data, i);
    }
    assert forall i | 0 <= i < |parse(data)| :: parse(data)[i] == parse'(data)[i];
  }

  lemma parse_length(data: mseq<byte>)
    requires parsable(data)
    ensures |parse(data)| == length(data)
  {
    MulDivCancel(length(data), USESM.UniformSize() as nat);
  }

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>) {
    var olen := TryLength(data);
    if olen == None {
      return None;
    }
    ovalue := USESM.TryParse(data[sizeOfLengthField()..sizeOfLengthField() + olen.value * USESM.UniformSize()]);
  }

  method Parsable(data: mseq<byte>) returns (p: bool) {
    var olen := TryLength(data);
    if olen == None {
      return false;
    }
    p := USESM.Parsable(data[sizeOfLengthField()..sizeOfLengthField() + olen.value * USESM.UniformSize()]);
  }

  method Parse(data: mseq<byte>) returns (value: UnmarshalledType) {
    var len := Length(data);
    value := USESM.Parse(data[sizeOfLengthField()..sizeOfLengthField() + len * USESM.UniformSize()]);
  }
}

// ////////////////////////////////////////////////////////
// // Interface for appending items to marshalled sequences
// ////////////////////////////////////////////////////////

// abstract module AppendableSeqMarshalling refines SeqMarshalling {
//   predicate appendable(data: mseq<byte>, newItemSize: nat)

//   method Appendable(data: mseq<byte>, newItemSize: uint64) returns (app: bool)
//     ensures app == appendable(data, newItemSize as nat)

//   method Append(linear data: mseq<byte>, start: uint64, end: uint64, elt: Element)
//     returns (linear newdata: mseq<byte>)
//     requires ElementMarshalling.marshallable(elt)
//     requires start as nat <= end as nat <= |data|
//     requires appendable(data[start..end], ElementMarshalling.size(elt))
//     ensures |newdata| == |data|
//     ensures forall i | 0 <= i < start :: newdata[i] == data[i]
//     ensures forall i | end as nat <= i < |newdata| :: newdata[i] == data[i]
//     ensures parsable(data[start..end]) ==> parsable(newdata[start..end])
//     ensures parsable(data[start..end]) ==> parse(newdata[start..end]) == parse(data[start..end]) + [ elt ]
// }

// //////////////////////////////////////////////////////////////////////
// // Implementation of marshalling a general sequence of items
// //////////////////////////////////////////////////////////////////////

// abstract module VariableSizedElementSeqMarshalling refines AppendableSeqMarshalling {
//   import LengthMarshalling : IntegerMarshalling
//   import BoundarySeqMarshalling : IntegerSeqMarshalling
//   import opened Sequences

//   import LengthInt = LengthMarshalling.Int
//   import BoundaryInt = BoundarySeqMarshalling.Int

//   type Length = LengthMarshalling.Int.Integer
//   type Boundary = BoundarySeqMarshalling.Int.Integer

//   type BoundaryTable = mseq<Boundary>

//   // INTERNAL FUNCTIONS

//   function sizeOfLengthField() : nat {
//     LengthInt.Size() as nat
//   }

//   function sizeOfBoundaryEntry() : nat {
//     BoundaryInt.Size() as nat
//   }

//   predicate lengthable'(data: mseq<byte>)
//   {
//     && sizeOfLengthField() <= |data|
//     && 0 <= LengthInt.toInt(LengthMarshalling.parse(data[..sizeOfLengthField()]))
//   }

//   function length'(data: mseq<byte>) : nat
//     requires lengthable'(data)
//   {
//     LengthInt.toInt(LengthMarshalling.parse(data[..sizeOfLengthField()]))
//   }

//   datatype Structure = Structure(boundaries: mseq<Boundary>, elements: mseq<byte>)

//   function sizeOfTable(len: nat) : nat {
//     len * sizeOfBoundaryEntry()
//   }

//   predicate tableable(data: mseq<byte>) {
//     && lengthable'(data)
//     && var len := length'(data);
//     && sizeOfLengthField() + sizeOfTable(len) <= |data|
//   }

//   function tabledata(data: mseq<byte>) : seq<byte>
//     requires tableable(data)
//   {
//     var len := length'(data);
//     data[sizeOfLengthField()..sizeOfLengthField() + sizeOfTable(len)]
//   }

//   function table(data: mseq<byte>) : BoundaryTable
//     requires tableable(data)
//   {
//     var td := tabledata(data);
//     BoundarySeqMarshalling.always_parsable(td);
//     BoundarySeqMarshalling.parse(td)
//   }

//   function elementsSize(data: mseq<byte>) : nat
//     requires tableable(data)
//   {
//     var tb: seq<Boundary> := table(data);
//     if |tb| == 0 then
//       0
//     else if BoundaryInt.toInt(Last(tb)) < 0 then
//       0
//     else
//       BoundaryInt.toInt(Last(tb))
//   }

//   predicate tableEndInBounds(data: mseq<byte>)
//     requires tableable(data)
//   {
//     elementsSize(data) <= |data| - sizeOfLengthField() - sizeOfTable(length'(data))
//   }

//   function elementsData(data: mseq<byte>) : mseq<byte>
//     requires tableable(data)
//   {
//     var tb := table(data);
//     data // FIXME
//   }

//   function partialParse(data: mseq<byte>) : (result: Structure)
//     requires tableable(data)
//   {
//     Structure(table(data), elementsData(data))
//   }

//   predicate structGettable(struct: Structure, idx: nat) {
//     && idx < |struct.boundaries|
//     && var start := BoundaryInt.toInt(struct.boundaries[idx]);
//     && var end := if idx == 0 then |struct.elements| else BoundaryInt.toInt(struct.boundaries[idx-1]);
//     && 0 <= start <= end <= |struct.elements|
//   }

//   function structGet(struct: Structure, idx: nat) : mseq<byte>
//     requires structGettable(struct, idx)
//   {
//     var start := BoundaryInt.toInt(struct.boundaries[idx]);
//     var end := if idx == 0 then |struct.elements| else BoundaryInt.toInt(struct.boundaries[idx-1]);
//     struct.elements[start..end]
//   }

//   // function get(data: mseq<byte>, idx: nat) : mseq<byte>
//   //   requires gettable(data, idx)
//   // {
//   //   structGet(partialParse(data), idx)
//   // }

// //   method TryGet(data: mseq<byte>, idx: uint64) returns (oedata: Option<mseq<byte>>)
// //   {
// //     var ostruct := PartialParse(data);
// //     if ostruct == None || |ostruct.value.boundaries| as uint64 <= idx {
// //       return None;
// //     }
// //     var struct := ostruct.value;

// //     var start := BoundarySeqMarshalling.Int.toUint64(struct.boundaries[idx]);
// //     var end := |struct.elements| as uint64;
// //     if 0 < idx {
// //       end := BoundarySeqMarshalling.Int.toUint64(struct.boundaries[idx]);
// //     }

// //     if start <= end <= |struct.elements| as uint64 {
// //       oedata := Some(struct.elements[start..end]);
// //     } else {
// //       oedata := None;
// //     }

// //   }

// //   method Gettable(data: mseq<byte>, idx: uint64) returns (g: bool)
// //   {
// //     var oedata := TryGet(data, idx);
// //     return oedata.Some?;
// //   }

// //   method Get(data: mseq<byte>, idx: uint64) returns (edata: mseq<byte>)
// //   {
// //     var oedata := TryGet(data, idx);
// //     return oedata.value;
// //   }

//   predicate structParsable(struct: Structure) {
//     && (forall i | 0 <= i < |struct.boundaries| :: structGettable(struct, i))
//     && (forall i | 0 <= i < |struct.boundaries| :: ElementMarshalling.parsable(structGet(struct, i)))
//   }

//   function structParse(struct: Structure, prefixLen: nat) : mseq<Element>
//     requires prefixLen <= |struct.boundaries|
//     requires structParsable(struct)
//   {
//     if prefixLen == 0 then
//       []
//     else
//       structParse(struct, prefixLen - 1) + [ ElementMarshalling.parse(structGet(struct, prefixLen - 1)) ]
//   }

//   predicate parsable(data: mseq<byte>) {
//     && tableable(data)
//     && var struct := partialParse(data);
//     && structParsable(struct)
//   }

//   function parse(data: mseq<byte>) : UnmarshalledType {
//     var struct := partialParse(data);
//     structParse(struct, |struct.boundaries|)
//   }

// //   method PartialParse(data: mseq<byte>) returns (oresult : Option<Structure>)
// //     ensures oresult.Some? <==> tableable(data)
// //     ensures tableable(data) ==> oresult.value == partialParse(data)
// //   {
// //     var olen := TryLength(data);
// //     if olen == None {
// //       return None;
// //     }
// //     var len := olen.value;

// //     var tbdata := data[LengthMarshalling.Int.Size()..LengthMarshalling.Int.Size() + len * BoundarySeqMarshalling.Int.Size()];
// //     var table := BoundarySeqMarshalling.Parse(tbdata);
// //     var esdata := data[LengthMarshalling.Int.Size()..];
// //     oresult := Some(Structure(table, esdata));
// //   }


// //   method TryLength(data: mseq<byte>) returns (olen: Option<uint64>)
// //   {
// //     if LengthMarshalling.Int.Size() <= |data| as uint64 {
// //       var l := LengthMarshalling.Parse(data[..LengthMarshalling.Int.Size()]);
// //       olen := Some(LengthMarshalling.Int.toUint64(l));
// //     } else {
// //       olen := None;
// //     }
// //   }

// //   method Lengthable(data: mseq<byte>) returns (l: bool)
// //   {
// //     l := LengthMarshalling.Int.Size() <= |data| as uint64;
// //   }

// //   method Length(data: mseq<byte>) returns (len: uint64)
// //     ensures len as nat == length(data)
// //   {
// //     var l := LengthMarshalling.Parse(data[..LengthMarshalling.Int.Size()]);
// //     len := LengthMarshalling.Int.toUint64(l);
// //   }


// //   predicate gettable(data: mseq<byte>, idx: nat)
// //   {
// //     && tableable(data)
// //     && var struct := partialParse(data);
// //     && structGettable(struct, idx)
// //   }

// }
