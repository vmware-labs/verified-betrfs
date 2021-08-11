include "../Lang/NativeTypes.s.dfy"
include "../Lang/System/PackedInts.s.dfy"
include "../Lang/LinearSequence.i.dfy"
include "../Base/Option.s.dfy"
include "../Base/mathematics.i.dfy"
include "../Base/sequences.i.dfy"
include "Math.i.dfy"
include "NLarith.i.dfy"
include "../Base/Slice.i.dfy"

/////////////////////////////////////////
// The most general marshalling interface
/////////////////////////////////////////

abstract module Marshalling {
  import opened NativeTypes
  import opened Options
  import opened Slices

  type UnmarshalledType

  type Config

  predicate validConfig(cfg: Config)

  predicate parsable(cfg: Config, data: mseq<byte>)
    requires validConfig(cfg)

  function parse(cfg: Config, data: mseq<byte>) : UnmarshalledType
    requires validConfig(cfg)
    requires parsable(cfg, data)

  method TryParse(cfg: Config, data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
    requires validConfig(cfg)
    ensures parsable(cfg, data) <==> ovalue.Some?
    ensures parsable(cfg, data) ==> ovalue.value == parse(cfg, data)

  method Parsable(cfg: Config, data: mseq<byte>) returns (p: bool)
    requires validConfig(cfg)
    ensures p == parsable(cfg, data)
  {
    var ovalue := TryParse(cfg, data);
    p := ovalue.Some?;
  }

  method Parse(cfg: Config, data: mseq<byte>) returns (value: UnmarshalledType)
    requires validConfig(cfg)
    requires parsable(cfg, data)
    ensures value == parse(cfg, data)
  {
    var ovalue := TryParse(cfg, data);
    value := ovalue.value;
  }

  predicate marshallable(cfg: Config, value: UnmarshalledType)
    requires validConfig(cfg)

  function size(cfg: Config, value: UnmarshalledType) : uint64
    requires validConfig(cfg)
    requires marshallable(cfg, value)

  method Size(cfg: Config, value: UnmarshalledType) returns (sz: uint64)
    requires validConfig(cfg)
    requires marshallable(cfg, value)
    ensures sz == size(cfg, value)

  method Marshall(cfg: Config, value: UnmarshalledType, linear inout data: mseq<byte>, start: uint64)
    returns (end: uint64)
    requires validConfig(cfg)
    requires marshallable(cfg, value)
    requires start as nat + size(cfg, value) as nat <= |old_data|
    ensures end == start + size(cfg, value)
    ensures |data| == |old_data|
    ensures forall i | 0 <= i < start :: data[i] == old_data[i]
    ensures forall i | end <= i < |data| as uint64 :: data[i] == old_data[i]
    ensures parsable(cfg, data[start..end])
    ensures parse(cfg, data[start..end]) == value
}

////////////////////////////////////////////////////
// Marshalling implementation for a packable integer
////////////////////////////////////////////////////

module IntegerMarshalling(Int: NativePackedInt) refines Marshalling {
  import opened LinearSequence_s

  type UnmarshalledType = Int.Integer

  datatype Config = DefaultConfig

  predicate validConfig(cfg: Config) {
    true
  }

  predicate parsable(cfg: Config, data: mseq<byte>)
  {
    Int.Size() as nat <= |data|
  }

  function parse(cfg: Config, data: mseq<byte>) : UnmarshalledType
  {
    Int.unpack(data[..Int.Size()])
  }

  method TryParse(cfg: Config, data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    if Int.Size() <= |data| as uint64 {
      var value := Int.Cast(data, 0);
      ovalue := Some(value);
    } else {
      ovalue := None;
    }
  }

  method Parsable(cfg: Config, data: mseq<byte>) returns (p: bool)
  {
    var p' := Int.Size() <= |data| as uint64;
    return p';
  }

  method Parse(cfg: Config, data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var value' := Int.Cast(data, 0);
    return value';
  }

  predicate marshallable(cfg: Config, value: UnmarshalledType) {
    true
  }

  function size(cfg: Config, value: UnmarshalledType) : uint64
  {
    Int.Size()
  }

  method Size(cfg: Config, value: UnmarshalledType) returns (sz: uint64)
  {
    sz := Int.Size();
  }

  method Marshall(cfg: Config, value: UnmarshalledType, linear inout data: mseq<byte>, start: uint64)
    returns (end: uint64)
  {
      Int.Pack_into_ByteSeq(value, inout data, start);
      end := start + Int.Size();
      assert data[start..end][..Int.Size()] == data[start..start + Int.Size()];
  }
}

module Uint32Marshalling refines IntegerMarshalling(NativePackedUint32) {
}

module Uint64Marshalling refines IntegerMarshalling(NativePackedUint64) {
}

//////////////////////////////////////////////////////////////////////
// Interface for marshalling sequences
//////////////////////////////////////////////////////////////////////

abstract module SeqMarshalling(Elt: Marshalling) refines Marshalling {
  import opened LinearSequence_s
  import opened LinearSequence_i

  type Element = Elt.UnmarshalledType
  type UnmarshalledType = mseq<Element>

  function method EltCfg(cfg: Config) : Elt.Config
    requires validConfig(cfg)
    ensures Elt.validConfig(EltCfg(cfg))

    // lengths
  predicate lengthable(cfg: Config, data: mseq<byte>)
    requires validConfig(cfg)

  function length(cfg: Config, data: mseq<byte>) : nat
    requires validConfig(cfg)
    requires lengthable(cfg, data)

  method TryLength(cfg: Config, data: mseq<byte>) returns (olen: Option<uint64>)
    requires validConfig(cfg)
    ensures olen.Some? <==> lengthable(cfg, data)
    ensures olen.Some? ==> olen.value as nat == length(cfg, data)

  method Lengthable(cfg: Config, data: mseq<byte>) returns (l: bool)
    requires validConfig(cfg)
    ensures l == lengthable(cfg, data)
  {
    var olen := TryLength(cfg, data);
    return olen.Some?;
  }

  method Length(cfg: Config, data: mseq<byte>) returns (len: uint64)
    requires validConfig(cfg)
    requires lengthable(cfg, data)
    ensures len as nat == length(cfg, data)
  {
    var olen := TryLength(cfg, data);
    return olen.value;
  }

  method LLength(cfg: Config, slice: Slice, shared data: mseq<byte>) returns (len: uint64)
    requires validConfig(cfg)
    requires slice.WF'(data)
    requires lengthable(cfg, slice.I(data))
    ensures len as nat == length(cfg, slice.I(data))

    // getting individual elements
  predicate gettable(cfg: Config, data: mseq<byte>, idx: nat)
    requires validConfig(cfg)

  function get(cfg: Config, slice: Slice, data: mseq<byte>, idx: nat) : (eslice: Slice)
    requires validConfig(cfg)
    requires slice.WF'(data)
    requires gettable(cfg, slice.I(data), idx)
    ensures eslice.WF'(data)

  function getData(cfg: Config, data: mseq<byte>, idx: nat) : (edata: mseq<byte>)
    requires validConfig(cfg)
    requires gettable(cfg, data, idx)
  {
    get(cfg, all(data), data, idx).I(data)
  }

  predicate eltParsable(cfg: Config, data: mseq<byte>, i: nat)
    requires validConfig(cfg)
    requires gettable(cfg, data, i)
  {
    Elt.parsable(EltCfg(cfg), getData(cfg, data, i))
  }

  function getElt(cfg: Config, data: mseq<byte>, idx: nat) : (elt: Element)
    requires validConfig(cfg)
    requires gettable(cfg, data, idx)
    requires eltParsable(cfg, data, idx)
  {
    Elt.parse(EltCfg(cfg), getData(cfg, data, idx))
  }

  method TryGet(cfg: Config, slice: Slice, data: mseq<byte>, idx: uint64) returns (oeslice: Option<Slice>)
    requires validConfig(cfg)
    requires slice.WF'(data)
    ensures oeslice.Some? <==> gettable(cfg, slice.I(data), idx as nat)
    ensures oeslice.Some? ==> oeslice.value == get(cfg, slice, data, idx as nat)

  method Gettable(cfg: Config, data: mseq<byte>, idx: uint64) returns (g: bool)
    requires validConfig(cfg)
    ensures g == gettable(cfg, data, idx as nat)
  {
    var oeslice := TryGet(cfg, all(data), data, idx);
    return oeslice.Some?;
  }

  method Get(cfg: Config, slice: Slice, data: mseq<byte>, idx: uint64) returns (eslice: Slice)
    requires validConfig(cfg)
    requires slice.WF'(data)
    requires gettable(cfg, slice.I(data), idx as nat)
    ensures eslice.WF()
    ensures eslice == get(cfg, slice, data, idx as nat)
  {
    var oeslice := TryGet(cfg, slice, data, idx);
    return oeslice.value;
  }

  method TryGetElt(cfg: Config, data: mseq<byte>, idx: uint64) returns (oelt: Option<Element>)
    requires validConfig(cfg)
    ensures oelt.Some? <==> gettable(cfg, data, idx as nat) && eltParsable(cfg, data, idx as nat)
    ensures oelt.Some? ==> oelt.value == getElt(cfg, data, idx as nat)
  {
    var oeslice := TryGet(cfg, all(data), data, idx);
    if oeslice == None {
      return None;
    }
    oelt := Elt.TryParse(EltCfg(cfg), oeslice.value.I(data));
  }

  method GetElt(cfg: Config, data: mseq<byte>, idx: uint64) returns (elt: Element)
    requires validConfig(cfg)
    requires gettable(cfg, data, idx as nat)
    requires eltParsable(cfg, data, idx as nat)
    ensures elt == getElt(cfg, data, idx as nat)
  {
    var eslice := Get(cfg, all(data), data, idx);
    elt := Elt.Parse(EltCfg(cfg), eslice.I(data));
  }

  method LGetElt(cfg: Config, slice: Slice, shared data: mseq<byte>, idx: uint64) returns (elt: Element)
    requires validConfig(cfg)
    requires slice.WF'(data)
    requires gettable(cfg, slice.I(data), idx as nat)
    requires eltParsable(cfg, slice.I(data), idx as nat)
    ensures elt == getElt(cfg, slice.I(data), idx as nat)

    // setting individual elements
  predicate settable(cfg: Config, data: mseq<byte>, idx: nat, value: Element)
    requires validConfig(cfg)
    requires Elt.marshallable(EltCfg(cfg), value)

  predicate preservesEntry(cfg: Config, data: mseq<byte>, i: nat, newdata: mseq<byte>)
    requires validConfig(cfg)
  {
    && (gettable(cfg, data, i) ==> gettable(cfg, newdata, i))
    && ((gettable(cfg, data, i) && eltParsable(cfg, data, i)) ==>
       (eltParsable(cfg, newdata, i) && getElt(cfg, newdata, i) == getElt(cfg, data, i)))
  }

  lemma preservesEntryTransitive(cfg: Config, data: mseq<byte>, i: nat, middle: mseq<byte>, newdata: mseq<byte>)
    requires validConfig(cfg)
    requires preservesEntry(cfg, data, i, middle)
    requires preservesEntry(cfg, middle, i, newdata)
    ensures preservesEntry(cfg, data, i, newdata)
  {
  }
  
  predicate sets(cfg: Config, data: mseq<byte>, idx: nat, value: Element, newdata: mseq<byte>)
    requires validConfig(cfg)
    requires Elt.marshallable(EltCfg(cfg), value)
    requires settable(cfg, data, idx, value)
  {
    && |newdata| == |data|
    && (lengthable(cfg, data) ==> lengthable(cfg, newdata) && length(cfg, newdata) == length(cfg, data))
    && (forall i | i != idx :: preservesEntry(cfg, data, i, newdata))
    && gettable(cfg, newdata, idx)
    && eltParsable(cfg, newdata, idx)
    && getElt(cfg, newdata, idx) == value
  }

  method Settable(cfg: Config, data: mseq<byte>, idx: uint64, value: Element) returns (s: bool)
    requires validConfig(cfg)
    requires Elt.marshallable(EltCfg(cfg), value)
    ensures s == settable(cfg, data, idx as nat, value)

  method Set(cfg: Config, slice: Slice, linear inout data: mseq<byte>, idx: uint64, value: Element)
    requires validConfig(cfg)
    requires slice.WF'(old_data)
    requires Elt.marshallable(EltCfg(cfg), value)
    requires settable(cfg, slice.I(old_data), idx as nat, value)
    ensures |data| == |old_data|
    ensures forall i | 0 <= i < slice.start :: data[i] == old_data[i]
    ensures forall i | slice.end <= i < |data| as uint64 :: data[i] == old_data[i]
    ensures sets(cfg, slice.I(old_data), idx as nat, value, slice.I(data))


    // resizing
  predicate resizable(cfg: Config, data: mseq<byte>, newlen: nat)
    requires validConfig(cfg)

  predicate resizes(cfg: Config, data: mseq<byte>, newlen: nat, newdata: mseq<byte>)
    requires validConfig(cfg)
    requires resizable(cfg, data, newlen)
  {
    && |newdata| == |data|
    && lengthable(cfg, newdata)
    && length(cfg, newdata) == newlen
    && (forall i :: preservesEntry(cfg, data, i, newdata))
  }

  method Resizable(cfg: Config, data: mseq<byte>, newlen: uint64) returns (r: bool)
    requires validConfig(cfg)
    ensures r == resizable(cfg, data, newlen as nat)

  method Resize(cfg: Config, slice: Slice, linear inout data: mseq<byte>, newlen: uint64)
    requires validConfig(cfg)
    requires slice.WF'(old_data)
    requires resizable(cfg, slice.I(old_data), newlen as nat)
    ensures |data| == |old_data|
    ensures forall i | 0 <= i < slice.start :: data[i] == old_data[i]
    ensures forall i | slice.end <= i < |data| as uint64 :: data[i] == old_data[i]
    ensures resizes(cfg, slice.I(old_data), newlen as nat, slice.I(data))


    // append
  predicate wellFormed(cfg: Config, data: mseq<byte>)
    requires validConfig(cfg)
    ensures wellFormed(cfg, data) ==> lengthable(cfg, data)

  predicate appendable(cfg: Config, data: mseq<byte>, value: Element)
    requires validConfig(cfg)
    requires wellFormed(cfg, data)
    requires Elt.marshallable(EltCfg(cfg), value)

  predicate appends(cfg: Config, data: mseq<byte>, value: Element, newdata: mseq<byte>)
    requires validConfig(cfg)
    requires wellFormed(cfg, data)
    requires Elt.marshallable(EltCfg(cfg), value)
    requires appendable(cfg, data, value)
  {
    var oldlen := length(cfg, data);
    && |newdata| == |data|
    && lengthable(cfg, newdata)
    && length(cfg, newdata) == oldlen + 1
    && (forall i | i != oldlen :: preservesEntry(cfg, data, i, newdata))
    && gettable(cfg, newdata, oldlen)
    && eltParsable(cfg, newdata, oldlen)
    && getElt(cfg, newdata, oldlen) == value
    && wellFormed(cfg, newdata)
  }

  method WellFormed(cfg: Config, data: mseq<byte>) returns (w: bool)
    requires validConfig(cfg)
    ensures w == wellFormed(cfg, data)

  method Appendable(cfg: Config, data: mseq<byte>, value: Element) returns (r: bool)
    requires validConfig(cfg)
    requires wellFormed(cfg, data)
    requires Elt.marshallable(EltCfg(cfg), value)
    ensures r == appendable(cfg, data, value)

  method Append(cfg: Config, slice: Slice, linear inout data: mseq<byte>, value: Element)
    requires validConfig(cfg)
    requires slice.WF'(old_data)
    requires wellFormed(cfg, slice.I(old_data))
    requires Elt.marshallable(EltCfg(cfg), value)
    requires appendable(cfg, slice.I(old_data), value)
    ensures |data| == |old_data|
    ensures forall i | 0 <= i < slice.start :: data[i] == old_data[i]
    ensures forall i | slice.end <= i < |data| as uint64 :: data[i] == old_data[i]
    ensures appends(cfg, slice.I(old_data), value, slice.I(data))


  predicate gettableToLen(cfg: Config, data: mseq<byte>, len: nat)
    requires validConfig(cfg)
  {
    && (forall i | 0 <= i < len :: gettable(cfg, data, i))
  }

  predicate eltParsableToLen(cfg: Config, data: mseq<byte>, len: nat)
    requires validConfig(cfg)
    requires gettableToLen(cfg, data, len)
  {
    && (forall i | 0 <= i < len :: eltParsable(cfg, data, i))
  }
  
  predicate parsableToLen(cfg: Config, data: mseq<byte>, len: uint64)
    requires validConfig(cfg)
  {
    && gettableToLen(cfg, data, len as nat)
    && eltParsableToLen(cfg, data, len as nat)
  }

  predicate parsable(cfg: Config, data: mseq<byte>)
  {
    && lengthable(cfg, data)
    && length(cfg, data) < Uint64UpperBound()
    && parsableToLen(cfg, data, length(cfg, data) as uint64)
  }

  function parseToLen(cfg: Config, data: mseq<byte>, len: uint64) : UnmarshalledType
    requires validConfig(cfg)
    requires parsableToLen(cfg, data, len)
  {
    var r: seq<Element> := seq(len as nat, i requires 0 <= i < len as nat => getElt(cfg, data, i));
    assert |r| < Uint64UpperBound();
    r
  }

  function parse(cfg: Config, data: mseq<byte>) : UnmarshalledType
  {
    parseToLen(cfg, data, length(cfg, data) as uint64)
  }

  method TryParse(cfg: Config, data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var olen := TryLength(cfg, data);
    if olen == None {
      return None;
    }
    var len := olen.value;
    if len == 0 {
      var empty: UnmarshalledType := [];
      return Some(empty);
    }

    // We get the first element by itself so we can call
    // seq_alloc_init below.
    var oelt := TryGetElt(cfg, data, 0);
    if oelt == None {
      return None;
    }
    linear var lresult := seq_alloc_init(len, oelt.value);

    var i: uint64 := 1;
    var parsing_failed := false;
    while i < len
      invariant i <= len
      invariant |lresult| == len as nat
      invariant forall j: nat | j < i as nat :: gettable(cfg, data, j)
      invariant forall j: nat | j < i as nat :: eltParsable(cfg, data, j)
      invariant forall j: nat | j < i as nat :: lresult[j] == getElt(cfg, data, j)
    {
      oelt := TryGetElt(cfg, data, i);
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
}

//////////////////////////////////////////////////////////////////////
// Common parts of implementation of marshalling a sequence of items
// that all have the same marshalled size.
//
// We omit the actual parsing and marshalling implementations so that
// we can use the optimized integer packing code.
//////////////////////////////////////////////////////////////////////

abstract module UniformSizedElementSeqMarshalling(elementMarshalling: Marshalling)
refines SeqMarshalling(elementMarshalling) {
  import opened Mathematics
  import Seq = Sequences
  import opened Math
  import NLarith

  type Config = Elt.Config

  predicate validConfig(cfg: Config) {
    && Elt.validConfig(cfg)
  }

  function method EltCfg(cfg: Config) : Elt.Config {
    cfg
  }

  function method UniformSize(cfg: Config) : uint64
    requires validConfig(cfg)
    ensures 0 < UniformSize(cfg)

  predicate lengthable(cfg: Config, data: mseq<byte>)
  {
    true
  }

  function slice_length(cfg: Config, slice: Slice) : nat
    requires validConfig(cfg)
    requires slice.WF()
  {
    NLarith.DivLe(|slice| as nat, UniformSize(cfg) as nat);
    |slice| as nat / UniformSize(cfg) as nat
  }

  function length(cfg: Config, data: mseq<byte>) : nat
    ensures slice_length(cfg, all(data))
         == length(cfg, data)
         <=  length(cfg, data) * UniformSize(cfg) as nat
         <= |data| as nat
  {
    NLarith.DivLe(|data| as nat, UniformSize(cfg) as nat);
    DivMulOrder(|data| as nat, UniformSize(cfg) as nat);
    assert (|data| as nat / UniformSize(cfg) as nat) * 1 == |data| as nat / UniformSize(cfg) as nat;
    if 1 < UniformSize(cfg) then
      PosMulPreservesLe(1, UniformSize(cfg) as nat, |data| as nat / UniformSize(cfg) as nat);
      |data| as nat / UniformSize(cfg) as nat
    else
      |data| as nat / UniformSize(cfg) as nat
  }

  method TryLength(cfg: Config, data: mseq<byte>) returns (olen: Option<uint64>)
  {
    NLarith.DivLe(|data| as nat, UniformSize(cfg) as nat);
    olen := Some(|data| as uint64 / UniformSize(cfg));
  }

  method Lengthable(cfg: Config, data: mseq<byte>) returns (l: bool)
  {
    l := true;
  }

  method Length(cfg: Config, data: mseq<byte>) returns (len: uint64)
    ensures len as nat == length(cfg, data)
  {
    NLarith.DivLe(|data| as nat, UniformSize(cfg) as nat);
    len := |data| as uint64 / UniformSize(cfg);
  }

  lemma index_bounds_facts(cfg: Config, slice: Slice, idx: nat)
    requires validConfig(cfg)
    requires slice.WF()
    requires idx < |slice| as nat / UniformSize(cfg) as nat
    ensures 0 <=  idx * UniformSize(cfg) as nat
              <  idx * UniformSize(cfg) as nat + UniformSize(cfg) as nat
              == (idx + 1) * UniformSize(cfg) as nat
              <=  |slice| as nat
  {
    NatMulNatIsNat(idx, UniformSize(cfg) as nat);
    PosMulPreservesOrder(idx, idx + 1, UniformSize(cfg) as nat);
    NLarith.DistributeLeft(idx, 1, UniformSize(cfg) as nat);
    DivMulOrder(|slice| as nat, UniformSize(cfg) as nat);
    if idx + 1 < slice_length(cfg, slice) as nat {
      PosMulPreservesOrder(idx + 1, slice_length(cfg, slice), UniformSize(cfg) as nat);
    }
  }

  predicate gettable(cfg: Config, data: mseq<byte>, idx: nat) {
    idx < length(cfg, data)
  }

  function get(cfg: Config, slice: Slice, data: mseq<byte>, idx: nat) : (eslice: Slice)
    ensures |eslice| == UniformSize(cfg)
  {
    index_bounds_facts(cfg, slice, idx as nat);
    slice.sub(idx as uint64 * UniformSize(cfg), idx as uint64 * UniformSize(cfg) + UniformSize(cfg))
  }

  method TryGet(cfg: Config, slice: Slice, data: mseq<byte>, idx: uint64) returns (oeslice: Option<Slice>)
  {
    var len := Length(cfg, slice.I(data));
    if idx < len {
      index_bounds_facts(cfg, slice, idx as nat);
      oeslice := Some(slice.sub(idx * UniformSize(cfg), idx * UniformSize(cfg) + UniformSize(cfg)));
    } else {
      oeslice := None;
    }
  }

  method Gettable(cfg: Config, data: mseq<byte>, idx: uint64) returns (g: bool)
  {
    var len := Length(cfg, data);
    g := idx < len;
  }

  method Get(cfg: Config, slice: Slice, data: mseq<byte>, idx: uint64) returns (eslice: Slice)
  {
    index_bounds_facts(cfg, slice, idx as nat);
    eslice := slice.sub(idx * UniformSize(cfg), idx * UniformSize(cfg) + UniformSize(cfg));
  }

  predicate settable(cfg: Config, data: mseq<byte>, idx: nat, value: Element) {
    && idx < length(cfg, data)
    && Elt.marshallable(EltCfg(cfg), value)
    && Elt.size(EltCfg(cfg), value) == UniformSize(cfg)
  }

  method Settable(cfg: Config, data: mseq<byte>, idx: uint64, value: Element) returns (s: bool)
  {
    var len := Length(cfg, data);
    var sz := Elt.Size(EltCfg(cfg), value);
    return idx < len && sz == UniformSize(cfg);
  }

  method Set(cfg: Config, slice: Slice, linear inout data: mseq<byte>, idx: uint64, value: Element)
  {
    index_bounds_facts(cfg, slice, idx as nat);

    var newend := Elt.Marshall(EltCfg(cfg), value, inout data, slice.start + idx * UniformSize(cfg));

    forall i: nat | i != idx as nat && gettable(cfg, slice.I(old_data), i)
      ensures getData(cfg, slice.I(data), i) == getData(cfg, slice.I(old_data), i)
    {
      index_bounds_facts(cfg, slice, i);

      Seq.lemma_seq_slice_slice(data,
        slice.start as nat,
        slice.end as nat,
        i * UniformSize(cfg) as nat,
        i * UniformSize(cfg) as nat + UniformSize(cfg) as nat);
      Seq.lemma_seq_slice_slice(old_data,
        slice.start as nat,
        slice.end as nat,
        i * UniformSize(cfg) as nat,
        i * UniformSize(cfg) as nat + UniformSize(cfg) as nat);

      if i < idx as nat {
        NLarith.MulPreservesLe(i + 1, idx as nat, UniformSize(cfg) as nat);
      } else {
        NLarith.MulPreservesLe(idx as nat + 1, i, UniformSize(cfg) as nat);
      }
      assert getData(cfg, slice.I(data), i) == getData(cfg, slice.I(old_data), i);
    }

    Seq.lemma_seq_slice_slice(data,
      slice.start as nat,
      slice.end as nat,
      idx as nat * UniformSize(cfg) as nat,
      idx as nat * UniformSize(cfg) as nat + UniformSize(cfg) as nat);
  }

  predicate resizable(cfg: Config, data: mseq<byte>, newlen: nat) {
    false
  }

  method Resizable(cfg: Config, data: mseq<byte>, newlen: uint64) returns (r: bool)
  {
    return false;
  }

  method Resize(cfg: Config, slice: Slice, linear inout data: mseq<byte>, newlen: uint64)
  {
    // This function requires false and hence cannot be called.
  }

  predicate marshallable(cfg: Config, value: UnmarshalledType)
  {
    && (forall i | 0 <= i < |value| :: Elt.marshallable(EltCfg(cfg), value[i]))
    && (forall i | 0 <= i < |value| :: Elt.size(EltCfg(cfg), value[i]) == UniformSize(cfg))
    && |value| * UniformSize(cfg) as nat < Uint64UpperBound()
  }

  lemma marshallable_prefix(cfg: Config, value: UnmarshalledType, len: nat)
    requires validConfig(cfg)
    requires marshallable(cfg, value)
    requires len <= |value|
    ensures marshallable(cfg, value[..len])

  function size(cfg: Config, value: UnmarshalledType) : uint64
  {
    NatMulNatIsNat(|value|, UniformSize(cfg) as nat);
    |value| as uint64 * UniformSize(cfg)
  }

  method Size(cfg: Config, value: UnmarshalledType) returns (sz: uint64)
  {
    sz := NLarith.Uint64Mult(|value| as uint64, UniformSize(cfg));
  }

  lemma parsing_extend(cfg: Config, data: mseq<byte>, edata: mseq<byte>)
    requires validConfig(cfg)
    requires parsable(cfg, data)
    requires |data| == length(cfg, data) * UniformSize(cfg) as nat
    requires Elt.parsable(EltCfg(cfg), edata)
    requires |edata| == UniformSize(cfg) as nat
    requires |data + edata| < Uint64UpperBound()
    ensures parsable(cfg, data + edata)
    ensures parse(cfg, data + edata) == parse(cfg, data) + [ Elt.parse(EltCfg(cfg), edata) ]
  {
    var extension := data + edata;
    lemma_div_ind(|data|, UniformSize(cfg) as nat);
    forall idx | 0 <= idx < length(cfg, data)
      ensures getData(cfg, extension, idx) == getData(cfg, data, idx);
      ensures eltParsable(cfg, extension, idx)
    {
      assert eltParsable(cfg, data, idx);
      index_bounds_facts(cfg, all(data), idx);
      Seq.lemma_seq_slice_slice(extension, 0, |data|, idx * UniformSize(cfg) as nat, idx * UniformSize(cfg) as nat + UniformSize(cfg) as nat);
    }
    assert getData(cfg, extension, length(cfg, data)) == edata;
    assert parse(cfg, extension)[..length(cfg, data)] == parse(cfg, data);
  }

  method Marshall(cfg: Config, value: UnmarshalledType, linear inout data: mseq<byte>, start: uint64)
    returns (end: uint64)
  {
    var i: uint64 := 0;
    end := start;

    forall l | 0 <= l < |value|
      ensures marshallable(cfg, value[..l])
    {
      NLarith.MulPreservesLe(l, |value|, UniformSize(cfg) as nat);
    }

    while i < |value| as uint64
      invariant i <= |value| as uint64
      invariant |data| as nat == |old_data|
      invariant end as nat == start as nat + size(cfg, value[..i]) as nat <= |data| as nat
      invariant forall j | 0 <= j < start :: data[j] == old_data[j]
      invariant forall j | end as nat <= j < |old_data| :: data[j] == old_data[j]
      invariant parsable(cfg, data[start..end])
      invariant parse(cfg, data[start..end]) == value[..i]
    {
      ghost var oldend := end;
      ghost var olddata := data[start..end];
      if i as nat + 1 < |value| {
        PosMulPreservesOrder(i as nat + 1, |value|, UniformSize(cfg) as nat);
      }

      NLarith.DistributeLeft(i as nat, 1, UniformSize(cfg) as nat);
      end := Elt.Marshall(EltCfg(cfg), value[i], inout data, end);
      i := i + 1;

      assert data[start..oldend] == olddata;
      parsing_extend(cfg, data[start..oldend], data[oldend..end]);
      assert data[start..end] == data[start..oldend] + data[oldend..end];
      assert value[..i] == value[..i-1] + [ value[i-1] ];
    }
    assert value == value[..|value|];
  }
}

/////////////////////////////////////////////////////////////////
// Implementation for marshalling a sequence of packable integers
//
// We could just use the UniformSized marshalling code further below,
// but that would marshall each integer one at a time, which would
// (presumably) be slower.
/////////////////////////////////////////////////////////////////

module IntegerSeqMarshalling(Int: NativePackedInt)
refines UniformSizedElementSeqMarshalling(IntegerMarshalling(Int)) {

  function method UniformSize(cfg: Config) : uint64 {
    Int.Size()
  }
  
  lemma parse_is_unpack_Seq(cfg: Config, data: mseq<byte>)
    requires validConfig(cfg)
    requires parsable(cfg, data)
    ensures parse(cfg, data) == Int.unpack_Seq(data[..length(cfg, data) * Int.Size() as nat], length(cfg, data))
  {
    var len := length(cfg, data);
    var value := Int.unpack_Seq(data[..len * Int.Size() as nat], len);
    forall i | 0 <= i < |value|
      ensures value[i] == parse(cfg, data)[i]
    {
      index_bounds_facts(cfg, all(data), i);
      if i + 1 < len {
        PosMulPreservesOrder(i + 1, len, Int.Size() as nat);
      }
      Seq.lemma_seq_slice_slice(data, 0, Int.Size() as nat * len as nat, i * Int.Size() as nat, (i+1) * Int.Size() as nat);
      Seq.lemma_seq_slice_slice(data, i * UniformSize(cfg) as nat, (i + 1) * UniformSize(cfg) as nat, 0, Int.Size() as nat);
    }
  }

  method TryParse(cfg: Config, data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var len := Length(cfg, data);
    var value: mseq<Int.Integer> := Int.Cast_Seq(data, 0, len);
    ovalue := Some(value);
    assert parsable(cfg, data);
    parse_is_unpack_Seq(cfg, data);
  }

  method Parsable(cfg: Config, data: mseq<byte>) returns (p: bool)
  {
    return true;
  }

  method Parse(cfg: Config, data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var length := Length(cfg, data);
    value := Int.Cast_Seq(data, 0, length);
    parse_is_unpack_Seq(cfg, data);
  }

  method Marshall(cfg: Config, value: UnmarshalledType, linear inout data: mseq<byte>, start: uint64)
    returns (end: uint64)
  {
    Int.Pack_Seq_into_ByteSeq(value, inout data, start);
    var sz := Size(cfg, value);
    end := start + sz;

    assert parsable(cfg, data[start..end]);
    parse_is_unpack_Seq(cfg, data[start..end]);
    MulDivCancel(|value|, Int.Size() as nat);
    Seq.lemma_seq_slice_slice(data, start as nat, end as nat, 0, length(cfg, data[start..end]) * Int.Size() as nat);
  }
}

module Uint32SeqMarshalling refines IntegerSeqMarshalling(NativePackedUint32) {
}

module Uint64SeqMarshalling refines IntegerSeqMarshalling(NativePackedUint64) {
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
  import opened Mathematics
  import Seq = Sequences
  import NLarith

  function method sizeOfLengthField() : uint64 {
    LengthInt.Size()
  }

  datatype Config = Config(totalSize: uint64, lengthCfg: LengthMarshalling.Config, eltCfg: Elt.Config)

  predicate validConfig(cfg: Config) {
    && sizeOfLengthField() <= cfg.totalSize
    && LengthMarshalling.validConfig(cfg.lengthCfg)
    && Elt.validConfig(cfg.eltCfg)
  }

  function method EltCfg(cfg: Config) : Elt.Config {
    cfg.eltCfg
  }

  function method UniformSize(cfg: Config) : uint64
    requires validConfig(cfg)
    ensures 0 < UniformSize(cfg)

  function method maxLength(cfg: Config) : uint64
    requires validConfig(cfg)
  {
    NLarith.DivLe(cfg.totalSize as nat - sizeOfLengthField() as nat, UniformSize(cfg) as nat);
    (cfg.totalSize - sizeOfLengthField()) / UniformSize(cfg)
  }

  predicate lengthable(cfg: Config, data: mseq<byte>) {
    && cfg.totalSize as nat <= |data|
    && var ilen := LengthMarshalling.parse(cfg.lengthCfg, data[..sizeOfLengthField()]);
    && LengthInt.fitsInUint64(ilen)
  }

  function length(cfg: Config, data: mseq<byte>) : nat
    ensures sizeOfLengthField() as nat <= sizeOfLengthField() as nat + length(cfg, data) * UniformSize(cfg) as nat
  {
    var len := LengthInt.toInt(LengthMarshalling.parse(cfg.lengthCfg, data[..sizeOfLengthField()]));
    NatMulNatIsNat(len, UniformSize(cfg) as nat);
    NLarith.DivLe(|data| - sizeOfLengthField() as nat,  UniformSize(cfg) as nat);
    len
  }

  lemma index_bounds_facts(cfg: Config, idx: nat)
    requires validConfig(cfg)
    requires idx < maxLength(cfg) as nat
    ensures
         sizeOfLengthField() as nat
      <=  sizeOfLengthField() as nat + idx * UniformSize(cfg) as nat
      <  sizeOfLengthField() as nat + idx * UniformSize(cfg) as nat + UniformSize(cfg) as nat
      == sizeOfLengthField() as nat + (idx + 1) * UniformSize(cfg) as nat
      <=  sizeOfLengthField() as nat + maxLength(cfg) as nat * UniformSize(cfg) as nat
      <=  cfg.totalSize as nat
  {
    NatMulNatIsNat(idx, UniformSize(cfg) as nat);
    NLarith.DistributeLeft(idx, 1, UniformSize(cfg) as nat);
    DivMulOrder(cfg.totalSize as nat - sizeOfLengthField() as nat, UniformSize(cfg) as nat);
    if idx + 1 < maxLength(cfg) as nat {
      PosMulPreservesOrder(idx + 1, maxLength(cfg) as nat, UniformSize(cfg) as nat);
    }
  }

  method TryLength(cfg: Config, data: mseq<byte>) returns (olen: Option<uint64>)
  {
    if |data| as uint64 < cfg.totalSize {
      return None;
    }
    var l' := LengthMarshalling.Parse(cfg.lengthCfg, data[..sizeOfLengthField()]);
    if LengthInt.fitsInUint64(l') {
      return Some(LengthInt.toUint64(l'));
    } else {
      olen := None;
    }
  }

  predicate gettable(cfg: Config, data: mseq<byte>, idx: nat) {
    && lengthable(cfg, data)
    && idx < maxLength(cfg) as nat
  }

  function get(cfg: Config, slice: Slice, data: mseq<byte>, idx: nat) : (eslice: Slice)
  {
    index_bounds_facts(cfg, idx as nat);
    slice.sub(sizeOfLengthField() + idx as uint64 * UniformSize(cfg),
      sizeOfLengthField() + idx as uint64 * UniformSize(cfg) + UniformSize(cfg))
  }

  method TryGet(cfg: Config, slice: Slice, data: mseq<byte>, idx: uint64) returns (oeslice: Option<Slice>) {
    var olen := TryLength(cfg, slice.I(data));
    if olen == None {
      return None;
    }
    var mlen := maxLength(cfg);
    if idx < mlen {
      index_bounds_facts(cfg, idx as nat);
      NatMulNatIsNat(idx as nat, UniformSize(cfg) as nat);
      oeslice := Some(slice.sub(sizeOfLengthField() + idx * UniformSize(cfg), sizeOfLengthField() + idx * UniformSize(cfg) + UniformSize(cfg)));
    } else {
      oeslice := None;
    }
  }

  method Gettable(cfg: Config, data: mseq<byte>, idx: uint64) returns (g: bool) {
    var olen := TryLength(cfg, data);
    return olen != None && idx < maxLength(cfg);
  }

  method Get(cfg: Config, slice: Slice, data: mseq<byte>, idx: uint64) returns (eslice: Slice) {
    index_bounds_facts(cfg, idx as nat);
    NatMulNatIsNat(idx as nat, UniformSize(cfg) as nat);
    return slice.sub(sizeOfLengthField() + idx * UniformSize(cfg), sizeOfLengthField() + idx * UniformSize(cfg) + UniformSize(cfg));
  }

  lemma parsableLengthBounds(cfg: Config, data: mseq<byte>)
    requires validConfig(cfg)
    requires parsable(cfg, data)
    ensures length(cfg, data) <= maxLength(cfg) as nat
    ensures length(cfg, data) * UniformSize(cfg) as nat <= cfg.totalSize as nat - sizeOfLengthField() as nat
  {
    var len := length(cfg, data);
    if 0 < len {
      assert gettable(cfg, data, len - 1);
      index_bounds_facts(cfg, len-1);
    }
  }

  predicate settable(cfg: Config, data: mseq<byte>, idx: nat, value: Element) {
    && lengthable(cfg, data)
    && idx < maxLength(cfg) as nat
    && Elt.size(EltCfg(cfg), value) == UniformSize(cfg)
  }

  method Settable(cfg: Config, data: mseq<byte>, idx: uint64, value: Element) returns (s: bool)
  {
    var olen := TryLength(cfg, data);
    var sz := Elt.Size(EltCfg(cfg), value);
    return
      && olen != None
      && idx < maxLength(cfg)
      && sz == UniformSize(cfg);
  }

  method Set(cfg: Config, slice: Slice, linear inout data: mseq<byte>, idx: uint64, value: Element)
    ensures forall i | 0 <= i < slice.start as nat + sizeOfLengthField() as nat + idx as nat * UniformSize(cfg) as nat :: data[i] == old_data[i]
    ensures forall i | slice.start as nat + sizeOfLengthField() as nat + idx as nat * UniformSize(cfg) as nat + UniformSize(cfg) as nat <= i < |data| :: data[i] == old_data[i]
  {
    var newend;
    index_bounds_facts(cfg, idx as nat);
    NatMulNatIsNat(idx as nat, UniformSize(cfg) as nat);
    newend := Elt.Marshall(EltCfg(cfg), value, inout data, slice.start + sizeOfLengthField() + idx * UniformSize(cfg));

    assert slice.I(data)[..sizeOfLengthField()] == slice.I(old_data)[..sizeOfLengthField()];

    forall i: nat | i != idx as nat && gettable(cfg, slice.I(old_data), i)
      ensures getData(cfg, slice.I(data), i) == getData(cfg, slice.I(old_data), i)
    {
      index_bounds_facts(cfg, i);
      Seq.lemma_seq_slice_slice(data,
        slice.start as nat,
        slice.end as nat,
        sizeOfLengthField() as nat + i * UniformSize(cfg) as nat,
        sizeOfLengthField() as nat + i * UniformSize(cfg) as nat + UniformSize(cfg) as nat);
      Seq.lemma_seq_slice_slice(old_data,
        slice.start as nat,
        slice.end as nat,
        sizeOfLengthField() as nat + i * UniformSize(cfg) as nat,
        sizeOfLengthField() as nat + i * UniformSize(cfg) as nat + UniformSize(cfg) as nat);

      if i < idx as nat {
        NLarith.MulPreservesLe(i + 1, idx as nat, UniformSize(cfg) as nat);
        calc {
          getData(cfg, slice.I(data), i);
          data[slice.start..slice.end]
            [sizeOfLengthField() as nat + i * UniformSize(cfg) as nat..
             sizeOfLengthField() as nat + i * UniformSize(cfg) as nat + UniformSize(cfg) as nat];

          old_data[slice.start..slice.end]
            [sizeOfLengthField() as nat + i * UniformSize(cfg) as nat..
             sizeOfLengthField() as nat + i * UniformSize(cfg) as nat + UniformSize(cfg) as nat];
          getData(cfg, slice.I(old_data), i);
        }
      } else {
        NLarith.MulPreservesLe(idx as nat + 1, i, UniformSize(cfg) as nat);
      }
    }

    Seq.lemma_seq_slice_slice(data,
      slice.start as nat,
      slice.end as nat,
      sizeOfLengthField() as nat + idx as nat * UniformSize(cfg) as nat,
      sizeOfLengthField() as nat + idx as nat * UniformSize(cfg) as nat + UniformSize(cfg) as nat);
  }

  predicate resizable(cfg: Config, data: mseq<byte>, newlen: nat) {
    && lengthable(cfg, data)
    && newlen <= maxLength(cfg) as nat
    && LengthInt.fitsInInteger(newlen as uint64)
  }

  method Resizable(cfg: Config, data: mseq<byte>, newlen: uint64) returns (r: bool)
  {
    var l := Lengthable(cfg, data);
    return
      && l
      && newlen <= maxLength(cfg)
      && LengthInt.fitsInInteger(newlen);
  }

  method Resize(cfg: Config, slice: Slice, linear inout data: mseq<byte>, newlen: uint64)
    ensures forall i | slice.start + sizeOfLengthField() <= i < |data| as uint64 :: data[i] == old_data[i]
  {
    var newend := LengthMarshalling.Marshall(cfg.lengthCfg, LengthInt.fromUint64(newlen), inout data, slice.start);

    assert data[slice.start..slice.end][..LengthInt.Size()] == data[slice.start..slice.start + LengthInt.Size()];
    LengthInt.fromtoInverses();

    forall i: nat | gettable(cfg, slice.I(old_data), i)
      ensures getData(cfg, slice.I(data), i) == getData(cfg, slice.I(old_data), i)
    {
      index_bounds_facts(cfg, i);
      Seq.lemma_seq_slice_slice(data,
        slice.start as nat,
        slice.end as nat,
        sizeOfLengthField() as nat + i * UniformSize(cfg) as nat,
        sizeOfLengthField() as nat + i * UniformSize(cfg) as nat + UniformSize(cfg) as nat);
      Seq.lemma_seq_slice_slice(old_data,
        slice.start as nat,
        slice.end as nat,
        sizeOfLengthField() as nat + i * UniformSize(cfg) as nat,
        sizeOfLengthField() as nat + i * UniformSize(cfg) as nat + UniformSize(cfg) as nat);

        calc {
          getData(cfg, slice.I(data), i);
          data[slice.start..slice.end]
            [sizeOfLengthField() as nat + i * UniformSize(cfg) as nat..
            sizeOfLengthField() as nat + i * UniformSize(cfg) as nat + UniformSize(cfg) as nat];

          old_data[slice.start..slice.end]
            [sizeOfLengthField() as nat + i * UniformSize(cfg) as nat..
            sizeOfLengthField() as nat + i * UniformSize(cfg) as nat + UniformSize(cfg) as nat];
            getData(cfg, slice.I(old_data), i);
        }
    }
  }

  predicate wellFormed(cfg: Config, data: mseq<byte>) {
    lengthable(cfg, data)
  }

  predicate appendable(cfg: Config, data: mseq<byte>, value: Element) {
    && length(cfg, data) < maxLength(cfg) as nat
    && Elt.size(EltCfg(cfg), value) == UniformSize(cfg)
    && LengthInt.fitsInInteger(length(cfg, data) as uint64 + 1)
  }

  method WellFormed(cfg: Config, data: mseq<byte>) returns (w: bool) {
    w := Lengthable(cfg, data);
  }

  method Appendable(cfg: Config, data: mseq<byte>, value: Element) returns (r: bool) {
    var len := Length(cfg, data);
    var sz := Elt.Size(EltCfg(cfg), value);
    r := len < maxLength(cfg) && sz == UniformSize(cfg) && LengthInt.fitsInInteger(len + 1);
  }

  method Append(cfg: Config, slice: Slice, linear inout data: mseq<byte>, value: Element)
    ensures forall i | slice.start as nat + sizeOfLengthField() as nat + length(cfg, slice.I(data)) * UniformSize(cfg) as nat <= i < |data| :: data[i] == old_data[i]
  {
    var len := LLength(cfg, slice, data);
    Set(cfg, slice, inout data, len, value);
    ghost var middle := slice.I(data);
    Resize(cfg, slice, inout data, len + 1);

    forall i | i != len
      ensures preservesEntry(cfg, slice.I(old_data), i as nat, slice.I(data))
    {
      var iold_data := slice.I(old_data);
      var idata := slice.I(data);
      preservesEntryTransitive(cfg, iold_data, i as nat, middle, idata);
    }
    assert preservesEntry(cfg, middle, len as nat, slice.I(data));
    NLarith.DistributeLeft(length(cfg, slice.I(old_data)), 1, UniformSize(cfg) as nat);
  }

  predicate marshallable(cfg: Config, value: UnmarshalledType) {
    && (forall i | 0 <= i < |value| :: Elt.marshallable(EltCfg(cfg), value[i]))
    && (forall i | 0 <= i < |value| :: Elt.size(EltCfg(cfg), value[i]) == UniformSize(cfg))
    && LengthInt.fitsInInteger(|value| as uint64)
    && sizeOfLengthField() as nat + |value| * UniformSize(cfg) as nat <= cfg.totalSize as nat
  }

  function size(cfg: Config, value: UnmarshalledType) : uint64 {
    cfg.totalSize
  }

  method Size(cfg: Config, value: UnmarshalledType) returns (sz: uint64) {
    return cfg.totalSize;
  }

  method Marshall(cfg: Config, value: UnmarshalledType, linear inout data: mseq<byte>, start: uint64)
    returns (end: uint64)
  {
    end := start + cfg.totalSize;
    var slice := Slice(start, end);
    var ilen := LengthInt.fromUint64(|value| as uint64);
    var dummy := LengthMarshalling.Marshall(cfg.lengthCfg, ilen, inout data, start);

    LengthInt.fromtoInverses();
    Seq.lemma_seq_slice_slice(data,
      start as nat,
      end as nat,
      0,
      sizeOfLengthField() as nat);
    assert lengthable(cfg, data[start..end]);
    assert length(cfg, data[start..end]) == |value|;

    InequalityMoveDivisor(|value|, cfg.totalSize as nat - sizeOfLengthField() as nat, UniformSize(cfg) as nat);

    var i: uint64 := 0;
    while i < |value| as uint64
      invariant i <= |value| as uint64
      invariant |data| == |old_data|
      invariant forall j | 0 <= j < start :: data[j] == old_data[j]
      invariant forall j | end as nat <= j < |old_data| :: data[j] == old_data[j]
      invariant lengthable(cfg, data[start..end])
      invariant length(cfg, data[start..end]) == |value|
      invariant forall j | 0 <= j < i :: gettable(cfg, data[start..end], j as nat)
      invariant forall j | 0 <= j < i :: eltParsable(cfg, data[start..end], j as nat)
      invariant forall j | 0 <= j < i :: getElt(cfg, data[start..end], j as nat) == value[j]
      invariant forall j | 0 <= j < |value| :: settable(cfg, data[start..end], j, value[j])
    {
      ghost var olddata := data;
      Set(cfg, slice, inout data, i, value[i]);
      i := i + 1;
      assert forall j | 0 <= j < i - 1 :: preservesEntry(cfg, olddata[start..end], j as nat, data[start..end]);
    }
    assert value == value[..|value|];

  }
}


// Implementation for marshalling a sequence of packable integers

// We could just use the UniformSized marshalling code further below,
// but that would marshall each integer one at a time, which would
// (presumably) be slower.


module ResizableIntegerSeqMarshalling(lengthInt: NativePackedInt, Int: NativePackedInt)
refines ResizableUniformSizedElementSeqMarshalling(lengthInt, IntegerMarshalling(Int)) {

  function method UniformSize(cfg: Config) : uint64 {
    Int.Size()
  }

  lemma parse_is_unpack_Seq(cfg: Config, data: mseq<byte>)
    requires validConfig(cfg)
    requires parsable(cfg, data)
    ensures sizeOfLengthField() as nat + length(cfg, data) * Int.Size() as nat <= |data|
    ensures parse(cfg, data) == Int.unpack_Seq(data[sizeOfLengthField()..sizeOfLengthField() as nat + length(cfg, data) * Int.Size() as nat], length(cfg, data))
  {
    var len := length(cfg, data);
    if 0 < len {
      assert gettable(cfg, data, len - 1);
      index_bounds_facts(cfg, len - 1);
    }
    var value := Int.unpack_Seq(data[sizeOfLengthField()..sizeOfLengthField() as nat + len * Int.Size() as nat], len);
    forall i | 0 <= i < |value|
      ensures value[i] == parse(cfg, data)[i]
    {
      index_bounds_facts(cfg, i);
      if i + 1 < len {
        PosMulPreservesOrder(i + 1, len, Int.Size() as nat);
      }
      Seq.lemma_seq_slice_slice(data,
        sizeOfLengthField() as nat,
        sizeOfLengthField() as nat + Int.Size() as nat * len as nat,
        i * Int.Size() as nat,
        (i+1) * Int.Size() as nat);
      Seq.lemma_seq_slice_slice(data,
        sizeOfLengthField() as nat + i * Int.Size() as nat,
        sizeOfLengthField() as nat + (i + 1) * Int.Size() as nat,
        0,
        sizeOfLengthField() as nat);
    }
  }

  method TryParse(cfg: Config, data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var olen := TryLength(cfg, data);
    if olen.Some? && olen.value <= maxLength(cfg) {
      if 0 < olen.value {
        index_bounds_facts(cfg, olen.value as nat - 1);
      }
      var value: mseq<Int.Integer> := Int.Cast_Seq(data, sizeOfLengthField(), olen.value);
      ovalue := Some(value);
      parse_is_unpack_Seq(cfg, data);
    } else {
      ghost var ghosty := true;
      if ghosty && olen.Some? {
        assert !gettable(cfg, data, olen.value as nat - 1);
      }
      ovalue := None;
    }
  }

  method Parsable(cfg: Config, data: mseq<byte>) returns (p: bool)
  {
    var olen := TryLength(cfg, data);
    ghost var ghosty := true;
    if ghosty && olen.Some? && olen.value > maxLength(cfg) {
      assert !gettable(cfg, data, olen.value as nat - 1);
    }
    return olen.Some? && olen.value <= maxLength(cfg);
  }

  method Parse(cfg: Config, data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var len := Length(cfg, data);
    if 0 < len {
      assert gettable(cfg, data, len as nat - 1);
      index_bounds_facts(cfg, len as nat - 1);
    }
    value := Int.Cast_Seq(data, sizeOfLengthField(), len);
    parse_is_unpack_Seq(cfg, data);
  }

  method Marshall(cfg: Config, value: UnmarshalledType, linear inout data: mseq<byte>, start: uint64)
    returns (end: uint64)
  {
    var ilen := LengthInt.fromUint64(|value| as uint64);
    var dummy := LengthMarshalling.Marshall(cfg.lengthCfg, ilen, inout data, start);
    ghost var tmp := data[start..dummy];
    Int.Pack_Seq_into_ByteSeq(value, inout data, start + sizeOfLengthField());
    var sz := Size(cfg, value);
    end := start + sz;

    assert data[start..end][..sizeOfLengthField()] == tmp;
    LengthInt.fromtoInverses();
    Seq.lemma_seq_slice_slice(data,
      start as nat,
      end as nat,
      sizeOfLengthField() as nat,
      sizeOfLengthField() as nat + length(cfg, data[start..end]) * Int.Size() as nat);
    InequalityMoveDivisor(|value|, cfg.totalSize as nat - sizeOfLengthField() as nat, UniformSize(cfg) as nat);
    parse_is_unpack_Seq(cfg, data[start..end]);
  }
}

// module ResizableUint32SeqMarshalling refines ResizableIntegerSeqMarshalling(NativePackedUint64, NativePackedUint32) {
// }

// module ResizableUint64SeqMarshalling refines ResizableIntegerSeqMarshalling(NativePackedUint64, NativePackedUint64) {
// }


//////////////////////////////////////////////////////////////////////
// Implementation of marshalling a general sequence of items
//////////////////////////////////////////////////////////////////////

module VariableSizedElementSeqMarshalling(LengthInt: NativePackedInt, BoundaryInt: NativePackedInt, elt: Marshalling)
refines SeqMarshalling(elt) {
  import BoundarySeqMarshalling = ResizableIntegerSeqMarshalling(LengthInt, BoundaryInt)
  import opened Sequences
  import opened Mathematics
  import NLarith

  type LengthType = LengthInt.Integer
  type Boundary = BoundaryInt.Integer
  type BoundaryTable = mseq<Boundary>

  datatype Config = Config(bsmCfg: BoundarySeqMarshalling.Config, eltCfg: Elt.Config)

  predicate validConfig(cfg: Config) {
    && BoundarySeqMarshalling.validConfig(cfg.bsmCfg)
    && Elt.validConfig(cfg.eltCfg)
    && LengthInt.fitsInInteger(cfg.bsmCfg.totalSize)
  }

  function method EltCfg(cfg: Config) : Elt.Config
  {
    cfg.eltCfg
  }

  function method BSMCfg(cfg: Config) : BoundarySeqMarshalling.Config {
    cfg.bsmCfg
  }

  function method BoundaryCfg(cfg: Config) : BoundarySeqMarshalling.Elt.Config
    requires validConfig(cfg)
  {
    BoundarySeqMarshalling.EltCfg(BSMCfg(cfg))
  }

  function method totalSize(cfg: Config) : uint64
    requires validConfig(cfg)
  {
    BSMCfg(cfg).totalSize
  }

  function method sizeOfLengthField(cfg: Config) : uint64
    requires validConfig(cfg)
  {
    BoundarySeqMarshalling.sizeOfLengthField()
  }

  function method sizeOfBoundaryEntry(cfg: Config) : uint64
  {
    BoundaryInt.Size()
  }

  function method maxLength(cfg: Config) : uint64
    requires validConfig(cfg)
  {
    BoundarySeqMarshalling.maxLength(BSMCfg(cfg))
  }

  predicate lengthable(cfg: Config, data: mseq<byte>)
  {
    BoundarySeqMarshalling.lengthable(BSMCfg(cfg), data)
  }

  function length(cfg: Config, data: mseq<byte>) : nat
  {
    BoundarySeqMarshalling.length(BSMCfg(cfg), data)
  }

  method TryLength(cfg: Config, data: mseq<byte>) returns (olen: Option<uint64>)
    ensures olen.Some? ==> olen.value as nat == length(cfg, data)
  {
    olen := BoundarySeqMarshalling.TryLength(BSMCfg(cfg), data);
  }

  method Lengthable(cfg: Config, data: mseq<byte>) returns (l: bool)
  {
    l := BoundarySeqMarshalling.Lengthable(BSMCfg(cfg), data);
  }

  method Length(cfg: Config, data: mseq<byte>) returns (len: uint64)
  {
    len := BoundarySeqMarshalling.Length(BSMCfg(cfg), data);
  }


  predicate BoundaryElementGettable(cfg: Config, data: mseq<byte>, i: nat)
    requires validConfig(cfg)
  {
    && BoundarySeqMarshalling.gettable(BSMCfg(cfg), data, i)
    && BoundarySeqMarshalling.Elt.parsable(BoundaryCfg(cfg), BoundarySeqMarshalling.getData(BSMCfg(cfg), data, i))
  }

  function ElementDataBegin(cfg: Config, data: mseq<byte>, i: nat) : int
    requires validConfig(cfg)
    requires BoundaryElementGettable(cfg, data, i)
  {
    BoundaryInt.toInt(BoundarySeqMarshalling.getElt(BSMCfg(cfg), data, i))
  }

  function ElementDataEnd(cfg: Config, data: mseq<byte>, i: nat) : int
    requires validConfig(cfg)
    requires 0 < i ==> BoundaryElementGettable(cfg, data, i-1)
  {
    if i == 0 then
      |data|
    else
      BoundaryInt.toInt(BoundarySeqMarshalling.getElt(BSMCfg(cfg), data, i - 1))
  }

  predicate gettable(cfg: Config, data: mseq<byte>, idx: nat)
  {
    && lengthable(cfg, data)
    && idx < length(cfg, data)
    && BoundaryElementGettable(cfg, data, idx)
    && (0 < idx ==> BoundaryElementGettable(cfg, data, idx-1))
    && 0 <= ElementDataBegin(cfg, data, idx) <= ElementDataEnd(cfg, data, idx) <= totalSize(cfg) as nat <= |data|
  }

  function get(cfg: Config, slice: Slice, data: mseq<byte>, idx: nat) : (eslice: Slice)
  {
    slice.sub(ElementDataBegin(cfg, slice.I(data), idx) as uint64, ElementDataEnd(cfg, slice.I(data), idx) as uint64)
  }

  method TryGet(cfg: Config, slice: Slice, data: mseq<byte>, idx: uint64) returns (oeslice: Option<Slice>)
  {
    var olen := TryLength(cfg, slice.I(data));
    if olen.Some? && idx < maxLength(cfg) && idx < olen.value {
      var istart := BoundarySeqMarshalling.GetElt(BSMCfg(cfg), slice.I(data), idx);
      if !BoundaryInt.fitsInUint64(istart) {
        return None;
      }
      var start := BoundaryInt.toUint64(istart);
      var end := |slice|;
      if 0 < idx {
        var iend := BoundarySeqMarshalling.GetElt(BSMCfg(cfg), slice.I(data), idx - 1);
        if !BoundaryInt.fitsInUint64(iend) {
          return None;
        }
        end := BoundaryInt.toUint64(iend);
      }
      if start <= end <= totalSize(cfg) {
        return Some(slice.sub(start, end));
      } else {
        return None;
      }
    } else {
      return None;
    }
  }

  method Get(cfg: Config, slice: Slice, data: mseq<byte>, idx: uint64) returns (eslice: Slice) {
    var len := Length(cfg, slice.I(data));
    var istart := BoundarySeqMarshalling.GetElt(BSMCfg(cfg), slice.I(data), idx);
    var start := BoundaryInt.toUint64(istart);
    var end := |slice|;
    if 0 < idx {
      var iend := BoundarySeqMarshalling.GetElt(BSMCfg(cfg), slice.I(data), idx - 1);
      end := BoundaryInt.toUint64(iend);
    }
    return slice.sub(start, end);
  }

  predicate settable(cfg: Config, data: mseq<byte>, idx: nat, value: Element) {
    false
  }

  method Settable(cfg: Config, data: mseq<byte>, idx: uint64, value: Element) returns (s: bool) {
    s := false;
  }

  method Set(cfg: Config, slice: Slice, linear inout data: mseq<byte>, idx: uint64, value: Element) {
    // Cannot be called
  }

  predicate resizable(cfg: Config, data: mseq<byte>, newlen: nat) {
    false
  }

  method Resizable(cfg: Config, data: mseq<byte>, newlen: uint64) returns (r: bool) {
    r := false;
  }

  method Resize(cfg: Config, slice: Slice, linear inout data: mseq<byte>, newlen: uint64) {
    // Cannot be called
  }

  function sizeOfTable(cfg: Config, len: nat) : nat
    requires validConfig(cfg)
  {
    NatMulNatIsNat(len, sizeOfBoundaryEntry(cfg) as nat);
    sizeOfLengthField(cfg) as nat + len * sizeOfBoundaryEntry(cfg) as nat
  }

  predicate tableable(cfg: Config, data: mseq<byte>)
    requires validConfig(cfg)
    ensures tableable(cfg, data) ==> lengthable(cfg, data)
    ensures tableable(cfg, data) ==> sizeOfTable(cfg, length(cfg, data)) <= totalSize(cfg) as nat
  {
    if BoundarySeqMarshalling.parsable(BSMCfg(cfg), data) then
      BoundarySeqMarshalling.parsableLengthBounds(BSMCfg(cfg), data);
      true
    else
      false
  }

  function btable(cfg: Config, data: mseq<byte>) : mseq<BoundaryInt.Integer>
    requires validConfig(cfg)
    requires tableable(cfg, data)
  {
    BoundarySeqMarshalling.parse(BSMCfg(cfg), data)
  }

  function table(cfg: Config, data: mseq<byte>) : mseq<int>
    requires validConfig(cfg)
    requires tableable(cfg, data)
  {
    var bt := btable(cfg, data);
    seq(|bt|, i requires 0 <= i < |bt| => BoundaryInt.toInt(bt[i]))
  }

  predicate validTable(cfg: Config, data: mseq<byte>)
    requires validConfig(cfg)
    requires tableable(cfg, data)
  {
    var t := table(cfg, data);
    && (forall i, j | 0 <= i <= j < |t| :: t[j] <= t[i])
    && (0 < |t| ==> t[0] <= totalSize(cfg) as nat)
    && (0 < |t| ==> sizeOfTable(cfg, |t|) <= Last(t))
  }

  predicate wellFormed(cfg: Config, data: mseq<byte>) {
    && tableable(cfg, data)
    && validTable(cfg, data)
  }

  function elementsStart(cfg: Config, data: mseq<byte>) : nat
    requires validConfig(cfg)
    requires tableable(cfg, data)
    requires validTable(cfg, data)
  {
    var t := table(cfg, data);
    if |t| == 0 then
      totalSize(cfg) as nat
    else
      Last(t)
  }
  function freeSpace(cfg: Config, data: mseq<byte>) : nat
    requires validConfig(cfg)
    requires tableable(cfg, data)
    requires validTable(cfg, data)
  {
    elementsStart(cfg, data) - sizeOfTable(cfg, length(cfg, data))
  }

  predicate appendable(cfg: Config, data: mseq<byte>, value: Element) {
    && BoundaryInt.Size() as nat + Elt.size(EltCfg(cfg), value) as nat <= freeSpace(cfg, data)
  }

  function appendOffset(cfg: Config, data: mseq<byte>, value: Element) : uint64
    requires validConfig(cfg)
    requires lengthable(cfg, data)
    requires wellFormed(cfg, data)
    requires Elt.marshallable(EltCfg(cfg), value)
    requires appendable(cfg, data, value)
  {
    var len := length(cfg, data);
    var sz := Elt.size(EltCfg(cfg), value);
    var ub :=
    if len == 0 then
      totalSize(cfg)
    else
      var iub := BoundarySeqMarshalling.getElt(BSMCfg(cfg), data, len - 1);
      BoundaryInt.toUint64(iub);
    ub - sz
  }

  lemma appendableImpliesBSMappendable(cfg: Config, data: mseq<byte>, value: Element)
    requires validConfig(cfg)
    requires wellFormed(cfg, data)
    requires Elt.marshallable(EltCfg(cfg), value)
    requires appendable(cfg, data, value)
    ensures length(cfg, data) + 1 < Uint64UpperBound()
    ensures BoundaryInt.fitsInInteger(length(cfg, data) as uint64 + 1)
    ensures BoundarySeqMarshalling.appendable(BSMCfg(cfg), data, BoundaryInt.fromUint64(appendOffset(cfg, data, value)))
  {
    var len := length(cfg, data);
    NLarith.DistributeLeft(len, 1, BoundaryInt.Size() as nat);
    NLarith.MulPreservesLe(1, BoundaryInt.Size() as nat, len);
    InequalityMoveDivisor(len + 1, totalSize(cfg) as nat - sizeOfLengthField(cfg) as nat, BoundaryInt.Size() as nat);
  }

  method WellFormed(cfg: Config, data: mseq<byte>) returns (w: bool) {
    var ot := BoundarySeqMarshalling.TryParse(BSMCfg(cfg), data);
    if ot == None {
      return false;
    }
    var tbl := ot.value;

    var len := |tbl| as uint64;
    if len == 0 {
      return true;
    }

    BoundarySeqMarshalling.parsableLengthBounds(BSMCfg(cfg), data);
    BoundarySeqMarshalling.index_bounds_facts(BSMCfg(cfg), len as nat - 1);
    var tbsz := sizeOfLengthField(cfg) + len * sizeOfBoundaryEntry(cfg);

    if !BoundaryInt.fitsInUint64(tbl[len-1]) || BoundaryInt.toUint64(tbl[len-1]) < tbsz {
      return false;
    }

    if !BoundaryInt.fitsInUint64(tbl[0]) || totalSize(cfg) < BoundaryInt.toUint64(tbl[0]) {
      return false;
    }

    var i := 0;
    while i < len - 1
      invariant 0 <= i < len
      invariant forall j | 0 <= j <= i :: BoundaryInt.fitsInUint64(tbl[j])
      invariant forall i', j' | 0 <= i' <= j' <= i :: BoundaryInt.toInt(tbl[j']) <= BoundaryInt.toInt(tbl[i'])
    {
      assert BoundaryInt.toInt(tbl[i]) == table(cfg, data)[i];
      assert BoundaryInt.toInt(tbl[i+1]) == table(cfg, data)[i+1];
      if !BoundaryInt.fitsInUint64(tbl[i+1]) {
        return false;
      }
      if BoundaryInt.toUint64(tbl[i]) < BoundaryInt.toUint64(tbl[i+1]) {
        return false;
      }
      i := i + 1;
    }

    return true;
  }

  method Appendable(cfg: Config, data: mseq<byte>, value: Element) returns (r: bool) {
    var len := Length(cfg, data);

    BoundarySeqMarshalling.parsableLengthBounds(BSMCfg(cfg), data);

    var tblsz := sizeOfLengthField(cfg) + len * sizeOfBoundaryEntry(cfg);
    var ub;
    if len == 0 {
      ub := totalSize(cfg);
    } else {
      var iub := BoundarySeqMarshalling.GetElt(BSMCfg(cfg), data, len - 1);
      ub := BoundaryInt.toUint64(iub);
    }
    var fs := ub - tblsz;
    var esz := Elt.Size(EltCfg(cfg), value);
    return BoundaryInt.Size() <= fs && esz <= fs - BoundaryInt.Size();
  }

  lemma tableIdentity(cfg: Config, data: mseq<byte>, newdata: mseq<byte>)
    requires validConfig(cfg)
    requires tableable(cfg, data)
    requires totalSize(cfg) as nat <= |newdata|
    requires newdata[..sizeOfTable(cfg, length(cfg, data))] == data[..sizeOfTable(cfg, length(cfg, data))]
    ensures tableable(cfg, newdata)
    ensures table(cfg, newdata) == table(cfg, data)
  {
    assert newdata[..sizeOfLengthField(cfg)] == data[..sizeOfLengthField(cfg)];
    var len := length(cfg, newdata);
    forall i | 0 <= i < len
      ensures BoundarySeqMarshalling.gettable(BSMCfg(cfg), newdata, i)
      ensures BoundarySeqMarshalling.getData(BSMCfg(cfg), newdata, i) == BoundarySeqMarshalling.getData(BSMCfg(cfg), data, i)
    {
      BoundarySeqMarshalling.parsableLengthBounds(BSMCfg(cfg), data);
      BoundarySeqMarshalling.index_bounds_facts(BSMCfg(cfg), i);
      PosMulPreservesLe(i+1, len, BoundaryInt.Size() as nat);
    }
  }

  lemma elementsIdentity(cfg: Config, data: mseq<byte>, newdata: mseq<byte>)
    requires validConfig(cfg)
    requires tableable(cfg, data)
    requires tableable(cfg, newdata)
    requires validTable(cfg, data)
    requires validTable(cfg, newdata)
    requires IsPrefix(table(cfg, data), table(cfg, newdata))
    requires newdata[elementsStart(cfg, data)..] == data[elementsStart(cfg, data)..];
    ensures forall i :: gettable(cfg, data, i) ==> gettable(cfg, newdata, i)
    ensures forall i | gettable(cfg, data, i) :: getData(cfg, newdata, i) == getData(cfg, data, i)
  {
    var dt := table(cfg, data);
    var nt := table(cfg, newdata);
    forall i: nat | gettable(cfg, data, i)
      ensures gettable(cfg, newdata, i)
      ensures getData(cfg, newdata, i) == getData(cfg, data, i)
    {
      var start := ElementDataBegin(cfg, data, i);
      var end := ElementDataEnd(cfg, data, i);
      reveal_IsPrefix();
      assert nt[..|dt|][i] == nt[i];
      if 0 < i {
        assert nt[..|dt|][i-1] == nt[i-1];
      }
    }
  }

  method Append(cfg: Config, slice: Slice, linear inout data: mseq<byte>, value: Element) {
    appendableImpliesBSMappendable(cfg, slice.I(data), value);
    var len := LLength(cfg, slice, data);
    var sz := Elt.Size(EltCfg(cfg), value);
    var ub;
    if len == 0 {
      ub := totalSize(cfg);
    } else {
      var iub := BoundarySeqMarshalling.LGetElt(BSMCfg(cfg), slice, data, len - 1);
      ub := BoundaryInt.toUint64(iub);
    }
    var start := ub - sz;
    var dummy := Elt.Marshall(EltCfg(cfg), value, inout data, slice.start + start);


    ghost var middle := slice.I(data);
    Seq.lemma_seq_slice_slice(data, slice.start as nat, slice.end as nat, 0, sizeOfTable(cfg, len as nat));
    Seq.lemma_seq_slice_slice(old_data, slice.start as nat, slice.end as nat, 0, sizeOfTable(cfg, len as nat));
    tableIdentity(cfg, slice.I(old_data), middle);
    assert IsPrefix(table(cfg, slice.I(old_data)), table(cfg, middle)) by {
      reveal_IsPrefix();
    }
    elementsIdentity(cfg, slice.I(old_data), middle);


    var istart := BoundaryInt.fromUint64(start);
    BoundarySeqMarshalling.Append(BSMCfg(cfg), slice, inout data, istart);

    ghost var t := table(cfg, middle);
    ghost var t' := table(cfg, slice.I(data));
    BoundaryInt.fromtoInverses();
    forall i | 0 <= i < |t|
      ensures t'[i] == t[i]
    {
      assert BoundarySeqMarshalling.preservesEntry(BSMCfg(cfg), middle, i, slice.I(data));
    }
    assert IsPrefix(table(cfg, middle), table(cfg, slice.I(data))) by {
      reveal_IsPrefix();
    }
    NLarith.DistributeLeft(|t|, 1, BoundaryInt.Size() as nat);
    elementsIdentity(cfg, middle, slice.I(data));

    assert ElementDataEnd(cfg, data, len) <= totalSize(cfg) as nat;
    assert gettable(cfg, slice.I(data), len as nat);
    assert eltParsable(cfg, slice.I(data), len as nat);
    assert getElt(cfg, slice.I(data), len as nat) == value;
  }
}
