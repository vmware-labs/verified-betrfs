include "MarshalledAccessors.i.dfy"
include "../Base/sequences.i.dfy"

abstract module Tuple2Marshalling refines Marshalling {
  import FstMarshalling : Marshalling
  import SndMarshalling : Marshalling
  import SizeMarshalling : IntegerMarshalling
  import Sequences

  type UnmarshalledType = (FstMarshalling.UnmarshalledType, SndMarshalling.UnmarshalledType)
  type SizeType = SizeMarshalling.UnmarshalledType

  // the tag contains the size of the first value of the pair
  function method getTagSize(): uint64
  {
    SizeMarshalling.Int.Size() as uint64
  }

  predicate parsable(data: mseq<byte>)
  {
    var tagSize := getTagSize() as int;
    && |data| >= tagSize
    && SizeMarshalling.parsable(data[..tagSize])
    && var fstSize := SizeMarshalling.Int.toInt(SizeMarshalling.parse(data[..tagSize]));
    && fstSize >= 0
    && |data| >= tagSize + fstSize
    && FstMarshalling.parsable(data[tagSize..tagSize + fstSize])
    && SndMarshalling.parsable(data[tagSize + fstSize..])
  }

  function parse(data: mseq<byte>) : UnmarshalledType
  {
    var tagSize := getTagSize() as int;
    var fstSize := SizeMarshalling.Int.toInt(SizeMarshalling.parse(data[..tagSize]));
    var fstValue := FstMarshalling.parse(data[tagSize..tagSize + fstSize]);
    var sndValue := SndMarshalling.parse(data[tagSize + fstSize..]);
    (fstValue, sndValue)
  }

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var tagSize := getTagSize();

    if tagSize > |data| as uint64 {
      return None;
    }

    var sizeOvalue := SizeMarshalling.TryParse(data[..tagSize]);
    
    if sizeOvalue.None? {
      return None;
    }

    if !SizeMarshalling.Int.fitsInUint64(sizeOvalue.value) {
      return None;
    }

    var fstSize := SizeMarshalling.Int.toUint64(sizeOvalue.value);

    if fstSize > |data| as uint64 - tagSize {
      return None;
    }

    var fstOvalue := FstMarshalling.TryParse(data[tagSize..tagSize + fstSize]);
    var sndOvalue := SndMarshalling.TryParse(data[tagSize + fstSize..]);
    if fstOvalue.Some? && sndOvalue.Some? {
      ovalue := Some((fstOvalue.value, sndOvalue.value));
    } else {
      ovalue := None;
    }
  }

  method Parsable(data: mseq<byte>) returns (p: bool)
  {
    var tagSize := getTagSize();

    if tagSize > |data| as uint64 {
      return false;
    }

    var sizeOvalue := SizeMarshalling.TryParse(data[..tagSize]);
    
    if sizeOvalue.None? {
      return false;
    }

    if !SizeMarshalling.Int.fitsInUint64(sizeOvalue.value) {
      return false;
    }

    var fstSize := SizeMarshalling.Int.toUint64(sizeOvalue.value);

    if fstSize > |data| as uint64 - tagSize {
      return false;
    }

    var fstParsable := FstMarshalling.Parsable(data[tagSize..tagSize + fstSize]);
    var sndParsable := SndMarshalling.Parsable(data[tagSize + fstSize..]);

    return fstParsable && sndParsable;
  }

  method Parse(data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var tagSize := getTagSize();
    var isize := SizeMarshalling.Parse(data[..tagSize]);
    var fstSize := SizeMarshalling.Int.toUint64(isize); 

    var fstValue := FstMarshalling.Parse(data[tagSize..tagSize + fstSize]);
    var sndValue := SndMarshalling.Parse(data[tagSize + fstSize..]);
    value := (fstValue, sndValue);
  }

  predicate marshallable(value: UnmarshalledType)
  {
    && var (fstValue, sndValue) := value;
    && FstMarshalling.marshallable(fstValue)
    && SndMarshalling.marshallable(sndValue)
    && var fstSize := FstMarshalling.size(fstValue);
    && SizeMarshalling.Int.MinValue() <= fstSize < SizeMarshalling.Int.UpperBound()
    && SizeMarshalling.marshallable(SizeMarshalling.Int.fromInt(fstSize))
  }

  function size(value: UnmarshalledType) : nat
  {
    var (fstValue, sndValue) := value;
    getTagSize() as nat + FstMarshalling.size(fstValue) + SndMarshalling.size(sndValue)
  }

  method Size(value: UnmarshalledType) returns (sz: uint64)
  {
    var (fstValue, sndValue) := value;
    var fstSz := FstMarshalling.Size(fstValue);
    var sndSz := SndMarshalling.Size(sndValue);
    sz := getTagSize() + fstSz + sndSz;
  }

  method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
    returns (linear newdata: mseq<byte>, end: uint64)
  {
    ghost var tagSize : uint64 := getTagSize();
    var (fstValue, sndValue) := value;
    var fstSz := FstMarshalling.Size(fstValue);

    newdata, end := SizeMarshalling.Marshall(SizeMarshalling.Int.fromUint64(fstSz), data, start);
    ghost var newdata1 :seq<byte>, end1 := newdata, end;

    newdata, end := FstMarshalling.Marshall(fstValue, newdata, end);
    ghost var newdata2 :seq<byte>, end2 := newdata, end;

    newdata, end := SndMarshalling.Marshall(sndValue, newdata, end);

    assert newdata1[start..end1] == newdata[start..end1];
    assert newdata2[end1..end2] == newdata[end1..end2];

    Sequences.lemma_seq_slice_slice(newdata, start as int, end as int, tagSize as int, end2 as int- start as int);
    assert newdata[start..end][tagSize..end2 - start] == newdata[end1..end2];

    ghost var size := SizeMarshalling.Int.toInt(SizeMarshalling.parse(newdata[start..end1]));
    SizeMarshalling.Int.fromtoInverses();

    assert newdata[start..end][..tagSize] == newdata[start..end1];
    assert size == fstSz as int;
  }

  method GetFst(data: mseq<byte>) returns (edata: mseq<byte>)
    requires parsable(data)
    ensures FstMarshalling.parsable(edata)
    ensures FstMarshalling.parse(edata) == parse(data).0
  {
    var tagSize := getTagSize();
    var isize := SizeMarshalling.Parse(data[..tagSize]);
    var fstSize := SizeMarshalling.Int.toUint64(isize); 

    edata := data[tagSize..tagSize + fstSize];
  }

  method GetSnd(data: mseq<byte>) returns (edata: mseq<byte>)
    requires parsable(data)
    ensures SndMarshalling.parsable(edata)
    ensures SndMarshalling.parse(edata) == parse(data).1
  {
    var tagSize := getTagSize();
    var isize := SizeMarshalling.Parse(data[..tagSize]);
    var fstSize := SizeMarshalling.Int.toUint64(isize); 

    edata := data[tagSize + fstSize..];
  }
}
