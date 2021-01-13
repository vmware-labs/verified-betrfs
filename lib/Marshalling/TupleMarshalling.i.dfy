include "MarshalledAccessors.i.dfy"
include "../Base/sequences.i.dfy"

abstract module Tuple2Marshalling refines Marshalling {
  import FstMarshalling : Marshalling
  import SndMarshalling : Marshalling
  import SizeMarshalling : IntegerMarshalling
  import Sequences

  type UnmarshalledType = (FstMarshalling.UnmarshalledType, SndMarshalling.UnmarshalledType)
  type SizeType = SizeMarshalling.UnmarshalledType

  function method fstSizeSize(): uint64
  {
    SizeMarshalling.Int.Size() as uint64
  }

  predicate parsable(data: mseq<byte>)
  {
    var fstSizeSize := fstSizeSize() as int;
    && |data| >= fstSizeSize
    && SizeMarshalling.parsable(data[..fstSizeSize])
    && var fstSize := SizeMarshalling.Int.toInt(SizeMarshalling.parse(data[..fstSizeSize]));
    && fstSize >= 0
    && |data| >= fstSizeSize + fstSize
    && FstMarshalling.parsable(data[fstSizeSize..fstSizeSize + fstSize])
    && SndMarshalling.parsable(data[fstSizeSize + fstSize..])
  }

  function parse(data: mseq<byte>) : UnmarshalledType
  {
    var fstSizeSize := fstSizeSize() as int;
    var size := SizeMarshalling.Int.toInt(SizeMarshalling.parse(data[..fstSizeSize]));
    var fstElm := FstMarshalling.parse(data[fstSizeSize..fstSizeSize + size]);
    var sndElm := SndMarshalling.parse(data[fstSizeSize + size..]);
    (fstElm, sndElm)
  }

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var fstSizeSize := fstSizeSize();

    if fstSizeSize > |data| as uint64 {
      return None;
    }

    var sizeOvalue := SizeMarshalling.TryParse(data[..fstSizeSize]);
    
    if sizeOvalue.None? {
      return None;
    }

    if !SizeMarshalling.Int.fitsInUint64(sizeOvalue.value) {
      return None;
    }

    var size := SizeMarshalling.Int.toUint64(sizeOvalue.value);

    if size > |data| as uint64 - fstSizeSize {
      return None;
    }

    var fstOvalue := FstMarshalling.TryParse(data[fstSizeSize..fstSizeSize + size]);
    var sndOvalue := SndMarshalling.TryParse(data[fstSizeSize + size..]);
    if fstOvalue.Some? && sndOvalue.Some? {
      ovalue := Some((fstOvalue.value, sndOvalue.value));
    } else {
      ovalue := None;
    }
  }

  method Parsable(data: mseq<byte>) returns (p: bool)
  {
    var fstSizeSize := fstSizeSize();

    if fstSizeSize > |data| as uint64 {
      return false;
    }

    var sizeOvalue := SizeMarshalling.TryParse(data[..fstSizeSize]);
    
    if sizeOvalue.None? {
      return false;
    }

    if !SizeMarshalling.Int.fitsInUint64(sizeOvalue.value) {
      return false;
    }

    var size := SizeMarshalling.Int.toUint64(sizeOvalue.value);

    if size > |data| as uint64 - fstSizeSize {
      return false;
    }

    var fstParsable := FstMarshalling.Parsable(data[fstSizeSize..fstSizeSize + size]);
    var sndParsable := SndMarshalling.Parsable(data[fstSizeSize + size..]);

    return fstParsable && sndParsable;
  }

  method Parse(data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var fstSizeSize := fstSizeSize();

    var isize := SizeMarshalling.Parse(data[..fstSizeSize]);
    var size := SizeMarshalling.Int.toUint64(isize);

    var fstValue := FstMarshalling.Parse(data[fstSizeSize..fstSizeSize + size]);
    var sndValue := SndMarshalling.Parse(data[fstSizeSize + size..]);
    value := (fstValue, sndValue);
  }

  predicate marshallable(value: UnmarshalledType)
  {
    && var (fstValue, sndValue) := value;
    && FstMarshalling.marshallable(fstValue)
    && SndMarshalling.marshallable(sndValue)
    && var size := FstMarshalling.size(fstValue);
    && SizeMarshalling.Int.MinValue() <= size < SizeMarshalling.Int.UpperBound()
    && SizeMarshalling.marshallable(SizeMarshalling.Int.fromInt(size))
  }

  function size(value: UnmarshalledType) : nat
  {
    var (fstValue, sndValue) := value;
    fstSizeSize() as nat + FstMarshalling.size(fstValue) + SndMarshalling.size(sndValue)
  }

  method Size(value: UnmarshalledType) returns (sz: uint64)
  {
    var (fstValue, sndValue) := value;
    var fstSz := FstMarshalling.Size(fstValue);
    var sndSz := SndMarshalling.Size(sndValue);
    sz := fstSizeSize() + fstSz + sndSz;
  }

  method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
    returns (linear newdata: mseq<byte>, end: uint64)
  {
    ghost var fstSzSz : uint64 := fstSizeSize();
    var (fstValue, sndValue) := value;
    var fstSz := FstMarshalling.Size(fstValue);

    newdata, end := SizeMarshalling.Marshall(SizeMarshalling.Int.fromUint64(fstSz), data, start);
    ghost var newdata1 :seq<byte>, end1 := newdata, end;

    newdata, end := FstMarshalling.Marshall(fstValue, newdata, end);
    ghost var newdata2 :seq<byte>, end2 := newdata, end;

    newdata, end := SndMarshalling.Marshall(sndValue, newdata, end);

    assert newdata1[start..end1] == newdata[start..end1];
    assert newdata2[end1..end2] == newdata[end1..end2];

    Sequences.lemma_seq_slice_slice(newdata, start as int, end as int, fstSzSz as int, end2 as int- start as int);
    assert newdata[start..end][fstSzSz..end2 - start] == newdata[end1.. end2];

    ghost var size := SizeMarshalling.Int.toInt(SizeMarshalling.parse(newdata[start..end1]));
    SizeMarshalling.Int.fromtoInverses();

    assert newdata[start..end][..fstSzSz] == newdata[start..end1];
    assert size == fstSz as int;
  }
}
