include "MarshalledAccessors.i.dfy"

abstract module Tuple2Marshalling refines Marshalling {
  import FstMarshalling : Marshalling
  import SndMarshalling : Marshalling
  import SizeMarshalling : IntegerMarshalling

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
    && var size := SizeMarshalling.Int.toInt(SizeMarshalling.parse(data[..fstSizeSize]));
    && size >= 0
    && |data| >= fstSizeSize + size
    && FstMarshalling.parsable(data[fstSizeSize..fstSizeSize + size])
    && SndMarshalling.parsable(data[fstSizeSize + size..])
  }

  function parse(data: mseq<byte>) : UnmarshalledType
    // requires parsable(data)
  {
    var fstSizeSize := fstSizeSize() as int;
    var size := SizeMarshalling.Int.toInt(SizeMarshalling.parse(data[..fstSizeSize]));
    var fstElm := FstMarshalling.parse(data[fstSizeSize..fstSizeSize + size]);
    var sndElm := SndMarshalling.parse(data[fstSizeSize + size..]);
    (fstElm, sndElm)
  }

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
    // ensures parsable(data) <==> ovalue.Some?
    // ensures parsable(data) ==> ovalue.value == parse(data)
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
    // ensures p == parsable(data)
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
    // requires parsable(data)
    // ensures value == parse(data)
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
    // requires marshallable(value)
    // requires size(value) < Uint64UpperBound()
    // ensures sz as nat == size(value)
  {
    var (fstValue, sndValue) := value;
    var fstSz := FstMarshalling.Size(fstValue);
    var sndSz := SndMarshalling.Size(sndValue);
    sz := fstSizeSize() + fstSz + sndSz;
  }

  lemma seqSliceSlice(s: mseq<byte>, a: uint64, b: uint64, c: uint64, d: uint64)
    requires a <= b <= |s| as uint64;
    requires c <= d <= b - a;
    requires a + d <= b;
    ensures s[a..b][c..d] == s[a + c..a + d];
  {
    assert s[a..b] == s[a..b];
    assert s[a..b][c..] == s[a + c..b];
    assert s[a..b][c..d] == s[a + c..a + d];
  }

  method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
    returns (linear newdata: mseq<byte>, end: uint64)
  {
    ghost var fstSzSz : uint64 := fstSizeSize();
    var (fstValue, sndValue) := value;
    var fstSz := FstMarshalling.Size(fstValue);
    newdata, end := SizeMarshalling.Marshall(SizeMarshalling.Int.fromUint64(fstSz), data, start);
    ghost var newdata1 :seq<byte> := newdata;
    ghost var end1 := end;

    newdata, end := FstMarshalling.Marshall(fstValue, newdata, end);
    ghost var newdata2 :seq<byte> := newdata;
    ghost var end2 := end;

    newdata, end := SndMarshalling.Marshall(sndValue, newdata, end);

    assert start + fstSzSz == end1;
    assert end1 + fstSz == end2;

    assert newdata1[start..end1] == newdata[start..end1];
    assert newdata2[end1..end2] == newdata[end1..end2];

    // calc == {
    //   newdata[start..end][fstSzSz..end2 - start];
    //   {
    //     assert end1 + fstSz == end2;
    //   }
    //   newdata[start..end][fstSzSz.. end1 + fstSz - start];
    //   {
    //     assert start + fstSzSz == end1;
    //   }
    //   newdata[start..end][fstSzSz..fstSzSz + fstSz];
    //   {
    //     // assume start + fstSzSz + fstSz < end;
    //   }
    //   newdata[start + fstSzSz..start + fstSzSz + fstSz];
    // }

    seqSliceSlice(newdata, start, end, fstSzSz, end2 - start);
    assert newdata[start..end][fstSzSz..end2 - start] == newdata[end1.. end2];
    // assume newdata[start..end][fstSzSz..end2 - start] == newdata[end1 .. end2];

    ghost var size := SizeMarshalling.Int.toInt(SizeMarshalling.parse(newdata[start..end1]));
    SizeMarshalling.Int.fromtoInverses();

    assert newdata[start..end][..fstSzSz] == newdata[start..end1];
    assert size == fstSz as int;
  }
}
