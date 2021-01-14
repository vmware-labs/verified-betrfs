include "MarshalledAccessors.i.dfy"
include "../Base/sequences.i.dfy"

abstract module Tuple2Marshalling refines Marshalling {
  import FstMarshalling : Marshalling
  import SndMarshalling : Marshalling
  import OffsetMarshalling : IntegerMarshalling
  import Sequences

  type UnmarshalledType = (FstMarshalling.UnmarshalledType, SndMarshalling.UnmarshalledType)
  type SizeType = OffsetMarshalling.UnmarshalledType

  function method getTagEnd(): uint64
  {
    OffsetMarshalling.Int.Size() as uint64
  }

  predicate parsable(data: mseq<byte>)
  {
    var tagEnd := getTagEnd() as int;
    && |data| >= tagEnd
    && OffsetMarshalling.parsable(data[..tagEnd])
    && var fstEnd := OffsetMarshalling.Int.toInt(OffsetMarshalling.parse(data[..tagEnd]));
    && tagEnd <= fstEnd <= |data| 
    && FstMarshalling.parsable(data[tagEnd..fstEnd])
    && SndMarshalling.parsable(data[fstEnd..])
  }

  function parse(data: mseq<byte>) : UnmarshalledType
  {
    var tagEnd := getTagEnd() as int;
    var fstEnd := OffsetMarshalling.Int.toInt(OffsetMarshalling.parse(data[..tagEnd]));
    var fstValue := FstMarshalling.parse(data[tagEnd..fstEnd]);
    var sndValue := SndMarshalling.parse(data[fstEnd..]);
    (fstValue, sndValue)
  }

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var tagEnd := getTagEnd();

    if tagEnd > |data| as uint64 {
      return None;
    }

    var fstEndOpt := OffsetMarshalling.TryParse(data[..tagEnd]);
    
    if fstEndOpt.None? {
      return None;
    }

    if !OffsetMarshalling.Int.fitsInUint64(fstEndOpt.value) {
      return None;
    }

    var fstEnd := OffsetMarshalling.Int.toUint64(fstEndOpt.value);

    if fstEnd > |data| as uint64 || fstEnd < tagEnd {
      return None;
    }

    var fstOvalue := FstMarshalling.TryParse(data[tagEnd..fstEnd]);
    var sndOvalue := SndMarshalling.TryParse(data[fstEnd..]);
    if fstOvalue.Some? && sndOvalue.Some? {
      ovalue := Some((fstOvalue.value, sndOvalue.value));
    } else {
      ovalue := None;
    }
  }

  method Parsable(data: mseq<byte>) returns (p: bool)
  {
    var tagEnd := getTagEnd();

    if tagEnd > |data| as uint64 {
      return false;
    }

    var fstEndOpt := OffsetMarshalling.TryParse(data[..tagEnd]);
    
    if fstEndOpt.None? {
      return false;
    }

    if !OffsetMarshalling.Int.fitsInUint64(fstEndOpt.value) {
      return false;
    }

    var fstEnd := OffsetMarshalling.Int.toUint64(fstEndOpt.value);

    if fstEnd > |data| as uint64 || fstEnd < tagEnd {
      return false;
    }

    var fstParsable := FstMarshalling.Parsable(data[tagEnd..fstEnd]);
    var sndParsable := SndMarshalling.Parsable(data[fstEnd..]);

    return fstParsable && sndParsable;
  }

  method Parse(data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var tagEnd := getTagEnd();
    var isize := OffsetMarshalling.Parse(data[..tagEnd]);
    var fstEnd := OffsetMarshalling.Int.toUint64(isize); 

    var fstValue := FstMarshalling.Parse(data[tagEnd..fstEnd]);
    var sndValue := SndMarshalling.Parse(data[fstEnd..]);
    value := (fstValue, sndValue);
  }

  predicate marshallable(value: UnmarshalledType)
  {
    && var (fstValue, sndValue) := value;
    && FstMarshalling.marshallable(fstValue)
    && SndMarshalling.marshallable(sndValue)
    && var fstSize := FstMarshalling.size(fstValue); var tagEnd := getTagEnd();
    && OffsetMarshalling.Int.MinValue() <= tagEnd as int + fstSize < OffsetMarshalling.Int.UpperBound()
    && OffsetMarshalling.marshallable(OffsetMarshalling.Int.fromInt(fstSize))
  }

  function size(value: UnmarshalledType) : nat
  {
    var (fstValue, sndValue) := value;
    getTagEnd() as nat + FstMarshalling.size(fstValue) + SndMarshalling.size(sndValue)
  }

  method Size(value: UnmarshalledType) returns (sz: uint64)
  {
    var (fstValue, sndValue) := value;
    var fstSz := FstMarshalling.Size(fstValue);
    var sndSz := SndMarshalling.Size(sndValue);
    sz := getTagEnd() + fstSz + sndSz;
  }

  method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
    returns (linear newdata: mseq<byte>, end: uint64)
  {
    var (fstValue, sndValue) := value;
    var tagEnd : uint64 := getTagEnd();
    var fstSz := FstMarshalling.Size(fstValue);
    var fstEnd := tagEnd + fstSz;

    newdata, end := OffsetMarshalling.Marshall(OffsetMarshalling.Int.fromUint64(fstEnd), data, start);
    ghost var newdata1 :seq<byte>, end1 := newdata, end;

    newdata, end := FstMarshalling.Marshall(fstValue, newdata, end);
    ghost var newdata2 :seq<byte>, end2 := newdata, end;

    newdata, end := SndMarshalling.Marshall(sndValue, newdata, end);

    assert newdata1[start..end1] == newdata[start..end1];
    assert newdata2[end1..end2] == newdata[end1..end2];

    Sequences.lemma_seq_slice_slice(newdata, start as int, end as int, tagEnd as int, end2 as int- start as int);
    assert newdata[start..end][tagEnd..end2 - start] == newdata[end1..end2];

    ghost var size := OffsetMarshalling.Int.toInt(OffsetMarshalling.parse(newdata[start..end1]));
    OffsetMarshalling.Int.fromtoInverses();

    assert newdata[start..end][..tagEnd] == newdata[start..end1];
    assert size == fstEnd as int;
  }

  method GetFst(data: mseq<byte>) returns (edata: mseq<byte>)
    requires parsable(data)
    ensures FstMarshalling.parsable(edata)
    ensures FstMarshalling.parse(edata) == parse(data).0
  {
    var tagEnd := getTagEnd();
    var ifstEnd := OffsetMarshalling.Parse(data[..tagEnd]);
    var fstEnd := OffsetMarshalling.Int.toUint64(ifstEnd); 

    edata := data[tagEnd..fstEnd];
  }

  method GetSnd(data: mseq<byte>) returns (edata: mseq<byte>)
    requires parsable(data)
    ensures SndMarshalling.parsable(edata)
    ensures SndMarshalling.parse(edata) == parse(data).1
  {
    var tagEnd := getTagEnd();
    var ifstEnd := OffsetMarshalling.Parse(data[..tagEnd]);
    var fstEnd := OffsetMarshalling.Int.toUint64(ifstEnd); 

    edata := data[fstEnd..];
  }
}
