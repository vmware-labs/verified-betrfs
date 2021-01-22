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

abstract module Tuple3Marshalling refines Marshalling {
  import ElemMarshalling0 : Marshalling
  import ElemMarshalling1 : Marshalling
  import ElemMarshalling2 : Marshalling
  import TableMarshalling : IntegerSeqMarshalling
  import Sequences
  import BoundaryInt = TableMarshalling.Int

  type UnmarshalledType = (ElemMarshalling0.UnmarshalledType, ElemMarshalling1.UnmarshalledType, ElemMarshalling2.UnmarshalledType)

  type Boundary = BoundaryInt.Integer
  type BoundaryTable = mseq<Boundary>

  // datatype Structure = Structure(boundaries: mseq<Boundary>, elements: mseq<byte>)

  function method sizeOfBoundaryEntry() : uint64
  {
    TableMarshalling.Int.Size()
  }

  function method sizeOfTable() : nat
  {
    2 * TableMarshalling.Int.Size() as nat
  }

  predicate parsable(data: mseq<byte>)
  {
    && var tableEnd := sizeOfTable();
    && |data| >= tableEnd
    && TableMarshalling.parsable(data[..tableEnd])
    && var table :mseq<Boundary> := TableMarshalling.parse(data[..tableEnd]);

    && var end0 := BoundaryInt.toInt(table[0]);
    && tableEnd <= end0 <= |data|
    && ElemMarshalling0.parsable(data[tableEnd..end0])

    && var end1 := BoundaryInt.toInt(table[1]);
    && end0 <= end1 <= |data|
    && ElemMarshalling1.parsable(data[end0..end1])

    && ElemMarshalling2.parsable(data[end1..])
  }

  function parse(data: mseq<byte>) : UnmarshalledType
  {
    var tableEnd := sizeOfTable();
    var table :mseq<Boundary> := TableMarshalling.parse(data[..tableEnd]);
    var end0 :=  BoundaryInt.toInt(table[0]);
    var end1 :=  BoundaryInt.toInt(table[1]);
    var elem0 := ElemMarshalling0.parse(data[tableEnd..end0]);
    var elem1 := ElemMarshalling1.parse(data[end0..end1]);
    var elem2 := ElemMarshalling2.parse(data[end1..]);
    (elem0, elem1, elem2)
  }

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    assume sizeOfTable() < Uint64UpperBound();
    var tableEnd := sizeOfTable() as uint64;

    if tableEnd > |data| as uint64 {
      return None;
    }

    var tableOpt := TableMarshalling.TryParse(data[..tableEnd]);
    
    if tableOpt.None? {
      return None;
    }

    var table :mseq<Boundary> := tableOpt.value;
  
    if !TableMarshalling.Int.fitsInUint64(table[0]) {
      return None;
    }

    if !BoundaryInt.fitsInUint64(table[0]) 
      || !BoundaryInt.fitsInUint64(table[1]) {
      return None;
    }

    var end0 := BoundaryInt.toUint64(table[0]);
    var end1 := BoundaryInt.toUint64(table[1]);

    if end0 > |data| as uint64 || end0 < tableEnd {
      return None;
    }

    if end1 > |data| as uint64 || end1 < end0 {
      return None;
    }

    var elemOpt0 := ElemMarshalling0.TryParse(data[tableEnd..end0]);
    var elemOpt1 := ElemMarshalling1.TryParse(data[end0..end1]);
    var elemOpt2 := ElemMarshalling2.TryParse(data[end1..]);

    if elemOpt0.None? || elemOpt1.None? || elemOpt2.None? {
      return None;
    }

    return Some((elemOpt0.value, elemOpt1.value, elemOpt2.value));
  }

}