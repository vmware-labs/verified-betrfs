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

  function method SizeOfBoundaryEntry() : uint64
  {
    BoundaryInt.Size()
  }

  function method sizeOfTable() : nat
  {
    2 * SizeOfBoundaryEntry() as nat
  }

  predicate parsable(data: mseq<byte>)
  {
    && var tableSize := sizeOfTable();
    && tableSize < Uint64UpperBound()
    && |data| >= tableSize
    && TableMarshalling.parsable(data[..tableSize])
    && var table :mseq<Boundary> := TableMarshalling.parse(data[..tableSize]);

    && var bound0 := BoundaryInt.toInt(table[0]);
    && tableSize <= bound0 <= |data|
    && ElemMarshalling0.parsable(data[tableSize..bound0])

    && var bound1 := BoundaryInt.toInt(table[1]);
    && bound0 <= bound1 <= |data|
    && ElemMarshalling1.parsable(data[bound0..bound1])

    && ElemMarshalling2.parsable(data[bound1..])
  }

  function parse(data: mseq<byte>) : UnmarshalledType
  {
    var tableSize := sizeOfTable();
    var table :mseq<Boundary> := TableMarshalling.parse(data[..tableSize]);
    var bound0 := BoundaryInt.toInt(table[0]);
    var bound1 := BoundaryInt.toInt(table[1]);
    var elem0 := ElemMarshalling0.parse(data[tableSize..bound0]);
    var elem1 := ElemMarshalling1.parse(data[bound0..bound1]);
    var elem2 := ElemMarshalling2.parse(data[bound1..]);
    (elem0, elem1, elem2)
  }

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var entrySize := SizeOfBoundaryEntry();

    if entrySize >= 0x8000_0000_0000_0000 {
      return None;
    }

    var tableSize := entrySize * 2;

    if tableSize > |data| as uint64 {
      return None;
    }

    var tableOpt := TableMarshalling.TryParse(data[..tableSize]);
    
    if tableOpt.None? {
      return None;
    }

    var table :mseq<Boundary> := tableOpt.value;
  
    if !BoundaryInt.fitsInUint64(table[0]) 
      || !BoundaryInt.fitsInUint64(table[1]) {
      return None;
    }

    var bound0 := BoundaryInt.toUint64(table[0]);
    var bound1 := BoundaryInt.toUint64(table[1]);

    if bound0 > |data| as uint64 || bound0 < tableSize {
      return None;
    }

    if bound1 > |data| as uint64 || bound1 < bound0 {
      return None;
    }

    var elemOpt0 := ElemMarshalling0.TryParse(data[tableSize..bound0]);
    var elemOpt1 := ElemMarshalling1.TryParse(data[bound0..bound1]);
    var elemOpt2 := ElemMarshalling2.TryParse(data[bound1..]);

    if elemOpt0.None? || elemOpt1.None? || elemOpt2.None? {
      return None;
    }

    return Some((elemOpt0.value, elemOpt1.value, elemOpt2.value));
  }

  method Parsable(data: mseq<byte>) returns (p: bool)
  {
    var entrySize := SizeOfBoundaryEntry();

    if entrySize >= 0x8000_0000_0000_0000 {
      return false;
    }

    var tableSize := sizeOfTable() as uint64;

    if tableSize > |data| as uint64 {
      return false;
    }

    var tableOpt := TableMarshalling.TryParse(data[..tableSize]);
    
    if tableOpt.None? {
      return false;
    }

    var table :mseq<Boundary> := tableOpt.value;

    if !BoundaryInt.fitsInUint64(table[0]) 
      || !BoundaryInt.fitsInUint64(table[1]) {
      return false;
    }

    var bound0 := BoundaryInt.toUint64(table[0]);
    var bound1 := BoundaryInt.toUint64(table[1]);

    if bound0 > |data| as uint64 || bound0 < tableSize {
      return false;
    }

    if bound1 > |data| as uint64 || bound1 < bound0 {
      return false;
    }

    var elemParsable0 := ElemMarshalling0.Parsable(data[tableSize..bound0]);
    var elemParsable1 := ElemMarshalling1.Parsable(data[bound0..bound1]);
    var elemParsable2 := ElemMarshalling2.Parsable(data[bound1..]);

    if !elemParsable0 || !elemParsable1 || !elemParsable2 {
      return false;
    }

    return true;
  }

  method Parse(data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var tableSize := sizeOfTable() as uint64;
    var table :mseq<Boundary> := TableMarshalling.Parse(data[..tableSize]);
  
    var bound0 := BoundaryInt.toUint64(table[0]);
    var bound1 := BoundaryInt.toUint64(table[1]);

    var elem0 := ElemMarshalling0.Parse(data[tableSize..bound0]);
    var elem1 := ElemMarshalling1.Parse(data[bound0..bound1]);
    var elem2 := ElemMarshalling2.Parse(data[bound1..]);
    return (elem0, elem1, elem2);
  }

  predicate marshallable(value: UnmarshalledType)
  {
    && var (elem0, elem1, elem2) := value;
    && ElemMarshalling0.marshallable(elem0)
    && ElemMarshalling1.marshallable(elem1)
    && ElemMarshalling2.marshallable(elem2)
    && var tableSize := sizeOfTable();
    var size0 := ElemMarshalling0.size(elem0);
    var size1 := ElemMarshalling1.size(elem1);
    var bound0 := tableSize + size0;
    var bound1 := bound0 + size1;
    && BoundaryInt.MinValue() <= bound0 < BoundaryInt.UpperBound()
    && BoundaryInt.MinValue() <= bound1 < BoundaryInt.UpperBound()
    && var table := [BoundaryInt.fromInt(bound0), BoundaryInt.fromInt(bound1)];
    && TableMarshalling.marshallable(table)
  }

  function size(value: UnmarshalledType) : nat
  {
    var (elem0, elem1, elem2) := value;
    var tableSize := sizeOfTable();
    var size0 := ElemMarshalling0.size(elem0);
    var size1 := ElemMarshalling1.size(elem1);
    var size2 := ElemMarshalling2.size(elem2);
    tableSize + size0 + size1 + size2
  }

  method Size(value: UnmarshalledType) returns (sz: uint64)
  {
    var (elem0, elem1, elem2) := value;
    var tableSize := sizeOfTable() as uint64;
    var size0 := ElemMarshalling0.Size(elem0);
    var size1 := ElemMarshalling1.Size(elem1);
    var size2 := ElemMarshalling2.Size(elem2);
    sz := tableSize + size0 + size1 + size2;
  }

  method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
    returns (linear newdata: mseq<byte>, end: uint64)
  {
    var (elem0, elem1, elem2) := value;
    var tableSize := sizeOfTable() as uint64;

    var size0 := ElemMarshalling0.Size(elem0);
    var size1 := ElemMarshalling1.Size(elem1);

    var bound0 := tableSize + size0;
    var bound1 := bound0 + size1;

    var table := [BoundaryInt.fromUint64(bound0), BoundaryInt.fromUint64(bound1)];

    newdata, end := TableMarshalling.Marshall(table, data, start);
    ghost var newdata0 :seq<byte>, end0 := newdata, end;

    newdata, end := ElemMarshalling0.Marshall(elem0, newdata, end);
    ghost var newdata1 :seq<byte>, end1 := newdata, end;

    newdata, end := ElemMarshalling1.Marshall(elem1, newdata, end);
    ghost var newdata2 :seq<byte>, end2 := newdata, end;

    newdata, end := ElemMarshalling2.Marshall(elem2, newdata, end);

    assert BoundaryInt.toInt(table[0]) == bound0 as int 
      && BoundaryInt.toInt(table[1]) == bound1 as int by {
      BoundaryInt.fromtoInverses();
    }

    assert newdata[start..end][..tableSize] == newdata[start..end0] == newdata0[start..end0];
    assert TableMarshalling.parse(newdata[start..end0]) == table;
    
    assert newdata[start..end][tableSize..bound0] == newdata[end0..end1] ==  newdata1[end0..end1] by {
      Sequences.lemma_seq_slice_slice(newdata, start as int, end as int, tableSize as int, bound0 as int);
    }
    assert ElemMarshalling0.parse(newdata[end0..end1]) == elem0;

    assert newdata[start..end][bound0..bound1] == newdata[end1..end2] == newdata2[end1..end2] by {
      Sequences.lemma_seq_slice_slice(newdata, start as int, end as int, bound0 as int, bound1 as int);
    }
    assert ElemMarshalling1.parse(newdata[end1..end2]) == elem1;

    assert newdata[start..end][bound1..] == newdata[end2..end];
    assert ElemMarshalling2.parse(newdata[end2..end]) == elem2;
  }
}