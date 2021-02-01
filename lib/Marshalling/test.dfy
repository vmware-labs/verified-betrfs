include "MarshalledAccessors.i.dfy"
include "../Base/sequences.i.dfy"

abstract module Tuple2Marshalling refines Marshalling {
  import TableMarshalling : IntegerSeqMarshalling
  import Sequences
  import BoundaryInt = TableMarshalling.Int
  import ElemMarshalling0 : Marshalling
  import ElemMarshalling1 : Marshalling

  type Boundary = BoundaryInt.Integer
  type BoundaryTable = mseq<Boundary>

  type UnmarshalledType = (ElemMarshalling0.UnmarshalledType, 
    ElemMarshalling1.UnmarshalledType)
    

  function method SizeOfBoundaryEntry() : uint64
  {
    BoundaryInt.Size()
  }

  function method sizeOfTable() : nat
  {
    1 * SizeOfBoundaryEntry() as nat
  }

  predicate parsable(data: mseq<byte>)
  {
    && var tableSize := sizeOfTable();
    && SizeOfBoundaryEntry() as int < Uint64UpperBound() / 1
    && |data| >= tableSize
    && TableMarshalling.parsable(data[..tableSize])
    && var table :mseq<Boundary> := TableMarshalling.parse(data[..tableSize]);

    && var bound0 := BoundaryInt.toInt(table[0]);
    && tableSize <= bound0 <= |data|
    && ElemMarshalling0.parsable(data[tableSize..bound0])
    
    && ElemMarshalling1.parsable(data[bound0..])
    
  }

  function parse(data: mseq<byte>) : UnmarshalledType
  {
    var tableSize := sizeOfTable();
    var table :mseq<Boundary> := TableMarshalling.parse(data[..tableSize]);

    var bound0 := BoundaryInt.toInt(table[0]);
    var elem0 := ElemMarshalling0.parse(data[tableSize..bound0]);
    
    var elem1 := ElemMarshalling1.parse(data[bound0..]);
    
    (elem0,
    elem1)
  }

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var entrySize := SizeOfBoundaryEntry();

    var tableSize := entrySize * 1;

    if tableSize > |data| as uint64 {
      return None;
    }

    var tableOpt := TableMarshalling.TryParse(data[..tableSize]);
    
    if tableOpt.None? {
      return None;
    }

    var table :mseq<Boundary> := tableOpt.value;
  
    if || !BoundaryInt.fitsInUint64(table[0])
    {
      return None;
    }

    var bound0 := BoundaryInt.toUint64(table[0]);


    if bound0 > |data| as uint64 || bound0 < tableSize {
      return None;
    }

    var elemOpt0 := ElemMarshalling0.TryParse(data[tableSize..bound0]);
    var elemOpt1 := ElemMarshalling1.TryParse(data[bound0..]);
    
    if || elemOpt0.None?
    || elemOpt1.None?
    {
      return None;
    }

    return Some((elemOpt0.value,
    elemOpt1.value));
  }

  method Parsable(data: mseq<byte>) returns (p: bool)
  {
    var entrySize := SizeOfBoundaryEntry();

    var tableSize := entrySize * 1;

    if tableSize > |data| as uint64 {
      return false;
    }

    var tableOpt := TableMarshalling.TryParse(data[..tableSize]);
    
    if tableOpt.None? {
      return false;
    }

    var table :mseq<Boundary> := tableOpt.value;
  
    if || !BoundaryInt.fitsInUint64(table[0])
    {
      return false;
    }

    var bound0 := BoundaryInt.toUint64(table[0]);


    if bound0 > |data| as uint64 || bound0 < tableSize {
      return false;
    }

    var elemParsable0 := ElemMarshalling0.Parsable(data[tableSize..bound0]);
    var elemParsable1 := ElemMarshalling1.Parsable(data[bound0..]);
    
    if || !elemParsable0
    || !elemParsable1
    {
      return false;
    }

    return true;
  }

  method Parse(data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var tableSize := sizeOfTable() as uint64;
    var table :mseq<Boundary> := TableMarshalling.Parse(data[..tableSize]);

    var bound0 := BoundaryInt.toUint64(table[0]);

    var elem0 := ElemMarshalling0.Parse(data[tableSize..bound0]);
    var elem1 := ElemMarshalling1.Parse(data[bound0..]);
    
    return (elem0,
    elem1);
  }

  predicate marshallable(value: UnmarshalledType)
  {
    && var entrySize := SizeOfBoundaryEntry();

    && var (elem0,elem1) := value;
    && ElemMarshalling0.marshallable(elem0)
    && ElemMarshalling1.marshallable(elem1)

    && var tableSize := sizeOfTable();
    var size0 := ElemMarshalling0.size(elem0);
    var bound0 := tableSize + size0;
    && BoundaryInt.MinValue() <= bound0 < BoundaryInt.UpperBound()
    && var table := [BoundaryInt.fromInt(bound0)];
    && TableMarshalling.marshallable(table)
  }

  function size(value: UnmarshalledType) : nat
  {
    var (elem0,elem1) := value;
    var tableSize := sizeOfTable();
    var size0 := ElemMarshalling0.size(elem0);
    var size1 := ElemMarshalling1.size(elem1);

    tableSize+size0+size1
  }

  method Size(value: UnmarshalledType) returns (sz: uint64)
  {
    var (elem0,elem1) := value;
    var tableSize := sizeOfTable() as uint64;
    var size0 := ElemMarshalling0.Size(elem0);
    var size1 := ElemMarshalling1.Size(elem1);

    sz := tableSize+size0+size1;
  }

  method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
    returns (linear newdata: mseq<byte>, end: uint64)
  {
    var (elem0,elem1) := value;

    var tableSize := sizeOfTable() as uint64;
    var size0 := ElemMarshalling0.Size(elem0);
    var bound0 := tableSize + size0;
    var table := [BoundaryInt.fromUint64(bound0)];

    newdata, end := TableMarshalling.Marshall(table, data, start);
    ghost var newdata0 :seq<byte>, end0 := newdata, end;
    newdata, end := ElemMarshalling0.Marshall(elem0, newdata, end);
    ghost var newdata1 :seq<byte>, end1 := newdata, end;
    newdata, end := ElemMarshalling1.Marshall(elem1, newdata, end);

    assert 
      && BoundaryInt.toInt(table[0]) == bound0 as int by {
      BoundaryInt.fromtoInverses();
    }

    assert newdata[start..end][..tableSize] == newdata[start..end0] == newdata0[start..end0];
    // assert TableMarshalling.parse(newdata[start..end0]) == table;
    
    assert newdata[start..end][tableSize..bound0] == newdata[end0..end1] == newdata1[end0..end1] by {
      Sequences.lemma_seq_slice_slice(newdata, start as int, end as int, tableSize as int, bound0 as int);
    }
    // assert ElemMarshalling0.parse(newdata[end0..end1]) == elem0;



    assert newdata[start..end][bound0..] == newdata[end1..end];
    // assert ElemMarshalling1.parse(newdata[end1..end]) == elem1;
  }
}
