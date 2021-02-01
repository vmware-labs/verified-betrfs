include "MarshalledAccessors.i.dfy"
include "../Base/sequences.i.dfy"

abstract module Tuple4Marshalling refines Marshalling {
  import TableMarshalling : IntegerSeqMarshalling
  import Sequences
  import BoundaryInt = TableMarshalling.Int
  import ElemMarshalling0 : Marshalling
  import ElemMarshalling1 : Marshalling
  import ElemMarshalling2 : Marshalling
  import ElemMarshalling3 : Marshalling

  type Boundary = BoundaryInt.Integer
  type BoundaryTable = mseq<Boundary>

  type UnmarshalledType = (ElemMarshalling0.UnmarshalledType, 
    ElemMarshalling1.UnmarshalledType, 
    ElemMarshalling2.UnmarshalledType, 
    ElemMarshalling3.UnmarshalledType)
    

  function method SizeOfBoundaryEntry() : uint64
  {
    BoundaryInt.Size()
  }

  function method sizeOfTable() : nat
  {
    3 * SizeOfBoundaryEntry() as nat
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
    
    && var bound2 := BoundaryInt.toInt(table[2]);
    && bound1 <= bound2 <= |data|
    && ElemMarshalling2.parsable(data[bound1..bound2])
    
    && ElemMarshalling3.parsable(data[bound2..])
    
  }

  function parse(data: mseq<byte>) : UnmarshalledType
  {
    var tableSize := sizeOfTable();
    var table :mseq<Boundary> := TableMarshalling.parse(data[..tableSize]);

    var bound0 := BoundaryInt.toInt(table[0]);
    var elem0 := ElemMarshalling0.parse(data[tableSize..bound0]);
    
    var bound1 := BoundaryInt.toInt(table[1]);
    var elem1 := ElemMarshalling1.parse(data[bound0..bound1]);
    
    var bound2 := BoundaryInt.toInt(table[2]);
    var elem2 := ElemMarshalling2.parse(data[bound1..bound2]);
    
    var elem3 := ElemMarshalling3.parse(data[bound2..]);
    
    (elem0,
    elem1,
    elem2,
    elem3)
  }

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var entrySize := SizeOfBoundaryEntry();

    if entrySize >= 0x5555555555555555 {
      return None;
    }

    var tableSize := entrySize * 3;

    if tableSize > |data| as uint64 {
      return None;
    }

    var tableOpt := TableMarshalling.TryParse(data[..tableSize]);
    
    if tableOpt.None? {
      return None;
    }

    var table :mseq<Boundary> := tableOpt.value;
  
    if || !BoundaryInt.fitsInUint64(table[0])
    || !BoundaryInt.fitsInUint64(table[1])
    || !BoundaryInt.fitsInUint64(table[2])
    {
      return None;
    }

    var bound0 := BoundaryInt.toUint64(table[0]);
    var bound1 := BoundaryInt.toUint64(table[1]);
    var bound2 := BoundaryInt.toUint64(table[2]);


    if bound0 > |data| as uint64 || bound0 < tableSize {
      return None;
    }

    if bound1 > |data| as uint64 || bound1 < bound0 {
      return None;
    }
    

    if bound2 > |data| as uint64 || bound2 < bound1 {
      return None;
    }
    

    var elemOpt0 := ElemMarshalling0.TryParse(data[tableSize..bound0]);
    var elemOpt1 := ElemMarshalling1.TryParse(data[bound0..bound1]);
    var elemOpt2 := ElemMarshalling2.TryParse(data[bound1..bound2]);
    var elemOpt3 := ElemMarshalling3.TryParse(data[bound2..]);
    
    if || elemOpt0.None?
    || elemOpt1.None?
    || elemOpt2.None?
    || elemOpt3.None?
    {
      return None;
    }

    return Some((elemOpt0.value,
    elemOpt1.value,
    elemOpt2.value,
    elemOpt3.value));
  }

  method Parsable(data: mseq<byte>) returns (p: bool)
  {
    var entrySize := SizeOfBoundaryEntry();

    if entrySize >= 0x5555555555555555 {
      return false;
    }

    var tableSize := entrySize * 3;

    if tableSize > |data| as uint64 {
      return false;
    }

    var tableOpt := TableMarshalling.TryParse(data[..tableSize]);
    
    if tableOpt.None? {
      return false;
    }

    var table :mseq<Boundary> := tableOpt.value;
  
    if || !BoundaryInt.fitsInUint64(table[0])
    || !BoundaryInt.fitsInUint64(table[1])
    || !BoundaryInt.fitsInUint64(table[2])
    {
      return false;
    }

    var bound0 := BoundaryInt.toUint64(table[0]);
    var bound1 := BoundaryInt.toUint64(table[1]);
    var bound2 := BoundaryInt.toUint64(table[2]);


    if bound0 > |data| as uint64 || bound0 < tableSize {
      return false;
    }

    if bound1 > |data| as uint64 || bound1 < bound0 {
      return false;
    }
    

    if bound2 > |data| as uint64 || bound2 < bound1 {
      return false;
    }
    

    var elemParsable0 := ElemMarshalling0.Parsable(data[tableSize..bound0]);
    var elemParsable1 := ElemMarshalling1.Parsable(data[bound0..bound1]);
    var elemParsable2 := ElemMarshalling2.Parsable(data[bound1..bound2]);
    var elemParsable3 := ElemMarshalling3.Parsable(data[bound2..]);
    
    if || !elemParsable0
    || !elemParsable1
    || !elemParsable2
    || !elemParsable3
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
    var bound1 := BoundaryInt.toUint64(table[1]);
    var bound2 := BoundaryInt.toUint64(table[2]);

    var elem0 := ElemMarshalling0.Parse(data[tableSize..bound0]);
    var elem1 := ElemMarshalling1.Parse(data[bound0..bound1]);
    var elem2 := ElemMarshalling2.Parse(data[bound1..bound2]);
    var elem3 := ElemMarshalling3.Parse(data[bound2..]);
    
    return (elem0,
    elem1,
    elem2,
    elem3);
  }

  predicate marshallable(value: UnmarshalledType)
  {
    && var (elem0,elem1,elem2,elem3) := value;
    && ElemMarshalling0.marshallable(elem0)
    && ElemMarshalling1.marshallable(elem1)
    && ElemMarshalling2.marshallable(elem2)
    && ElemMarshalling3.marshallable(elem3)

    && var tableSize := sizeOfTable();
    var size0 := ElemMarshalling0.size(elem0);
    var bound0 := tableSize + size0;
    var size1 := ElemMarshalling1.size(elem1);
    var bound1 := bound0 + size1;
    
    var size2 := ElemMarshalling2.size(elem2);
    var bound2 := bound1 + size2;
    
    && BoundaryInt.MinValue() <= bound0 < BoundaryInt.UpperBound()
    && BoundaryInt.MinValue() <= bound1 < BoundaryInt.UpperBound()
    && BoundaryInt.MinValue() <= bound2 < BoundaryInt.UpperBound()
    && var table := [BoundaryInt.fromInt(bound0),
    BoundaryInt.fromInt(bound1),
    BoundaryInt.fromInt(bound2)];
    && TableMarshalling.marshallable(table)
  }

  function size(value: UnmarshalledType) : nat
  {
    var (elem0,elem1,elem2,elem3) := value;
    var tableSize := sizeOfTable();
    var size0 := ElemMarshalling0.size(elem0);
    var size1 := ElemMarshalling1.size(elem1);
    var size2 := ElemMarshalling2.size(elem2);
    var size3 := ElemMarshalling3.size(elem3);

    tableSize+size0+size1+size2+size3
  }

  method Size(value: UnmarshalledType) returns (sz: uint64)
  {
    var (elem0,elem1,elem2,elem3) := value;
    var tableSize := sizeOfTable() as uint64;
    var size0 := ElemMarshalling0.Size(elem0);
    var size1 := ElemMarshalling1.Size(elem1);
    var size2 := ElemMarshalling2.Size(elem2);
    var size3 := ElemMarshalling3.Size(elem3);

    sz := tableSize+size0+size1+size2+size3;
  }

  method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
    returns (linear newdata: mseq<byte>, end: uint64)
  {
    var (elem0,elem1,elem2,elem3) := value;

    var tableSize := sizeOfTable() as uint64;
    var size0 := ElemMarshalling0.Size(elem0);
    var bound0 := tableSize + size0;
    var size1 := ElemMarshalling1.Size(elem1);
    var bound1 := bound0 + size1;
    
    var size2 := ElemMarshalling2.Size(elem2);
    var bound2 := bound1 + size2;
    
    var table := [BoundaryInt.fromUint64(bound0),
    BoundaryInt.fromUint64(bound1),
    BoundaryInt.fromUint64(bound2)];

    newdata, end := TableMarshalling.Marshall(table, data, start);
    ghost var newdata0 :seq<byte>, end0 := newdata, end;
    newdata, end := ElemMarshalling0.Marshall(elem0, newdata, end);
    ghost var newdata1 :seq<byte>, end1 := newdata, end;
    newdata, end := ElemMarshalling1.Marshall(elem1, newdata, end);
    ghost var newdata2 :seq<byte>, end2 := newdata, end;
    newdata, end := ElemMarshalling2.Marshall(elem2, newdata, end);
    ghost var newdata3 :seq<byte>, end3 := newdata, end;
    newdata, end := ElemMarshalling3.Marshall(elem3, newdata, end);

    assert 
      && BoundaryInt.toInt(table[0]) == bound0 as int
      && BoundaryInt.toInt(table[1]) == bound1 as int
      && BoundaryInt.toInt(table[2]) == bound2 as int by {
      BoundaryInt.fromtoInverses();
    }

    assert newdata[start..end][..tableSize] == newdata[start..end0] == newdata0[start..end0];
    // assert TableMarshalling.parse(newdata[start..end0]) == table;
    
    assert newdata[start..end][tableSize..bound0] == newdata[end0..end1] == newdata1[end0..end1] by {
      Sequences.lemma_seq_slice_slice(newdata, start as int, end as int, tableSize as int, bound0 as int);
    }
    // assert ElemMarshalling0.parse(newdata[end0..end1]) == elem0;


    assert newdata[start..end][bound0..bound1] == newdata[end1..end2] == newdata2[end1..end2] by {
      Sequences.lemma_seq_slice_slice(newdata, start as int, end as int, bound0 as int, bound1 as int);
    }
    // assert ElemMarshalling1.parse(newdata[end1..end2]) == elem1;
    assert newdata[start..end][bound1..bound2] == newdata[end2..end3] == newdata3[end2..end3] by {
      Sequences.lemma_seq_slice_slice(newdata, start as int, end as int, bound1 as int, bound2 as int);
    }
    // assert ElemMarshalling2.parse(newdata[end2..end3]) == elem2;

    assert newdata[start..end][bound2..] == newdata[end3..end];
    // assert ElemMarshalling3.parse(newdata[end3..end]) == elem3;
  }
}
