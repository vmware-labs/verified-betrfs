include "MarshalledAccessors.i.dfy"
include "../Base/sequences.i.dfy"

module Tuple2Marshalling(
  BoundaryInt: NativePackedInt,
  ElemMarshalling0 : Marshalling,
  ElemMarshalling1 : Marshalling)
  refines Marshalling {

  import Sequences

  import BSM = IntegerSeqMarshalling(BoundaryInt)

  type Boundary = BoundaryInt.Integer
  type BoundaryTable = mseq<Boundary>
  type UnmarshalledType = (ElemMarshalling0.UnmarshalledType, ElemMarshalling1.UnmarshalledType)

  datatype Config = Config(bsmCfg: BSM.Config,
    elem0Cfg: ElemMarshalling0.Config,
    elem1Cfg: ElemMarshalling1.Config)

  const eltCount := 2;

  predicate validConfig(cfg: Config)
  {
    && BSM.validConfig(cfg.bsmCfg)
    && ElemMarshalling0.validConfig(cfg.elem0Cfg)
    && ElemMarshalling1.validConfig(cfg.elem1Cfg)
  }

  function sizeOfTable(): nat
  {
    (eltCount - 1) as nat * BoundaryInt.Size() as nat
  }

  predicate sizeOfTableBounded()
  {
    sizeOfTable() < Uint64UpperBound()
  }

  function method SizeOfTable() : (size: uint64)
    requires sizeOfTableBounded()
    ensures size as nat == sizeOfTable()
  {
    (eltCount - 1) as uint64 * BoundaryInt.Size()
  }

  predicate tableParsable(bsmCfg: BSM.Config, data: mseq<byte>)
  {
    && sizeOfTableBounded()
    && sizeOfTable() <= |data|
  }

  function parseTable(bsmCfg: BSM.Config, data: mseq<byte>): (table : mseq<Boundary>)
    requires tableParsable(bsmCfg, data)
    ensures table == BoundaryInt.unpack_Seq(data[..sizeOfTable()], eltCount - 1)
  {
    var tableData := data[.. sizeOfTable()];
    var table: mseq<Boundary> := BSM.parse(bsmCfg, tableData);
    BSM.parse_is_unpack_Seq(bsmCfg, tableData);
    assert BSM.length(bsmCfg, tableData) == |tableData| / BoundaryInt.Size() as nat;
    table
  }

  predicate parsable(cfg: Config, data: mseq<byte>)
  {
    && tableParsable(cfg.bsmCfg, data)
    && var table := parseTable(cfg.bsmCfg, data);
    && var bound0 := table[0];
    && sizeOfTable() <= bound0 <= |data|
    && ElemMarshalling0.parsable(cfg.elem0Cfg, data[sizeOfTable()..bound0])
    && ElemMarshalling1.parsable(cfg.elem1Cfg, data[bound0..])
  }

  function parse(cfg: Config, data: mseq<byte>) : UnmarshalledType
  {
    var table := parseTable(cfg.bsmCfg, data);
    var bound0 := table[0];
    var elt0 := ElemMarshalling0.parse(cfg.elem0Cfg, data[sizeOfTable()..bound0]);
    var elt1 := ElemMarshalling1.parse(cfg.elem1Cfg, data[bound0..]);
    (elt0, elt1)
  }

  method TryParse(cfg: Config, data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var tableSize := SizeOfTable();

    if tableSize > |data| as uint64 {
      return None;
    }

    var table :- BSM.TryParse(cfg.bsmCfg, data[..tableSize]);
    assert table == parseTable(cfg.bsmCfg, data);

    var bound0 := BoundaryInt.toUint64(table[0]);

    if bound0 > |data| as uint64 || bound0 < tableSize {
      return None;
    }

    var value0 :- ElemMarshalling0.TryParse(cfg.elem0Cfg, data[tableSize..bound0]);
    var value1 :- ElemMarshalling1.TryParse(cfg.elem1Cfg, data[bound0..]);

    ovalue := Some((value0, value1));
  }

  method Parsable(cfg: Config, data: mseq<byte>) returns (p: bool)
  {
    var tableSize := SizeOfTable();

    if tableSize > |data| as uint64 {
      return false;
    }

    var tableOpt := BSM.TryParse(cfg.bsmCfg, data[..tableSize]);

    if tableOpt.None? {
      return false;
    }

    var table := tableOpt.value;
    assert table == parseTable(cfg.bsmCfg, data);

    var bound0 := BoundaryInt.toUint64(table[0]);

    if bound0 > |data| as uint64 || bound0 < tableSize {
      return false;
    }

    var fstParsable := ElemMarshalling0.Parsable(cfg.elem0Cfg, data[tableSize..bound0]);
    var sndParsable := ElemMarshalling1.Parsable(cfg.elem1Cfg, data[bound0..]);

    return fstParsable && sndParsable;
  }

  method Parse(cfg: Config, data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var tableSize := SizeOfTable();
    var table := BSM.Parse(cfg.bsmCfg, data[..tableSize]);
    assert table == parseTable(cfg.bsmCfg, data);
    var bound0 := table[0];

    var value0 := ElemMarshalling0.Parse(cfg.elem0Cfg, data[tableSize..bound0]);
    var value1 := ElemMarshalling1.Parse(cfg.elem1Cfg, data[bound0..]);
    return (value0, value1);
  }

  predicate marshallable(cfg: Config, value: UnmarshalledType)
  {
    && var (value0, value1) := value;
    && ElemMarshalling0.marshallable(cfg.elem0Cfg, value0)
    && ElemMarshalling1.marshallable(cfg.elem1Cfg, value1)
    && var tableSize := sizeOfTable();
    && var bound0 := ElemMarshalling0.size(cfg.elem0Cfg, value0) as int + tableSize;
    && var bound1 := ElemMarshalling0.size(cfg.elem1Cfg, value1) as int + bound0;
    && BoundaryInt.MinValue() <= bound0 < BoundaryInt.UpperBound()
    && BoundaryInt.MinValue() <= bound1 < BoundaryInt.UpperBound()
  }

  function size(cfg: Config, value: UnmarshalledType) : uint64
  {
    var (value0, value1) := value;
    SizeOfTable() + ElemMarshalling0.size(cfg.elem0Cfg, value0) + ElemMarshalling1.size(cfg.elem1Cfg, value1)
  }

  method Size(cfg: Config, value: UnmarshalledType) returns (sz: uint64)
  {
    var (value0, value1) := value;
    var size0 := ElemMarshalling0.Size(cfg.elem0Cfg, value0);
    var size1 := ElemMarshalling0.Size(cfg.elem1Cfg, value1);
    return SizeOfTable() + size0 + size1;
  }

  method Marshall(cfg: Config, value: UnmarshalledType, linear inout data: mseq<byte>, start: uint64)
    returns (end: uint64)
  {
    var (value0, value1) := value;

    var size0 := ElemMarshalling0.Size(cfg.elem0Cfg, value0);
    var tableSize := SizeOfTable();
    var bound0 := tableSize + size0;
    var table := [bound0 as BoundaryInt.Integer];

    end := BSM.Marshall(cfg.bsmCfg, table, inout data, start);
    ghost var newdata0 :seq<byte>, end0 := data, end;

    end := ElemMarshalling0.Marshall(cfg.elem0Cfg, value0, inout data, end);
    ghost var newdata1 :seq<byte>, end1 := data, end;

    end := ElemMarshalling1.Marshall(cfg.elem1Cfg, value1, inout data, end);

    assert data[start..end][..tableSize] == data[start..end0] == newdata0[start..end0];
    // assert BSM.parse(cfg.bsmCfg, data[start..end0]) == table;

    assert data[start..end][tableSize..bound0] == data[end0..end1] == newdata1[end0..end1] by {
      Sequences.lemma_seq_slice_slice(data, start as int, end as int, tableSize as int, bound0 as int);
    }
    // assert ElemMarshalling0.parse(cfg.elem0Cfg, data[end0..end1]) == value0;

    assert data[start..end][bound0..] == data[end1..end];
    // assert ElemMarshalling1.parse(cfg.elem1Cfg, data[end1..end]) == value1;
  }

  predicate boundGettable(cfg: Config, data: mseq<byte>, index: nat)
  {
    && validConfig(cfg)
    && index <= eltCount - 1

    && var tableSize := sizeOfTable();
    && tableSize <= |data|
    && var tableData := data[..tableSize];

    && (index != eltCount - 1 ==> BSM.gettable(cfg.bsmCfg, tableData, index))
    && (index != 0 ==> BSM.gettable(cfg.bsmCfg, tableData, index-1))
  }

  function getBounds(cfg: Config, data: mseq<byte>, index: nat) :(int, int)
    requires boundGettable(cfg, data, index)
  {
    var tableData := data[..sizeOfTable()];
    var start := if index == 0 then sizeOfTable() else BSM.getElt(cfg.bsmCfg, tableData, index - 1);
    var end := if index == eltCount-1 then |data| else BSM.getElt(cfg.bsmCfg, tableData, index);
    (start, end)
  }

  predicate gettable(cfg: Config, data: mseq<byte>, index: nat)
  {
    && boundGettable(cfg, data, index)
    && var (start, end) := getBounds(cfg, data, index);
    && 0 <= start <= end <= |data|
  }

  method Gettable(cfg: Config, data: mseq<byte>, index: uint64)
    returns (g: bool)
    requires validConfig(cfg)
    requires index as nat < eltCount
    ensures g == gettable(cfg, data, index as nat)
  {
    var tableSize := SizeOfTable();
  
    if tableSize > |data| as uint64 {
      return false;
    }
    
    var tableData := data[..tableSize];

    if index != eltCount as uint64 - 1 {
      var startGettable := BSM.Gettable(cfg.bsmCfg, tableData, index);
      if !startGettable { return false; }
    }

    if index != 0 {
      var endGettable := BSM.Gettable(cfg.bsmCfg, tableData, index-1);
      if !endGettable { return false; }
    }

    var start := tableSize;

    if index != 0 {
      var istart := BSM.GetElt(cfg.bsmCfg, tableData, index - 1);
      start := BoundaryInt.toUint64(istart);
    }

    var end := |data| as uint64;

    if index != eltCount as uint64 - 1 {
      var iend := BSM.GetElt(cfg.bsmCfg, tableData, index);
      end := BoundaryInt.toUint64(iend);
    }

    g := 0 <= start <= end <= |data| as uint64;
  }

  method GetElem0(cfg: Config, data: mseq<byte>)
    returns (eslice: Slice)
    requires gettable(cfg, data, 0)

    ensures eslice.WF'(data)
    ensures parsable(cfg, data) ==> ElemMarshalling0.parsable(cfg.elem0Cfg, eslice.I(data))
    ensures parsable(cfg, data) ==> parse(cfg, data).0 == ElemMarshalling0.parse(cfg.elem0Cfg, eslice.I(data))
  {
    var tableSize := SizeOfTable();
    var bound0 := BSM.GetElt(cfg.bsmCfg, data[..tableSize], 0);
    eslice := Slice(tableSize, BoundaryInt.toUint64(bound0));
  }

  method GetElem1(cfg: Config, data: mseq<byte>)
    returns (eslice: Slice)
    requires gettable(cfg, data, 1)

    ensures eslice.WF'(data)
    ensures parsable(cfg, data) ==> ElemMarshalling1.parsable(cfg.elem1Cfg, eslice.I(data))
    ensures parsable(cfg, data) ==> parse(cfg, data).1 == ElemMarshalling1.parse(cfg.elem1Cfg, eslice.I(data))
  {
    var tableSize := SizeOfTable();
    var bound0 := BSM.GetElt(cfg.bsmCfg, data[..tableSize], 0);
    eslice := Slice(BoundaryInt.toUint64(bound0), |data| as uint64);
    assert eslice.I(data) == data[bound0..];
  }

  // method SetElem0(cfg: Config, linear inout data: mseq<byte>, value: ElemMarshalling0.UnmarshalledType)
  //   requires validConfig(cfg)
  // {

  // }
}

// abstract module Tuple3Marshalling refines Marshalling {
//   import ElemMarshalling0 : Marshalling
//   import ElemMarshalling1 : Marshalling
//   import ElemMarshalling2 : Marshalling
//   import TableMarshalling : IntegerSeqMarshalling
//   import Sequences
//   import BoundaryInt = TableMarshalling.Int

//   type UnmarshalledType = (ElemMarshalling0.UnmarshalledType, ElemMarshalling1.UnmarshalledType, ElemMarshalling2.UnmarshalledType)

//   type Boundary = BoundaryInt.Integer
//   type BoundaryTable = mseq<Boundary>

//   function method SizeOfBoundaryEntry() : uint64
//   {
//     BoundaryInt.Size()
//   }

//   function method sizeOfTable() : nat
//   {
//     2 * SizeOfBoundaryEntry() as nat
//   }

//   predicate parsable(data: mseq<byte>)
//   {
//     && var tableSize := sizeOfTable();
//     && tableSize < Uint64UpperBound()
//     && |data| >= tableSize
//     && TableMarshalling.parsable(data[..tableSize])
//     && var table :mseq<Boundary> := TableMarshalling.parse(data[..tableSize]);

//     && var bound0 := BoundaryInt.toInt(table[0]);
//     && tableSize <= bound0 <= |data|
//     && ElemMarshalling0.parsable(data[tableSize..bound0])

//     && var bound1 := BoundaryInt.toInt(table[1]);
//     && bound0 <= bound1 <= |data|
//     && ElemMarshalling1.parsable(data[bound0..bound1])

//     && ElemMarshalling2.parsable(data[bound1..])
//   }

//   function parse(data: mseq<byte>) : UnmarshalledType
//   {
//     var tableSize := sizeOfTable();
//     var table :mseq<Boundary> := TableMarshalling.parse(data[..tableSize]);
//     var bound0 := BoundaryInt.toInt(table[0]);
//     var elem0 := ElemMarshalling0.parse(data[tableSize..bound0]);
//     var bound1 := BoundaryInt.toInt(table[1]);
//     var elem1 := ElemMarshalling1.parse(data[bound0..bound1]);
//     var elem2 := ElemMarshalling2.parse(data[bound1..]);
//     (elem0, elem1, elem2)
//   }

//   method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
//   {
//     var entrySize := SizeOfBoundaryEntry();

//     if entrySize >= 0x8000_0000_0000_0000 {
//       return None;
//     }

//     var tableSize := entrySize * 2;

//     if tableSize > |data| as uint64 {
//       return None;
//     }

//     var tableOpt := TableMarshalling.TryParse(data[..tableSize]);
    
//     if tableOpt.None? {
//       return None;
//     }

//     var table :mseq<Boundary> := tableOpt.value;
  
//     if !BoundaryInt.fitsInUint64(table[0]) 
//       || !BoundaryInt.fitsInUint64(table[1]) {
//       return None;
//     }

//     var bound0 := BoundaryInt.toUint64(table[0]);
//     var bound1 := BoundaryInt.toUint64(table[1]);

//     if bound0 > |data| as uint64 || bound0 < tableSize {
//       return None;
//     }

//     if bound1 > |data| as uint64 || bound1 < bound0 {
//       return None;
//     }

//     var elemOpt0 := ElemMarshalling0.TryParse(data[tableSize..bound0]);
//     var elemOpt1 := ElemMarshalling1.TryParse(data[bound0..bound1]);
//     var elemOpt2 := ElemMarshalling2.TryParse(data[bound1..]);

//     if elemOpt0.None? || elemOpt1.None? || elemOpt2.None? {
//       return None;
//     }

//     return Some((elemOpt0.value, elemOpt1.value, elemOpt2.value));
//   }

//   method Parsable(data: mseq<byte>) returns (p: bool)
//   {
//     var entrySize := SizeOfBoundaryEntry();

//     if entrySize >= 0x8000_0000_0000_0000 {
//       return false;
//     }

//     var tableSize := sizeOfTable() as uint64;

//     if tableSize > |data| as uint64 {
//       return false;
//     }

//     var tableOpt := TableMarshalling.TryParse(data[..tableSize]);
    
//     if tableOpt.None? {
//       return false;
//     }

//     var table :mseq<Boundary> := tableOpt.value;

//     if !BoundaryInt.fitsInUint64(table[0]) 
//       || !BoundaryInt.fitsInUint64(table[1]) {
//       return false;
//     }

//     var bound0 := BoundaryInt.toUint64(table[0]);
//     var bound1 := BoundaryInt.toUint64(table[1]);

//     if bound0 > |data| as uint64 || bound0 < tableSize {
//       return false;
//     }

//     if bound1 > |data| as uint64 || bound1 < bound0 {
//       return false;
//     }

//     var elemParsable0 := ElemMarshalling0.Parsable(data[tableSize..bound0]);
//     var elemParsable1 := ElemMarshalling1.Parsable(data[bound0..bound1]);
//     var elemParsable2 := ElemMarshalling2.Parsable(data[bound1..]);

//     if !elemParsable0 || !elemParsable1 || !elemParsable2 {
//       return false;
//     }

//     return true;
//   }

//   method Parse(data: mseq<byte>) returns (value: UnmarshalledType)
//   {
//     var tableSize := sizeOfTable() as uint64;
//     var table :mseq<Boundary> := TableMarshalling.Parse(data[..tableSize]);
  
//     var bound0 := BoundaryInt.toUint64(table[0]);
//     var bound1 := BoundaryInt.toUint64(table[1]);

//     var elem0 := ElemMarshalling0.Parse(data[tableSize..bound0]);
//     var elem1 := ElemMarshalling1.Parse(data[bound0..bound1]);
//     var elem2 := ElemMarshalling2.Parse(data[bound1..]);
//     return (elem0, elem1, elem2);
//   }

//   predicate marshallable(value: UnmarshalledType)
//   {
//     && var (elem0, elem1, elem2) := value;
//     && ElemMarshalling0.marshallable(elem0)
//     && ElemMarshalling1.marshallable(elem1)
//     && ElemMarshalling2.marshallable(elem2)
//     && var tableSize := sizeOfTable();
//     var size0 := ElemMarshalling0.size(elem0);
//     var size1 := ElemMarshalling1.size(elem1);
//     var bound0 := tableSize + size0;
//     var bound1 := bound0 + size1;
//     && BoundaryInt.MinValue() <= bound0 < BoundaryInt.UpperBound()
//     && BoundaryInt.MinValue() <= bound1 < BoundaryInt.UpperBound()
//     && var table := [BoundaryInt.fromInt(bound0), BoundaryInt.fromInt(bound1)];
//     && TableMarshalling.marshallable(table)
//   }

//   function size(value: UnmarshalledType) : nat
//   {
//     var (elem0, elem1, elem2) := value;
//     var tableSize := sizeOfTable();
//     var size0 := ElemMarshalling0.size(elem0);
//     var size1 := ElemMarshalling1.size(elem1);
//     var size2 := ElemMarshalling2.size(elem2);
//     tableSize + size0 + size1 + size2
//   }

//   method Size(value: UnmarshalledType) returns (sz: uint64)
//   {
//     var (elem0, elem1, elem2) := value;
//     var tableSize := sizeOfTable() as uint64;
//     var size0 := ElemMarshalling0.Size(elem0);
//     var size1 := ElemMarshalling1.Size(elem1);
//     var size2 := ElemMarshalling2.Size(elem2);
//     sz := tableSize + size0 + size1 + size2;
//   }

//   method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
//     returns (linear newdata: mseq<byte>, end: uint64)
//   {
//     var (elem0, elem1, elem2) := value;
//     var tableSize := sizeOfTable() as uint64;

//     var size0 := ElemMarshalling0.Size(elem0);
//     var size1 := ElemMarshalling1.Size(elem1);

//     var bound0 := tableSize + size0;
//     var bound1 := bound0 + size1;

//     var table := [BoundaryInt.fromUint64(bound0), BoundaryInt.fromUint64(bound1)];

//     newdata, end := TableMarshalling.Marshall(table, data, start);
//     ghost var newdata0 :seq<byte>, end0 := newdata, end;

//     newdata, end := ElemMarshalling0.Marshall(elem0, newdata, end);
//     ghost var newdata1 :seq<byte>, end1 := newdata, end;

//     newdata, end := ElemMarshalling1.Marshall(elem1, newdata, end);
//     ghost var newdata2 :seq<byte>, end2 := newdata, end;

//     newdata, end := ElemMarshalling2.Marshall(elem2, newdata, end);

//     assert BoundaryInt.toInt(table[0]) == bound0 as int 
//       && BoundaryInt.toInt(table[1]) == bound1 as int by {
//       BoundaryInt.fromtoInverses();
//     }

//     assert newdata[start..end][..tableSize] == newdata[start..end0] == newdata0[start..end0];
//     // assert TableMarshalling.parse(newdata[start..end0]) == table;
    
//     assert newdata[start..end][tableSize..bound0] == newdata[end0..end1] == newdata1[end0..end1] by {
//       Sequences.lemma_seq_slice_slice(newdata, start as int, end as int, tableSize as int, bound0 as int);
//     }
//     // assert ElemMarshalling0.parse(newdata[end0..end1]) == elem0;

//     assert newdata[start..end][bound0..bound1] == newdata[end1..end2] == newdata2[end1..end2] by {
//       Sequences.lemma_seq_slice_slice(newdata, start as int, end as int, bound0 as int, bound1 as int);
//     }
//     // assert ElemMarshalling1.parse(newdata[end1..end2]) == elem1;

//     assert newdata[start..end][bound1..] == newdata[end2..end];
//     // assert ElemMarshalling2.parse(newdata[end2..end]) == elem2;
//   }

//   method GetElem0(data: mseq<byte>) returns (edata: mseq<byte>)
//     requires var tableSize := sizeOfTable();
//     // && TableMarshalling.parsable(data[..tableSize])
//     // && var table :mseq<Boundary> := TableMarshalling.parse(data[..tableSize]);
//     // && BoundaryInt.fitsInUint64(table[0])
//     // && var bound0 := BoundaryInt.toInt(table[0]);
//     // && tableSize <= bound0 <= |data|
//     ensures parsable(data) ==> ElemMarshalling0.parsable(edata)
//     ensures parsable(data) ==> ElemMarshalling0.parse(edata) == parse(data).0
//   {
//     var tableSize := sizeOfTable() as uint64;
//     var iend0 := TableMarshalling.FastGet(data[..tableSize], 0);
//     var end0 := BoundaryInt.toUint64(iend0); 

//     edata := data[tableSize..end0];
//   }

//   method GetElem1(data: mseq<byte>) returns (edata: mseq<byte>)
//     requires parsable(data)
//     ensures ElemMarshalling1.parsable(edata)
//     ensures ElemMarshalling1.parse(edata) == parse(data).1
//   {
//     var tableSize := sizeOfTable() as uint64;
//     var iend0 := TableMarshalling.FastGet(data[..tableSize], 0);
//     var end0 := BoundaryInt.toUint64(iend0); 
//     var iend1 := TableMarshalling.FastGet(data[..tableSize], 1);
//     var end1 := BoundaryInt.toUint64(iend1); 

//     edata := data[end0..end1];
//   }

//   method GetElem2(data: mseq<byte>) returns (edata: mseq<byte>)
//     requires parsable(data)
//     ensures ElemMarshalling2.parsable(edata)
//     ensures ElemMarshalling2.parse(edata) == parse(data).2
//   {
//     var tableSize := sizeOfTable() as uint64;
//     var iend1 := TableMarshalling.FastGet(data[..tableSize], 1);
//     var end1 := BoundaryInt.toUint64(iend1); 

//     edata := data[end1..];
//   }