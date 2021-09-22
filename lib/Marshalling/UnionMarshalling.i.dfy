include "MarshalledAccessors.i.dfy"
// include "../Base/sequences.i.dfy"

abstract module Union2Marshalling(
  TagInt: NativePackedInt,
  CaseMarshalling0: Marshalling,
  CaseMarshalling1: Marshalling)
refines Marshalling {
  
  import TGM = IntegerMarshalling(TagInt)

  datatype UnionType = 
    | Left(l : CaseMarshalling0.UnmarshalledType)
    | Right(r: CaseMarshalling1.UnmarshalledType)

  datatype Config = Config(tgmCfg: TGM.Config,
    elemCfg0: CaseMarshalling0.Config,
    elemCfg1: CaseMarshalling1.Config)

  type UnmarshalledType = UnionType

  type TagType = TGM.UnmarshalledType

  predicate validConfig(cfg: Config)
  {
    && TGM.validConfig(cfg.tgmCfg)
    && CaseMarshalling0.validConfig(cfg.elemCfg0)
    && CaseMarshalling1.validConfig(cfg.elemCfg1)
  }

  function method getTagEnd(): uint64
  {
    TagInt.Size() as uint64
  }

  predicate parsable(cfg: Config, data: mseq<byte>)
  {
    var tagEnd := getTagEnd() as int;
    && |data| >= tagEnd
    && TGM.parsable(cfg.tgmCfg, data[..tagEnd])
    && var tag := TGM.parse(cfg.tgmCfg, data[..tagEnd]);
    (if tag == 0 then CaseMarshalling0.parsable(cfg.elemCfg0, data[tagEnd..])
        else CaseMarshalling1.parsable(cfg.elemCfg1, data[tagEnd..]))
  }

  function parse(cfg: Config, data: mseq<byte>) : UnmarshalledType
  {
    var tagEnd := getTagEnd() as int;
    var tag := TGM.parse(cfg.tgmCfg, data[..tagEnd]);

    if tag == 0 then Left(CaseMarshalling0.parse(cfg.elemCfg0, data[tagEnd..]))
      else Right(CaseMarshalling1.parse(cfg.elemCfg1, data[tagEnd..]))
  }

  method TryParse(cfg: Config, data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var tagEnd := getTagEnd();

    if tagEnd > |data| as uint64 {
      return None;
    }

    var tag :- TGM.TryParse(cfg.tgmCfg, data[..tagEnd]);
    
    ovalue := None;

    if tag == 0 {
      var left :- CaseMarshalling0.TryParse(cfg.elemCfg0, data[tagEnd..]);
      ovalue := Some(Left(left));
    } else {
      var right :- CaseMarshalling1.TryParse(cfg.elemCfg1, data[tagEnd..]);
      ovalue := Some(Right(right));
    }
  }

  method Parsable(cfg: Config, data: mseq<byte>) returns (p: bool)
  {
    var tagEnd := getTagEnd();

    if tagEnd > |data| as uint64 {
      return false;
    }

    var tagOvalue := TGM.TryParse(cfg.tgmCfg, data[..tagEnd]);
    
    if tagOvalue.None? {
      return false;
    }

    var tag := TGM.Int.toUint64(tagOvalue.value);

    var parsable := false;

    if tag == 0 {
      parsable := CaseMarshalling0.Parsable(cfg.elemCfg0, data[tagEnd..]);
    } else {
      parsable := CaseMarshalling1.Parsable(cfg.elemCfg1, data[tagEnd..]);
    }
    return parsable;
  }

  method Parse(cfg: Config, data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var tagEnd := getTagEnd();
    var tag := TGM.Parse(cfg.tgmCfg, data[..tagEnd]);

    if tag == 0 {
      var leftValue := CaseMarshalling0.Parse(cfg.elemCfg0, data[tagEnd..]);
      return Left(leftValue);
    } else {
      var rightValue := CaseMarshalling1.Parse(cfg.elemCfg1, data[tagEnd..]);
      return Right(rightValue);
    }
  }

  predicate marshallable(cfg: Config, value: UnmarshalledType)
  {
    && TagInt.MinValue() <= 0 < 1 < TagInt.UpperBound()
    && match value {
      case Left(leftValue) =>
        (&& CaseMarshalling0.marshallable(cfg.elemCfg0, leftValue)
        && getTagEnd() as nat + CaseMarshalling0.size(cfg.elemCfg0, leftValue) as nat < Uint64UpperBound())
      case Right(rightValue) =>
        (&& CaseMarshalling1.marshallable(cfg.elemCfg1, rightValue)
        && getTagEnd() as nat + CaseMarshalling1.size(cfg.elemCfg1, rightValue) as nat < Uint64UpperBound())
    }
  }

  function size(cfg: Config, value: UnmarshalledType) : uint64
  {
    var tagEnd := getTagEnd();
    match value {
      case Left(leftValue) => tagEnd + CaseMarshalling0.size(cfg.elemCfg0, leftValue)
      case Right(rightValue) => tagEnd + CaseMarshalling1.size(cfg.elemCfg1, rightValue)
    }
  }

  method Size(cfg: Config, value: UnmarshalledType) returns (sz: uint64)
  {
    sz := getTagEnd();
    match value {
      case Left(leftValue) => {
        var leftSize := CaseMarshalling0.Size(cfg.elemCfg0, leftValue);
        sz := sz + leftSize;
      }
      case Right(rightValue) => {
        var rightSize := CaseMarshalling1.Size(cfg.elemCfg1, rightValue);
        sz := sz + rightSize;
      }
    }
    return sz;
  }

  method Marshall(cfg: Config, value: UnmarshalledType, linear inout data: mseq<byte>, start: uint64) returns (end: uint64)
  {
    ghost var tagEnd : uint64 := getTagEnd();

    match value
    case Left(leftValue) => {
      end := TGM.Marshall(cfg.tgmCfg, 0, inout data, start);
      ghost var newdata1 :seq<byte>, end1 := data, end;
      end := CaseMarshalling0.Marshall(cfg.elemCfg0, leftValue, inout data, end);

      assert newdata1[start..end1] == data[start..end1];
      assert data[start..end][..tagEnd] == data[start..end1];
    }
    case Right(rightValue) => {
      end := TGM.Marshall(cfg.tgmCfg, 1, inout data, start);
      ghost var newdata1 :seq<byte>, end1 := data, end;
      end := CaseMarshalling0.Marshall(cfg.elemCfg1, rightValue, inout data, end);

      assert newdata1[start..end1] == data[start..end1];
      assert data[start..end][..tagEnd] == data[start..end1];
    }
  }
}

// abstract module Union3Marshalling refines Marshalling {
//   import CaseMarshalling0 : Marshalling
//   import CaseMarshalling1 : Marshalling
//   import CaseMarshalling2 : Marshalling
//   import TGM : IntegerMarshalling
//   // import Sequences

//   datatype UnionType = 
//     | Case0(c0: CaseMarshalling0.UnmarshalledType)
//     | Case1(c1: CaseMarshalling1.UnmarshalledType)
//     | Case2(c2: CaseMarshalling2.UnmarshalledType)

//   type UnmarshalledType = UnionType

//   type TagType = TGM.UnmarshalledType

//   function method getTagEnd(): uint64
//   {
//     TGM.Int.Size() as uint64
//   }

//   predicate parsable(data: mseq<byte>)
//   {
//     var tagEnd := getTagEnd() as int;
//     && |data| >= tagEnd
//     && TGM.parsable(data[..tagEnd])
//     && TGM.Int.fitsInUint64(TGM.parse(data[..tagEnd]))
//     && var tag := TGM.Int.toInt(TGM.parse(data[..tagEnd]));
//     (if tag == 0 then CaseMarshalling0.parsable(data[tagEnd..])
//       else if tag == 1 then CaseMarshalling1.parsable(data[tagEnd..])
//       else CaseMarshalling2.parsable(data[tagEnd..]))
//   }

//   function parse(data: mseq<byte>) : UnmarshalledType
//   {
//     var tagEnd := getTagEnd() as int;
//     var tag := TGM.Int.toInt(TGM.parse(data[..tagEnd]));

//     if tag == 0 then Case0(CaseMarshalling0.parse(data[tagEnd..]))
//       else if tag == 1 then Case1(CaseMarshalling1.parse(data[tagEnd..]))
//       else Case2(CaseMarshalling2.parse(data[tagEnd..]))
//   }

//   method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
//   {
//     var tagEnd := getTagEnd();

//     if tagEnd > |data| as uint64 {
//       return None;
//     }

//     var tagOvalue := TGM.TryParse(data[..tagEnd]);
    
//     if tagOvalue.None? {
//       return None;
//     }

//     if !TGM.Int.fitsInUint64(tagOvalue.value) {
//       return None;
//     }

//     var tag := TGM.Int.toUint64(tagOvalue.value);
//     ovalue := None;

//     if tag == 0 {
//       var valueOpt := CaseMarshalling0.TryParse(data[tagEnd..]);
//       if valueOpt.Some? {
//         ovalue := Some(Case0(valueOpt.value));
//       }
//     } else if tag == 1 {
//       var valueOpt := CaseMarshalling1.TryParse(data[tagEnd..]);
//       if valueOpt.Some? {
//         ovalue := Some(Case1(valueOpt.value));
//       }
//     } else {
//       var valueOpt := CaseMarshalling2.TryParse(data[tagEnd..]);
//       if valueOpt.Some? {
//         ovalue := Some(Case2(valueOpt.value));
//       }
//     }
//   }

//   method Parsable(data: mseq<byte>) returns (p: bool)
//   {
//     var tagEnd := getTagEnd();

//     if tagEnd > |data| as uint64 {
//       return false;
//     }

//     var tagOvalue := TGM.TryParse(data[..tagEnd]);
    
//     if tagOvalue.None? {
//       return false;
//     }

//     if !TGM.Int.fitsInUint64(tagOvalue.value) {
//       return false;
//     }

//     var tag := TGM.Int.toUint64(tagOvalue.value);

//     if tag == 0 {
//       p := CaseMarshalling0.Parsable(data[tagEnd..]);
//     } else if tag == 1{
//       p := CaseMarshalling1.Parsable(data[tagEnd..]);
//     } else {
//       p := CaseMarshalling2.Parsable(data[tagEnd..]);
//     }
//   }

//   method Parse(data: mseq<byte>) returns (value: UnmarshalledType)
//   {
//     var tagEnd := getTagEnd();
//     var tagOvalue := TGM.TryParse(data[..tagEnd]);
//     var tag := TGM.Int.toUint64(tagOvalue.value);

//     if tag == 0 {
//       var val := CaseMarshalling0.Parse(data[tagEnd..]);
//       value := Case0(val);
//     } else if tag == 1 {
//       var val := CaseMarshalling1.Parse(data[tagEnd..]);
//       value := Case1(val);
//     } else {
//       var val := CaseMarshalling2.Parse(data[tagEnd..]);
//       value := Case2(val);    
//     }
//   }

//   predicate marshallable(value: UnmarshalledType)
//   {
//     && TGM.Int.MinValue() <= 0 < 2 < TGM.Int.UpperBound()
//     && match value {
//       case Case0(c0) => CaseMarshalling0.marshallable(c0)
//       case Case1(c1) => CaseMarshalling1.marshallable(c1)
//       case Case2(c2) => CaseMarshalling2.marshallable(c2)
//     }
//   }

//   function size(value: UnmarshalledType) : nat
//   {
//     var tagEnd := getTagEnd();
//     match value {
//       case Case0(c0) => tagEnd as nat + CaseMarshalling0.size(c0)
//       case Case1(c1) => tagEnd as nat + CaseMarshalling1.size(c1)
//       case Case2(c2) => tagEnd as nat + CaseMarshalling2.size(c2)
//     }
//   }

//   method Size(value: UnmarshalledType) returns (sz: uint64)
//   {
//     sz := getTagEnd();
//     match value
//     case Case0(c0) => {
//       var size := CaseMarshalling0.Size(c0);
//       sz := sz + size;
//     }
//     case Case1(c1) => {
//       var size := CaseMarshalling1.Size(c1);
//       sz := sz + size;
//     }
//     case Case2(c2) => {
//       var size := CaseMarshalling2.Size(c2);
//       sz := sz + size;
//     }
//   }

//   method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
//     returns (linear newdata: mseq<byte>, end: uint64)
//   {
//     ghost var tagEnd : uint64 := getTagEnd();

//     match value
//     case Case0(c0) => {
//       newdata, end := TGM.Marshall(TGM.Int.fromUint64(0), data, start);
//       ghost var newdata1 :seq<byte>, end1 := newdata, end;
//       newdata, end := CaseMarshalling0.Marshall(c0, newdata, end);

//       assert newdata[start..end][..tagEnd] == newdata1[start..end1] == newdata[start..end1];
//       ghost var tag := TGM.Int.toInt(TGM.parse(newdata[start..end1]));
//       TGM.Int.fromtoInverses();
//       assert tag == 0;
//     }
//     case Case1(c1) => {
//       newdata, end := TGM.Marshall(TGM.Int.fromUint64(1), data, start);
//       ghost var newdata1 :seq<byte>, end1 := newdata, end;
//       newdata, end := CaseMarshalling1.Marshall(c1, newdata, end);
  
//       assert newdata1[start..end1] == newdata[start..end1];
//       ghost var tag := TGM.Int.toInt(TGM.parse(newdata[start..end1]));
//       TGM.Int.fromtoInverses();
//       assert tag == 1;

//       assert newdata[start..end][..tagEnd] == newdata[start..end1];
//     }
//     case Case2(c2) => {
//       newdata, end := TGM.Marshall(TGM.Int.fromUint64(2), data, start);
//       ghost var newdata1 :seq<byte>, end1 := newdata, end;
//       newdata, end := CaseMarshalling2.Marshall(c2, newdata, end);
  
//       assert newdata1[start..end1] == newdata[start..end1];
//       ghost var tag := TGM.Int.toInt(TGM.parse(newdata[start..end1]));
//       TGM.Int.fromtoInverses();
//       assert tag == 2;

//       assert newdata[start..end][..tagEnd] == newdata[start..end1];
//     }
//   }
// }