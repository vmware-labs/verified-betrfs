include "MarshalledAccessors.i.dfy"
// include "../Base/sequences.i.dfy"

abstract module Union2Marshalling(
  TagInt: NativePackedInt,
  CaseMarshalling0: Marshalling,
  CaseMarshalling1: Marshalling)
refines Marshalling {
  
  import TGM = IntegerMarshalling(TagInt)

  datatype UnmarshalledType = 
    | Case0(l : CaseMarshalling0.UnmarshalledType)
    | Case1(r: CaseMarshalling1.UnmarshalledType)

  datatype Config = Config(tgmCfg: TGM.Config,
    elemCfg0: CaseMarshalling0.Config,
    elemCfg1: CaseMarshalling1.Config)

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

    if tag == 0 then Case0(CaseMarshalling0.parse(cfg.elemCfg0, data[tagEnd..]))
      else Case1(CaseMarshalling1.parse(cfg.elemCfg1, data[tagEnd..]))
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
      ovalue := Some(Case0(left));
    } else {
      var right :- CaseMarshalling1.TryParse(cfg.elemCfg1, data[tagEnd..]);
      ovalue := Some(Case1(right));
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
      return Case0(leftValue);
    } else {
      var rightValue := CaseMarshalling1.Parse(cfg.elemCfg1, data[tagEnd..]);
      return Case1(rightValue);
    }
  }

  predicate marshallable(cfg: Config, value: UnmarshalledType)
  {
    && TagInt.MinValue() <= 0 < 1 < TagInt.UpperBound()
    && match value {
      case Case0(leftValue) =>
        (&& CaseMarshalling0.marshallable(cfg.elemCfg0, leftValue)
        && getTagEnd() as nat + CaseMarshalling0.size(cfg.elemCfg0, leftValue) as nat < Uint64UpperBound())
      case Case1(rightValue) =>
        (&& CaseMarshalling1.marshallable(cfg.elemCfg1, rightValue)
        && getTagEnd() as nat + CaseMarshalling1.size(cfg.elemCfg1, rightValue) as nat < Uint64UpperBound())
    }
  }

  function size(cfg: Config, value: UnmarshalledType) : uint64
  {
    var tagEnd := getTagEnd();
    match value {
      case Case0(leftValue) => tagEnd + CaseMarshalling0.size(cfg.elemCfg0, leftValue)
      case Case1(rightValue) => tagEnd + CaseMarshalling1.size(cfg.elemCfg1, rightValue)
    }
  }

  method Size(cfg: Config, value: UnmarshalledType) returns (sz: uint64)
  {
    sz := getTagEnd();
    match value {
      case Case0(leftValue) => {
        var leftSize := CaseMarshalling0.Size(cfg.elemCfg0, leftValue);
        sz := sz + leftSize;
      }
      case Case1(rightValue) => {
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
    case Case0(leftValue) => {
      end := TGM.Marshall(cfg.tgmCfg, 0, inout data, start);
      ghost var newdata1 :seq<byte>, end1 := data, end;
      end := CaseMarshalling0.Marshall(cfg.elemCfg0, leftValue, inout data, end);

      assert newdata1[start..end1] == data[start..end1];
      assert data[start..end][..tagEnd] == data[start..end1];
    }
    case Case1(rightValue) => {
      end := TGM.Marshall(cfg.tgmCfg, 1, inout data, start);
      ghost var newdata1 :seq<byte>, end1 := data, end;
      end := CaseMarshalling0.Marshall(cfg.elemCfg1, rightValue, inout data, end);

      assert newdata1[start..end1] == data[start..end1];
      assert data[start..end][..tagEnd] == data[start..end1];
    }
  }

  predicate settable(cfg: Config, slice: Slice, data: mseq<byte>, value: UnmarshalledType)
  {
    && validConfig(cfg)
    && marshallable(cfg, value)
    && slice.WF'(data)
    && size(cfg, value) <= |slice|
  }

  // method Set(cfg: Config, slice: Slice, linear inout data: mseq<byte>, value: UnmarshalledType)
  //   requires settable(cfg, slice, old_data, value)
  // {

  // }
}