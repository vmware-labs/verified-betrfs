include "MarshalledAccessors.i.dfy"
// include "../Base/sequences.i.dfy"

abstract module Union2Marshalling refines Marshalling {
  import CaseMarshalling0 : Marshalling
  import CaseMarshalling1 : Marshalling
  import TagMarshalling : IntegerMarshalling
  // import Sequences

  datatype UnionType = 
    | Left(l : CaseMarshalling0.UnmarshalledType)
    | Right(r: CaseMarshalling1.UnmarshalledType)

  type UnmarshalledType = UnionType

  type TagType = TagMarshalling.UnmarshalledType

  function method getTagEnd(): uint64
  {
    TagMarshalling.Int.Size() as uint64
  }

  predicate parsable(data: mseq<byte>)
  {
    var tagEnd := getTagEnd() as int;
    && |data| >= tagEnd
    && TagMarshalling.parsable(data[..tagEnd])
    && TagMarshalling.Int.fitsInUint64(TagMarshalling.parse(data[..tagEnd]))
    && var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(data[..tagEnd]));
    (if tag == 0 then CaseMarshalling0.parsable(data[tagEnd..])
        else CaseMarshalling1.parsable(data[tagEnd..]))
  }

  function parse(data: mseq<byte>) : UnmarshalledType
  {
    var tagEnd := getTagEnd() as int;
    var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(data[..tagEnd]));

    if tag == 0 then Left(CaseMarshalling0.parse(data[tagEnd..]))
      else Right(CaseMarshalling1.parse(data[tagEnd..]))
  }

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var tagEnd := getTagEnd();

    if tagEnd > |data| as uint64 {
      return None;
    }

    var tagOvalue := TagMarshalling.TryParse(data[..tagEnd]);
    
    if tagOvalue.None? {
      return None;
    }

    if !TagMarshalling.Int.fitsInUint64(tagOvalue.value) {
      return None;
    }

    var tag := TagMarshalling.Int.toUint64(tagOvalue.value);
    ovalue := None;

    if tag == 0 {
      var leftOvalue := CaseMarshalling0.TryParse(data[tagEnd..]);
      if leftOvalue.Some? {
        ovalue := Some(Left(leftOvalue.value));
      }
    } else {
      var rightOvalue := CaseMarshalling1.TryParse(data[tagEnd..]);
      if rightOvalue.Some? {
        ovalue := Some(Right(rightOvalue.value));
      }
    }

  }

  method Parsable(data: mseq<byte>) returns (p: bool)
  {
    var tagEnd := getTagEnd();

    if tagEnd > |data| as uint64 {
      return false;
    }

    var tagOvalue := TagMarshalling.TryParse(data[..tagEnd]);
    
    if tagOvalue.None? {
      return false;
    }

    if !TagMarshalling.Int.fitsInUint64(tagOvalue.value) {
      return false;
    }

    var tag := TagMarshalling.Int.toUint64(tagOvalue.value);

    if tag == 0 {
      p := CaseMarshalling0.Parsable(data[tagEnd..]);
    } else {
      p := CaseMarshalling1.Parsable(data[tagEnd..]);
    }
  }

  method Parse(data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var tagEnd := getTagEnd();
    var tagOvalue := TagMarshalling.TryParse(data[..tagEnd]);
    var tag := TagMarshalling.Int.toUint64(tagOvalue.value);

    if tag == 0 {
      var leftValue := CaseMarshalling0.Parse(data[tagEnd..]);
      value := Left(leftValue);
    } else {
      var rightValue := CaseMarshalling1.Parse(data[tagEnd..]);
      value := Right(rightValue);
    }
  }

  predicate marshallable(value: UnmarshalledType)
  {
    && TagMarshalling.Int.MinValue() <= 0 < 1 < TagMarshalling.Int.UpperBound()
    && match value {
      case Left(leftValue) => CaseMarshalling0.marshallable(leftValue)
      case Right(rightValue) => CaseMarshalling1.marshallable(rightValue)
    }
  }

  function size(value: UnmarshalledType) : nat
  {
    var tagEnd := getTagEnd();
    match value {
      case Left(leftValue) => tagEnd as nat + CaseMarshalling0.size(leftValue)
      case Right(rightValue) => tagEnd as nat + CaseMarshalling1.size(rightValue)
    }
  }

  method Size(value: UnmarshalledType) returns (sz: uint64)
  {
    sz := getTagEnd();
    match value
    case Left(leftValue) => {
      var leftSize := CaseMarshalling0.Size(leftValue);
      sz := sz + leftSize;
    }
    case Right(rightValue) => {
      var rightSize := CaseMarshalling1.Size(rightValue);
      sz := sz + rightSize;
    }
  }

  method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
    returns (linear newdata: mseq<byte>, end: uint64)
  {
    ghost var tagEnd : uint64 := getTagEnd();

    match value
    case Left(leftValue) => {
      newdata, end := TagMarshalling.Marshall(TagMarshalling.Int.fromUint64(0), data, start);
      ghost var newdata1 :seq<byte>, end1 := newdata, end;
      newdata, end := CaseMarshalling0.Marshall(leftValue, newdata, end);

      assert newdata1[start..end1] == newdata[start..end1];
      ghost var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(newdata[start..end1]));
      TagMarshalling.Int.fromtoInverses();
      assert tag == 0;

      assert newdata[start..end][..tagEnd] == newdata[start..end1];
    }
    case Right(rightValue) => {
      newdata, end := TagMarshalling.Marshall(TagMarshalling.Int.fromUint64(1), data, start);
      ghost var newdata1 :seq<byte>, end1 := newdata, end;
      newdata, end := CaseMarshalling1.Marshall(rightValue, newdata, end);
  
      assert newdata1[start..end1] == newdata[start..end1];
      ghost var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(newdata[start..end1]));
      TagMarshalling.Int.fromtoInverses();
      assert tag == 1;

      assert newdata[start..end][..tagEnd] == newdata[start..end1];
    }
  }
}


abstract module Union3Marshalling refines Marshalling {
  import CaseMarshalling0 : Marshalling
  import CaseMarshalling1 : Marshalling
  import CaseMarshalling2 : Marshalling
  import TagMarshalling : IntegerMarshalling
  // import Sequences

  datatype UnionType = 
    | Case0(c0: CaseMarshalling0.UnmarshalledType)
    | Case1(c1: CaseMarshalling1.UnmarshalledType)
    | Case2(c2: CaseMarshalling2.UnmarshalledType)

  type UnmarshalledType = UnionType

  type TagType = TagMarshalling.UnmarshalledType

  function method getTagEnd(): uint64
  {
    TagMarshalling.Int.Size() as uint64
  }

  predicate parsable(data: mseq<byte>)
  {
    var tagEnd := getTagEnd() as int;
    && |data| >= tagEnd
    && TagMarshalling.parsable(data[..tagEnd])
    && TagMarshalling.Int.fitsInUint64(TagMarshalling.parse(data[..tagEnd]))
    && var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(data[..tagEnd]));
    (if tag == 0 then CaseMarshalling0.parsable(data[tagEnd..])
      else if tag == 1 then CaseMarshalling1.parsable(data[tagEnd..])
      else CaseMarshalling2.parsable(data[tagEnd..]))
  }

  function parse(data: mseq<byte>) : UnmarshalledType
  {
    var tagEnd := getTagEnd() as int;
    var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(data[..tagEnd]));

    if tag == 0 then Case0(CaseMarshalling0.parse(data[tagEnd..]))
      else if tag == 1 then Case1(CaseMarshalling1.parse(data[tagEnd..]))
      else Case2(CaseMarshalling2.parse(data[tagEnd..]))
  }

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var tagEnd := getTagEnd();

    if tagEnd > |data| as uint64 {
      return None;
    }

    var tagOvalue := TagMarshalling.TryParse(data[..tagEnd]);
    
    if tagOvalue.None? {
      return None;
    }

    if !TagMarshalling.Int.fitsInUint64(tagOvalue.value) {
      return None;
    }

    var tag := TagMarshalling.Int.toUint64(tagOvalue.value);
    ovalue := None;

    if tag == 0 {
      var valueOpt := CaseMarshalling0.TryParse(data[tagEnd..]);
      if valueOpt.Some? {
        ovalue := Some(Case0(valueOpt.value));
      }
    } else if tag == 1 {
      var valueOpt := CaseMarshalling1.TryParse(data[tagEnd..]);
      if valueOpt.Some? {
        ovalue := Some(Case1(valueOpt.value));
      }
    } else {
      var valueOpt := CaseMarshalling2.TryParse(data[tagEnd..]);
      if valueOpt.Some? {
        ovalue := Some(Case2(valueOpt.value));
      }
    }
  }

  method Parsable(data: mseq<byte>) returns (p: bool)
  {
    var tagEnd := getTagEnd();

    if tagEnd > |data| as uint64 {
      return false;
    }

    var tagOvalue := TagMarshalling.TryParse(data[..tagEnd]);
    
    if tagOvalue.None? {
      return false;
    }

    if !TagMarshalling.Int.fitsInUint64(tagOvalue.value) {
      return false;
    }

    var tag := TagMarshalling.Int.toUint64(tagOvalue.value);

    if tag == 0 {
      p := CaseMarshalling0.Parsable(data[tagEnd..]);
    } else if tag == 1{
      p := CaseMarshalling1.Parsable(data[tagEnd..]);
    } else {
      p := CaseMarshalling2.Parsable(data[tagEnd..]);
    }
  }

  method Parse(data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var tagEnd := getTagEnd();
    var tagOvalue := TagMarshalling.TryParse(data[..tagEnd]);
    var tag := TagMarshalling.Int.toUint64(tagOvalue.value);

    if tag == 0 {
      var val := CaseMarshalling0.Parse(data[tagEnd..]);
      value := Case0(val);
    } else if tag == 1 {
      var val := CaseMarshalling1.Parse(data[tagEnd..]);
      value := Case1(val);
    } else {
      var val := CaseMarshalling2.Parse(data[tagEnd..]);
      value := Case2(val);    
    }
  }

  predicate marshallable(value: UnmarshalledType)
  {
    && TagMarshalling.Int.MinValue() <= 0 < 2 < TagMarshalling.Int.UpperBound()
    && match value {
      case Case0(c0) => CaseMarshalling0.marshallable(c0)
      case Case1(c1) => CaseMarshalling1.marshallable(c1)
      case Case2(c2) => CaseMarshalling2.marshallable(c2)
    }
  }

  function size(value: UnmarshalledType) : nat
  {
    var tagEnd := getTagEnd();
    match value {
      case Case0(c0) => tagEnd as nat + CaseMarshalling0.size(c0)
      case Case1(c1) => tagEnd as nat + CaseMarshalling1.size(c1)
      case Case2(c2) => tagEnd as nat + CaseMarshalling2.size(c2)
    }
  }

  method Size(value: UnmarshalledType) returns (sz: uint64)
  {
    sz := getTagEnd();
    match value
    case Case0(c0) => {
      var size := CaseMarshalling0.Size(c0);
      sz := sz + size;
    }
    case Case1(c1) => {
      var size := CaseMarshalling1.Size(c1);
      sz := sz + size;
    }
    case Case2(c2) => {
      var size := CaseMarshalling2.Size(c2);
      sz := sz + size;
    }
  }

  method Marshall(value: UnmarshalledType, linear data: mseq<byte>, start: uint64)
    returns (linear newdata: mseq<byte>, end: uint64)
  {
    ghost var tagEnd : uint64 := getTagEnd();

    match value
    case Case0(c0) => {
      newdata, end := TagMarshalling.Marshall(TagMarshalling.Int.fromUint64(0), data, start);
      ghost var newdata1 :seq<byte>, end1 := newdata, end;
      newdata, end := CaseMarshalling0.Marshall(c0, newdata, end);

      assert newdata1[start..end1] == newdata[start..end1];
      ghost var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(newdata[start..end1]));
      TagMarshalling.Int.fromtoInverses();
      assert tag == 0;

      assert newdata[start..end][..tagEnd] == newdata[start..end1];
    }
    case Case1(c1) => {
      newdata, end := TagMarshalling.Marshall(TagMarshalling.Int.fromUint64(1), data, start);
      ghost var newdata1 :seq<byte>, end1 := newdata, end;
      newdata, end := CaseMarshalling1.Marshall(c1, newdata, end);
  
      assert newdata1[start..end1] == newdata[start..end1];
      ghost var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(newdata[start..end1]));
      TagMarshalling.Int.fromtoInverses();
      assert tag == 1;

      assert newdata[start..end][..tagEnd] == newdata[start..end1];
    }
    case Case2(c2) => {
      newdata, end := TagMarshalling.Marshall(TagMarshalling.Int.fromUint64(2), data, start);
      ghost var newdata1 :seq<byte>, end1 := newdata, end;
      newdata, end := CaseMarshalling2.Marshall(c2, newdata, end);
  
      assert newdata1[start..end1] == newdata[start..end1];
      ghost var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(newdata[start..end1]));
      TagMarshalling.Int.fromtoInverses();
      assert tag == 2;

      assert newdata[start..end][..tagEnd] == newdata[start..end1];
    }
  }
}