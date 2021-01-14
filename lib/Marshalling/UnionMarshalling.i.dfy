include "MarshalledAccessors.i.dfy"
// include "../Base/sequences.i.dfy"

abstract module Union2Marshalling refines Marshalling {
  import LeftMarshalling : Marshalling
  import RightMarshalling : Marshalling
  import TagMarshalling : IntegerMarshalling
  // import Sequences

  datatype UnionType = 
    | Left(l : LeftMarshalling.UnmarshalledType)
    | Right(r: RightMarshalling.UnmarshalledType)

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
    (if tag == 0 then LeftMarshalling.parsable(data[tagEnd..])
        else RightMarshalling.parsable(data[tagEnd..]))
  }

  function parse(data: mseq<byte>) : UnmarshalledType
  {
    var tagEnd := getTagEnd() as int;
    var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(data[..tagEnd]));

    if tag == 0 then Left(LeftMarshalling.parse(data[tagEnd..]))
      else Right(RightMarshalling.parse(data[tagEnd..]))
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
      var leftOvalue := LeftMarshalling.TryParse(data[tagEnd..]);
      if leftOvalue.Some? {
        ovalue := Some(Left(leftOvalue.value));
      }
    } else {
      var rightOvalue := RightMarshalling.TryParse(data[tagEnd..]);
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
      p := LeftMarshalling.Parsable(data[tagEnd..]);
    } else {
      p := RightMarshalling.Parsable(data[tagEnd..]);
    }
  }

  method Parse(data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var tagEnd := getTagEnd();
    var tagOvalue := TagMarshalling.TryParse(data[..tagEnd]);
    var tag := TagMarshalling.Int.toUint64(tagOvalue.value);

    if tag == 0 {
      var leftValue := LeftMarshalling.Parse(data[tagEnd..]);
      value := Left(leftValue);
    } else {
      var rightValue := RightMarshalling.Parse(data[tagEnd..]);
      value := Right(rightValue);
    }
  }

  predicate marshallable(value: UnmarshalledType)
  {
    && TagMarshalling.Int.MinValue() <= 0 < 1 < TagMarshalling.Int.UpperBound()
    && match value {
      case Left(leftValue) => LeftMarshalling.marshallable(leftValue)
      case Right(rightValue) => RightMarshalling.marshallable(rightValue)
    }
  }

  function size(value: UnmarshalledType) : nat
  {
    var tagEnd := getTagEnd();
    match value {
      case Left(leftValue) => tagEnd as nat + LeftMarshalling.size(leftValue)
      case Right(rightValue) => tagEnd as nat + RightMarshalling.size(rightValue)
    }
  }

  method Size(value: UnmarshalledType) returns (sz: uint64)
  {
    sz := getTagEnd();
    match value
    case Left(leftValue) => {
      var leftSize := LeftMarshalling.Size(leftValue);
      sz := sz + leftSize;
    }
    case Right(rightValue) => {
      var rightSize := RightMarshalling.Size(rightValue);
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
      newdata, end := LeftMarshalling.Marshall(leftValue, newdata, end);

      assert newdata1[start..end1] == newdata[start..end1];
      ghost var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(newdata[start..end1]));
      TagMarshalling.Int.fromtoInverses();
      assert tag == 0;

      assert newdata[start..end][..tagEnd] == newdata[start..end1];
    }
    case Right(rightValue) => {
      newdata, end := TagMarshalling.Marshall(TagMarshalling.Int.fromUint64(1), data, start);
      ghost var newdata1 :seq<byte>, end1 := newdata, end;
      newdata, end := RightMarshalling.Marshall(rightValue, newdata, end);
  
      assert newdata1[start..end1] == newdata[start..end1];
      ghost var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(newdata[start..end1]));
      TagMarshalling.Int.fromtoInverses();
      assert tag == 1;

      assert newdata[start..end][..tagEnd] == newdata[start..end1];
    }
  }
}