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

  function method tagSize(): uint64
  {
    TagMarshalling.Int.Size() as uint64
  }

  predicate parsable(data: mseq<byte>)
  {
    var tagSize := tagSize() as int;
    && |data| >= tagSize
    && TagMarshalling.parsable(data[..tagSize])
    && TagMarshalling.Int.fitsInUint64(TagMarshalling.parse(data[..tagSize]))
    && var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(data[..tagSize]));
    (if tag == 0 then LeftMarshalling.parsable(data[tagSize..])
        else RightMarshalling.parsable(data[tagSize..]))
  }

  function parse(data: mseq<byte>) : UnmarshalledType
  {
    var tagSize := tagSize() as int;
    var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(data[..tagSize]));

    if tag == 0 then Left(LeftMarshalling.parse(data[tagSize..]))
      else Right(RightMarshalling.parse(data[tagSize..]))
  }

  method TryParse(data: mseq<byte>) returns (ovalue: Option<UnmarshalledType>)
  {
    var tagSize := tagSize();

    if tagSize > |data| as uint64 {
      return None;
    }

    var tagOvalue := TagMarshalling.TryParse(data[..tagSize]);
    
    if tagOvalue.None? {
      return None;
    }

    if !TagMarshalling.Int.fitsInUint64(tagOvalue.value) {
      return None;
    }

    var tag := TagMarshalling.Int.toUint64(tagOvalue.value);
    ovalue := None;

    if tag == 0 {
      var leftOvalue := LeftMarshalling.TryParse(data[tagSize..]);
      if leftOvalue.Some? {
        ovalue := Some(Left(leftOvalue.value));
      }
    } else {
      var rightOvalue := RightMarshalling.TryParse(data[tagSize..]);
      if rightOvalue.Some? {
        ovalue := Some(Right(rightOvalue.value));
      }
    }

  }

  method Parsable(data: mseq<byte>) returns (p: bool)
  {
    var tagSize := tagSize();

    if tagSize > |data| as uint64 {
      return false;
    }

    var tagOvalue := TagMarshalling.TryParse(data[..tagSize]);
    
    if tagOvalue.None? {
      return false;
    }

    if !TagMarshalling.Int.fitsInUint64(tagOvalue.value) {
      return false;
    }

    var tag := TagMarshalling.Int.toUint64(tagOvalue.value);

    if tag == 0 {
      p := LeftMarshalling.Parsable(data[tagSize..]);
    } else {
      p := RightMarshalling.Parsable(data[tagSize..]);
    }
  }

  method Parse(data: mseq<byte>) returns (value: UnmarshalledType)
  {
    var tagSize := tagSize();
    var tagOvalue := TagMarshalling.TryParse(data[..tagSize]);
    var tag := TagMarshalling.Int.toUint64(tagOvalue.value);

    if tag == 0 {
      var leftValue := LeftMarshalling.Parse(data[tagSize..]);
      value := Left(leftValue);
    } else {
      var rightValue := RightMarshalling.Parse(data[tagSize..]);
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
    var tagSize := tagSize();
    match value {
      case Left(leftValue) => tagSize as nat + LeftMarshalling.size(leftValue)
      case Right(rightValue) => tagSize as nat + RightMarshalling.size(rightValue)
    }
  }

  method Size(value: UnmarshalledType) returns (sz: uint64)
  {
    sz := tagSize();
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
    ghost var tagSize : uint64 := tagSize();

    match value
    case Left(leftValue) => {
      newdata, end := TagMarshalling.Marshall(TagMarshalling.Int.fromUint64(0), data, start);
      ghost var newdata1 :seq<byte>, end1 := newdata, end;
      newdata, end := LeftMarshalling.Marshall(leftValue, newdata, end);

      assert newdata1[start..end1] == newdata[start..end1];
      ghost var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(newdata[start..end1]));
      TagMarshalling.Int.fromtoInverses();
      assert tag == 0;

      assert newdata[start..end][..tagSize] == newdata[start..end1];
    }
    case Right(rightValue) => {
      newdata, end := TagMarshalling.Marshall(TagMarshalling.Int.fromUint64(1), data, start);
      ghost var newdata1 :seq<byte>, end1 := newdata, end;
      newdata, end := RightMarshalling.Marshall(rightValue, newdata, end);
  
      assert newdata1[start..end1] == newdata[start..end1];
      ghost var tag := TagMarshalling.Int.toInt(TagMarshalling.parse(newdata[start..end1]));
      TagMarshalling.Int.fromtoInverses();
      assert tag == 1;

      assert newdata[start..end][..tagSize] == newdata[start..end1];
    }
  }
}