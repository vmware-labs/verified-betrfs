include "MarshalledAccessors.i.dfy"

abstract module Tuple2Marshalling refines Marshalling {
  import FstMarshalling : Marshalling
  import SndMarshalling : Marshalling

  type UnmarshalledType = (FstMarshalling.UnmarshalledType, SndMarshalling.UnmarshalledType)

}
