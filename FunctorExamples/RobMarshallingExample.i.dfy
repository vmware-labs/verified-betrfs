abstract module Marshalling {
  type Thing
}

abstract module IntegerMarshalling refines Marshalling {
  type Thing = int
}

module Uint32Marshalling refines IntegerMarshalling {
}

abstract module SeqMarshalling(ElementMarshalling : Marshalling)
{
  type Booger
}

abstract module IntegerSeqMarshalling(IM : IntegerMarshalling) refines SeqMarshalling(IntegerMarshalling)
{
  type Doo = ElementMarshalling.Thing
}

//module Uint32SeqMarshalling refines IntegerSeqMarshalling(Uint32Marshalling)
//{
//}
