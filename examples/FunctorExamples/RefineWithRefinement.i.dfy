abstract module Marshalling {
  type Thing
}
 
abstract module IntegerMarshalling refines Marshalling {
  type Thing = int
}
 
abstract module SeqMarshalling
{
  import ElementMarshalling : Marshalling
}

abstract module IntegerSeqMarshalling refines SeqMarshalling
{
  import IM : IntegerMarshalling
  import ElementMarshalling = IM
  predicate x(a:int) { true }
  predicate y(b:ElementMarshalling.Thing) { x(b) }
}

