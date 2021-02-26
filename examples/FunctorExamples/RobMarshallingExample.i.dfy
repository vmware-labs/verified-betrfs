abstract module Marshalling {
  type Thing
}

abstract module IntegerMarshalling refines Marshalling {
  type Thing = int

  predicate intDiddle(foo: int, bar: Thing)
  {
    foo == bar
  }
}

module Uint32Marshalling refines IntegerMarshalling {
}

abstract module SeqMarshalling(ElementMarshalling : Marshalling)
{
  type Booger
  predicate smDoodle(foo: ElementMarshalling.Thing) {
    true
  }
}

module SeqMarshalling_applied_IntegerMarshalling
{
    import ElementMarshalling = IntegerMarshalling
}

module X {
    import SeqMarshalling(IntegerMarshalling)
}

module Y {
    import IM : IntegerMarshalling
    import F = SeqMarshalling(IM)
    predicate A(a: F.ElementMarshalling.Thing) { true }
}

module Z {
    import IM : IntegerMarshalling
    import G = SeqMarshalling(IM)
    import Y
    predicate A(a: G.ElementMarshalling.Thing) { Y.A(a) }
}

// So we know IM is the 1st parameter to SeqMarshalling, but we don't know which of SeqMarshalling's
// import:'s it refers to.
abstract module IntegerSeqMarshalling(IM : IntegerMarshalling) refines SeqMarshalling(IM)
{
  import IntegerMarshalling
  // ElementMarshallinng is IM, which is known to be an IntegerMarshalling. So Thing = int now, right?
  // I think I need to change SeqMarshalling to point to SeqMarshallingIM, in which ElementMarshalling has
  // been replaced with IntegerMarshalling.
  type Doo = IM.Thing
  predicate pick(booger: Booger) {
    true
  }

  predicate diddle(foo: int, bar: IntegerMarshalling.Thing)
  {
    && IM.intDiddle(foo, bar)
    && smDoodle(bar)    // smDoodle comes from SeqMarshalling_applied, which has had ElementMarshalling replaced with IM, right?
    && foo == bar
  }

  predicate daddle(foo: int, bar: Doo)
  {
    foo == bar
  }

  predicate dee(doo: Doo)
  { true }
}

//module Uint32SeqMarshalling refines IntegerSeqMarshalling(Uint32Marshalling)
//{
//}
