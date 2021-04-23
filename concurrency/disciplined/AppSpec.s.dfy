// This is the application-specific part of the spec.
// It first describes the abstract-level interface
// (the inputs and outputs that label the transitions of a state machine),
// and then the semantics (the state & transitions of the state machine).

include "InputOutputIfc.s.dfy"

module KeyValueType {
  import opened NativeTypes

  type Key = uint64
  type Value(==)

  datatype QueryResult = Found(val: Value) | NotFound
}

module MapSpec {
  import opened KeyValueType

  import Ifc = MapIfc
  datatype Variables = Variables(m: map<Key, Value>)

  predicate Init(s: Variables) {
    s.m == map[]
  }

  predicate Next(s: Variables, s': Variables, op: Ifc.Op) {
    match op {
      case Op(input, output) => (
        match input {
          case QueryInput(key) => 
            && s' == s
            && (key in s.m ==> output == Ifc.QueryOutput(Found(s.m[key])))
            && (key !in s.m ==> output == Ifc.QueryOutput(NotFound))
          case InsertInput(key, value) =>
           (
            && s' == s.(m := s.m[key := value])
            && output == Ifc.InsertOutput(true)
           )
           ||
           (
            && s' == s
            && output == Ifc.InsertOutput(false)
           )
          case RemoveInput(key) =>
            && s'.m == s.m - {key}
            && output == Ifc.RemoveOutput(key in s.m)
        }
      )
    }
  }
}
