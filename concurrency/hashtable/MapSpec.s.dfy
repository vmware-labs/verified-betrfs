include "../../lib/Lang/NativeTypes.s.dfy"
include "../framework/StateMachines.s.dfy"

module KeyValueType {
  import opened NativeTypes

  type Key = uint64
  type Value(==)

  datatype QueryResult = Found(val: Value) | NotFound
}

module MapIfc refines InputOutputIfc {
  import opened KeyValueType

  datatype Input =
    | QueryInput(key: Key)
    | InsertInput(key: Key, value: Value)
    | RemoveInput(key: Key)

  datatype Output =
    | QueryOutput(res: QueryResult)
    | InsertOutput(success: bool) // an insert may fail when there is no capacity
    | RemoveOutput(existed: bool) // to Travis: added the possibility that there is nothing to remove
}

module MapSpec refines StateMachine(MapIfc) {
  import opened KeyValueType

  datatype Variables = Variables(m: map<Key, Value>)
  
  predicate Init(s: Variables)
  {
    s.m == map[]
  }

  predicate Next(s: Variables, s': Variables, op: ifc.Op)
  {
    match op {
      case Op(input, output) => (
        match input {
          case QueryInput(key) => 
            && s' == s
            && (key in s.m ==> output == ifc.QueryOutput(Found(s.m[key])))
            && (key !in s.m ==> output == ifc.QueryOutput(NotFound))
          case InsertInput(key, value) =>
           (
            && s' == s.(m := s.m[key := value])
            && output == ifc.InsertOutput(true)
           )
          //  ||
          //  (
          //   && s' == s
          //   && output == ifc.InsertOutput(false)
          //  )
          case RemoveInput(key) =>
            && s'.m == s.m - {key}
            && output == ifc.RemoveOutput(key in s.m)
        }
      )
    }
  }
}
