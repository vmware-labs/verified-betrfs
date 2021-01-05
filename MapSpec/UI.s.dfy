include "../lib/Base/KeyType.s.dfy"

// Defines the "UI Op", used as labels on transitions of many of our
// state machines. These labels correspond to the user-visible behavior
// of the state machine. So for example: implementation handlers (Main.s.dfy)
// connect their inputs and outputs to the UI ops of the transitions they perform,
// and state machine refinements preserve UI ops. This is how we connect the
// behavior of our main handlers with the behavior of the MapSpec.

module {:extern} UI {
  //import Keyspace = Total_Order
  //import Keyspace = Lexicographic_Byte_Order

  import opened ValueType
  import opened KeyType

  datatype RangeStart = SInclusive(key: UKey) | SExclusive(key: UKey) | NegativeInf
  datatype RangeEnd = EInclusive(key: UKey) | EExclusive(key: UKey) | PositiveInf

  datatype SuccResult = SuccResult(key: UKey, value: Value)
  datatype SuccResultList = SuccResultList(results: seq<SuccResult>, end: RangeEnd)

  datatype Op =
    | NoOp
    | SyncOp
    | CrashOp
    | PushSyncOp(ghost id: int)
    | PopSyncOp(ghost id: int)

    | GetOp(key: UKey, value: Value)
    
    | GetBeginOp(key: UKey, ghost id: int)
    | GetEndOp(value: Value, ghost id: int)

    // TODO make this async? any value from it?
    | PutOp(key: UKey, value: Value)

    | SuccOp(start: RangeStart,
        results: seq<SuccResult>, end: RangeEnd)
}
