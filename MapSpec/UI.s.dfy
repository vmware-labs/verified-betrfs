include "../lib/Base/KeyType.s.dfy"

module {:extern} UI {
  //import Keyspace = Total_Order
  //import Keyspace = Lexicographic_Byte_Order

  import opened ValueType
  import opened KeyType

  datatype RangeStart = SInclusive(key: Key) | SExclusive(key: Key) | NegativeInf
  datatype RangeEnd = EInclusive(key: Key) | EExclusive(key: Key) | PositiveInf

  datatype SuccResult = SuccResult(key: Key, value: Value)
  datatype SuccResultList = SuccResultList(results: seq<SuccResult>, end: RangeEnd)

  datatype Op =
    | NoOp
    | SyncOp
    | CrashOp
    | PushSyncOp(ghost id: int)
    | PopSyncOp(ghost id: int)

    | GetOp(key: Key, value: Value)
    
    | GetBeginOp(key: Key, ghost id: int)
    | GetEndOp(value: Value, ghost id: int)

    // TODO make this async? any value from it?
    | PutOp(key: Key, value: Value)

    | SuccOp(start: RangeStart,
        results: seq<SuccResult>, end: RangeEnd)
}
