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

    // TODO make these async? any value from it?
    | GetOp(key: Key, value: Value)
    | PutOp(key: Key, value: Value)

    | SuccOp(start: RangeStart,
        results: seq<SuccResult>, end: RangeEnd)
}
