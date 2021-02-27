// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

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
