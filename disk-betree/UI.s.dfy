include "../lib/Base/NativeTypes.s.dfy"

module {:extern} KeyType {
  import NativeTypes

  function method MaxLen() : NativeTypes.uint64 { 1024 }
  type Key = s : seq<NativeTypes.byte> | |s| <= 1024
}

module {:extern} ValueWithDefault {
  import NativeTypes

  function method MaxLen() : NativeTypes.uint64 { 1024 }
  type Value(==,!new) = s : seq<NativeTypes.byte> | |s| <= 1024
	function method DefaultValue() : Value { [] }

	function Len(v: Value) : nat { |v| }

	export S provides Value, DefaultValue, Len
	export Internal reveals *
	export extends S
}

module UI {
  //import Keyspace = Total_Order
  //import Keyspace = Lexicographic_Byte_Order

  import V = ValueWithDefault
  import K = KeyType

  type Value = V.Value
  type Key = K.Key

  datatype Op =
    | NoOp
    | SyncOp
    | CrashOp
    | PushSyncOp(ghost id: int)
    | PopSyncOp(ghost id: int)

    // TODO make these async? any value from it?
    | GetOp(key: Key, value: Value)
    | PutOp(key: Key, value: Value)
}
