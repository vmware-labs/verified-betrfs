include "../lib/NativeTypes.dfy"
include "../lib/total_order.dfy"

module ValueWithDefault {
  import NativeTypes

  type Value(==,!new) = seq<NativeTypes.byte>
	function method DefaultValue() : Value { [] }

	export S provides Value, DefaultValue
	export Internal reveals *
	export extends S
}

module UI {
  //import Keyspace = Total_Order
  import Keyspace = Lexicographic_Byte_Order

  import V = ValueWithDefault
  type Key = Keyspace.Element
  type Value = V.Value

  datatype Op =
    | NoOp
    | SyncOp
    | CrashOp
    | PushSyncOp(id: int)
    | PopSyncOp(id: int)

    // TODO make these async? any value from it?
    | GetOp(key: Key, value: Value)
    | PutOp(key: Key, value: Value)
}
