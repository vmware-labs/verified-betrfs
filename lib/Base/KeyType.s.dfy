include "NativeTypes.s.dfy"

module {:extern} KeyType {
  import NativeTypes

  function method MaxLen() : NativeTypes.uint64 { 1024 }
  type Key = s : seq<NativeTypes.byte> | |s| <= 1024
}

module {:extern} ValueType {
  import NativeTypes

  function method MaxLen() : NativeTypes.uint64 { 1024 }
  type Value(==,!new) = s : seq<NativeTypes.byte> | |s| <= 1024
	function method DefaultValue() : Value { [] }

	function Len(v: Value) : nat { |v| }

	export S provides Value, DefaultValue, Len
	export Internal reveals *
	export extends S
}
