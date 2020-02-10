include "NativeTypes.s.dfy"

module {:extern} KeyType {
  import NativeTypes

  function method {:extern} MaxLen() : NativeTypes.uint64
  //type Key = s : seq<NativeTypes.byte> | |s| <= 20
  type Key(!new,==)

  function method {:extern} seq_to_key(s: seq<NativeTypes.byte>) : Key
  requires |s| <= 20

  function method {:extern} key_to_seq(k: Key) : seq<NativeTypes.byte>

  function method {:extern} KeyLenUint64(key: Key): NativeTypes.uint64

  function method {:extern} key_cmp(a: Key, b: Key): NativeTypes.int32

  method {:extern "KeyType_Compile", "CopyKeyIntoArray"} CopyKeyIntoArray(src:Key, dst:array<NativeTypes.byte>, dstIndex:NativeTypes.uint64)

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
