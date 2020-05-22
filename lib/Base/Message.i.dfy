include "KeyType.s.dfy"
include "../Lang/NativeTypes.s.dfy"
include "sequences.i.dfy"

//
// The messages propagated down a B-epsilon tree. Each message either
// completely defines the value of the key, or is a delta that modifies the
// value defined by prior messages.
//

// Delta forms a monoid with a monoid-action on the values
// (https://en.wikipedia.org/wiki/Monoid_action)

abstract module Message {
  type Value(!new)
	type Delta(!new)

	function method NopDelta() : Delta
	function method DefaultValue() : Value

	datatype Message =
	  | Define(value: Value)
	  | Update(delta: Delta)

	function method CombineDeltas(newdelta: Delta, olddelta: Delta) : (result: Delta)
	ensures newdelta == NopDelta() ==> result == olddelta
	ensures olddelta == NopDelta() ==> result == newdelta

	function method ApplyDelta(delta: Delta, value: Value) : (result: Value)
	ensures delta == NopDelta() ==> result == value

	function method Merge(newmessage: Message, oldmessage: Message) : Message {
		match (newmessage, oldmessage) {
			case (Define(newvalue), _) => Define(newvalue)
			case (Update(newdelta), Update(olddelta)) => Update(CombineDeltas(newdelta, olddelta))
			case (Update(delta), Define(value)) => Define(ApplyDelta(delta, value))
		}
	}

	function method IdentityMessage() : Message {
	  Update(NopDelta())
  }

	function method DefineDefault() : Message {
	  Define(DefaultValue())
  }

	lemma DeltaIsAssociative(a: Delta, b: Delta, c: Delta)
		ensures CombineDeltas(CombineDeltas(a, b), c) == CombineDeltas(a, CombineDeltas(b, c))

	lemma ApplyIsAssociative(a: Delta, b: Delta, value: Value)
		ensures ApplyDelta(CombineDeltas(a, b), value) == ApplyDelta(a, ApplyDelta(b, value))

	lemma MergeIsAssociative(a: Message, b: Message, c: Message)
		ensures Merge(Merge(a, b), c) == Merge(a, Merge(b, c))
		{
			match a {
			  case Define(a) => { }
			  case Update(a) => {
			    match b {
            case Define(b) => { }
            case Update(b) => {
              match c {
                case Define(c) => {
                  ApplyIsAssociative(a, b, c);
                }
                case Update(c) => {
                  DeltaIsAssociative(a, b, c);
                }
              }
            }
			    }
			  }
			}
		}
}

module ValueMessage refines Message {
  import ValueType`Internal
  import opened NativeTypes
  import opened Sequences
  
  type Value = ValueType.Value
  datatype Delta = NoDelta

  function method NopDelta() : Delta { NoDelta }
  function method DefaultValue() : Value { ValueType.DefaultValue() }

  function method CombineDeltas(newdelta: Delta, olddelta: Delta) : Delta { NoDelta }
  function method ApplyDelta(delta: Delta, value: Value) : Value { value }

	lemma DeltaIsAssociative(a: Delta, b: Delta, c: Delta)
	{
	}

	lemma ApplyIsAssociative(a: Delta, b: Delta, value: Value)
	{
	}

  function method bytestring_to_Message(s: seq<byte>) : Message
  requires |s| < 0x1_0000_0000
  {
    if |s| as uint64 <= ValueType.MaxLen() then (
      Define(s)
    ) else (
      // NOTE(travis)
      // It's just convenient to make this function total, so
      // we just do this if the byte string is invalid.
      Define(ValueType.DefaultValue())
    )
  }

  predicate EncodableMessage(msg: Message)
  {
    && msg.Define?
  }

  predicate EncodableMessageSeq(msgs: seq<Message>)
  {
    && (forall i | 0 <= i < |msgs| :: EncodableMessage(msgs[i]))
  }

  function method Message_to_bytestring(msg: Message) : seq<byte>
    requires msg.Define?
  {
    msg.value
  }
  
  function messageSeq_to_bytestringSeq(msgs: seq<Message>) : (result: seq<seq<byte>>)
    requires EncodableMessageSeq(msgs)
    ensures |result| == |msgs|
    ensures forall i | 0 <= i < |result| :: result[i] == Message_to_bytestring(msgs[i])
  {
    if |msgs| == 0 then
      []
    else
      messageSeq_to_bytestringSeq(Sequences.DropLast(msgs)) + [ Message_to_bytestring(Last(msgs)) ]
  }

  function bytestringSeq_to_MessageSeq(strings: seq<seq<byte>>) : (result: seq<Message>)
    requires forall i | 0 <= i < |strings| :: |strings[i]| < 0x1_0000_0000
    ensures |result| == |strings|
    ensures forall i | 0 <= i < |strings| :: result[i] == bytestring_to_Message(strings[i])
  {
    if |strings| == 0 then
      []
    else
      bytestringSeq_to_MessageSeq(Sequences.DropLast(strings)) + [ bytestring_to_Message(Last(strings)) ]
  }

  lemma bytestringSeq_to_MessageSeq_Additive(msgs1: seq<seq<byte>>, msgs2: seq<seq<byte>>)
    requires forall i | 0 <= i < |msgs1| :: |msgs1[i]| < 0x1_0000_0000
    requires forall i | 0 <= i < |msgs2| :: |msgs2[i]| < 0x1_0000_0000
    ensures bytestringSeq_to_MessageSeq(msgs1 + msgs2) == bytestringSeq_to_MessageSeq(msgs1) + bytestringSeq_to_MessageSeq(msgs2)
  {
  }
  
  lemma messageSeq_to_bytestringSeq_Additive(msgs1: seq<Message>, msgs2: seq<Message>)
    requires EncodableMessageSeq(msgs1)
    requires EncodableMessageSeq(msgs2)
    ensures EncodableMessageSeq(msgs1 + msgs2)
    ensures messageSeq_to_bytestringSeq(msgs1 + msgs2) == messageSeq_to_bytestringSeq(msgs1) + messageSeq_to_bytestringSeq(msgs2)
  {
  }
  
  method MessageArray_to_bytestringSeq(msgs: array<Message>, nmsgs: uint64) returns (result: seq<seq<byte>>)
    requires nmsgs as nat <= msgs.Length
    requires EncodableMessageSeq(msgs[..nmsgs])
    ensures result[..] == messageSeq_to_bytestringSeq(msgs[..nmsgs])
  {
    var aresult := new seq<byte>[nmsgs];
    var i: uint64 := 0;

    while i < nmsgs
      invariant i <= nmsgs
      invariant aresult[..i] == messageSeq_to_bytestringSeq(msgs[..i])
    {
      aresult[i] := Message_to_bytestring(msgs[i]);
      i := i + 1;
    }

    result := aresult[..i];
  }

  
  
	export S provides * reveals Message, Merge, IdentityMessage, DefineDefault, Value
	export extends S
	export Internal reveals *
}

// module IntMessage refines Message {
// 	type Value = int
// 	type Delta = int	
// 
// 	function NopDelta() : Delta {
// 		0
// 	}
// 
// 	function DefaultValue() : Value {
// 		0
// 	}
// 
// 	function CombineDeltas(newdelta: Delta, olddelta: Delta) : Delta {
// 		newdelta + olddelta
// 	}
// 
// 	function ApplyDelta(delta: Delta, value: Value) : Value {
// 		value + delta
// 	}
// 
// 	lemma DeltaIsAssociative(a: Delta, b: Delta, c: Delta)
// 		ensures CombineDeltas(CombineDeltas(a, b), c) == CombineDeltas(a, CombineDeltas(b, c))
// 		{ }
// 
// 	lemma ApplyIsAssociative(a: Delta, b: Delta, value: Value)
// 		ensures ApplyDelta(CombineDeltas(a, b), value) == ApplyDelta(a, ApplyDelta(b, value))
// 		{ }
// }

