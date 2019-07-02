include "MapSpec.dfy"

// Delta forms a monoid with a monoid-action on the values
// (https://en.wikipedia.org/wiki/Monoid_action)

abstract module Message {
  type Value(!new)
	type Delta(!new)

	function NopDelta() : Delta
	function DefaultValue() : Value

	datatype Message =
	  | Define(value: Value)
	  | Update(delta: Delta)

	function CombineDeltas(newdelta: Delta, olddelta: Delta) : (result: Delta)
	ensures newdelta == NopDelta() ==> result == olddelta
	ensures olddelta == NopDelta() ==> result == newdelta

	function ApplyDelta(delta: Delta, value: Value) : (result: Value)
	ensures delta == NopDelta() ==> result == value

	function Merge(newmessage: Message, oldmessage: Message) : Message {
		match (newmessage, oldmessage) {
			case (Define(newvalue), _) => Define(newvalue)
			case (Update(newdelta), Update(olddelta)) => Update(CombineDeltas(newdelta, olddelta))
			case (Update(delta), Define(value)) => Define(ApplyDelta(delta, value))
		}
	}

	function IdentityMessage() : Message {
	  Update(NopDelta())
  }

	function DefineDefault() : Message {
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
  import V = ValueWithDefault

  type Value = V.Value
  datatype Delta = NoDelta

  function NopDelta() : Delta { NoDelta }
  function DefaultValue() : Value { V.DefaultValue() }

  function CombineDeltas(newdelta: Delta, olddelta: Delta) : Delta { NoDelta }
  function ApplyDelta(delta: Delta, value: Value) : Value { value }

	lemma DeltaIsAssociative(a: Delta, b: Delta, c: Delta)
	{
	}

	lemma ApplyIsAssociative(a: Delta, b: Delta, value: Value)
	{
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

