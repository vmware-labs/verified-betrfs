
// Delta forms a monoid with a monoid-action on the values
// (https://en.wikipedia.org/wiki/Monoid_action)

module Message {
	type Value
	type Delta

	function NopDelta() : Delta
	function DefaultValue() : Value 

	datatype Message = | Define(value: Value)
				       | Update(delta: Delta)

	function CombineDeltas(newdelta: Delta, olddelta: Delta) : Delta
	function ApplyDelta(delta: Delta, value: Value) : Value

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

	lemma DeltaIsAssociative(a: Delta, b: Delta, c: Delta)
		ensures CombineDeltas(CombineDeltas(a, b), c) == CombineDeltas(a, CombineDeltas(b, c))

	lemma ApplyIsAssociative(a: Delta, b: Delta, value: Value)
		ensures ApplyDelta(CombineDeltas(a, b), value) == ApplyDelta(a, ApplyDelta(b, value))

	lemma MergeIsAssociative(a: Message, b: Message, c: Message)
		ensures Merge(Merge(a, b), c) == Merge(a, Merge(b, c))
		{
			match (a, b, c) {
				case (Define(a), _, _) => { }
				case (Update(a), Define(b), _) => { }
				case (Update(a), Update(b), Define(c)) => {
					ApplyIsAssociative(a, b, c);
				}
				case (Update(a), Update(b), Update(c)) => {
					DeltaIsAssociative(a, b, c);
				}
			}
		}
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

