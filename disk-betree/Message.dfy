

abstract module Message {
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

	lemma DeltaIsAssociative(a: Delta, b: Delta, c: Delta)
		ensures CombineDeltas(CombineDeltas(a, b), c) == CombineDeltas(a, CombineDeltas(b, c))

	lemma MergeIsAssociative(a: Message, b: Message, c: Message)
		ensures Merge(Merge(a, b), c) == Merge(a, Merge(b, c))
}
