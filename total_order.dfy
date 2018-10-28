abstract module Totally_Ordered_Type {

	type Element(!new,==)

	predicate method lt(a: Element, b: Element)
		ensures lt(a, b) == ltdef(a, b);
		ensures ltdef(a, b) || ltdef(b, a) || a == b; 
		ensures ltdef(a, b) ==> a != b && !ltdef(b, a); 
		ensures forall a, b, c :: ltdef(a, b) && ltdef(b, c) ==> ltdef(a, c);
		// ensures forall a, b, c :: ltdef(a, b) && ltedef(b, c) ==> ltdef(a, c);
		// ensures forall a, b, c :: ltedef(a, b) && ltdef(b, c) ==> ltdef(a, c);

	// predicate method lte(a: Element, b: Element)
	// 	ensures lte(a, b) == ltedef(a, b);
	// 	ensures forall a, b :: ltedef(a, b) && ltedef(b, a) ==> a == b;
	// 	ensures forall a, b, c :: ltedef(a, b) && ltedef(b, c) ==> ltedef(a, c);
		// ensures forall a, b, c :: ltdef(a, b) && ltedef(b, c) ==> ltdef(a, c);
		// ensures forall a, b, c :: ltedef(a, b) && ltdef(b, c) ==> ltdef(a, c);
		
	predicate ltdef(a: Element, b: Element)
	//predicate ltedef(a: Element, b: Element)
}
