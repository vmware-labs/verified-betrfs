abstract module Total_Order {

	type Element(!new,==)

	predicate method lt(a: Element, b: Element)
	{
		lte(a, b) && a != b
	}
		
	predicate method lte(a: Element, b: Element)
		ensures lte(a, b) == ltedef(a, b);
		ensures ltedef(a, b) || ltedef(b, a); // Total
		ensures ltedef(a, b) && ltedef(b, a) ==> a == b; // Antisymmetric
		ensures forall a, b, c :: ltedef(a, b) && ltedef(b, c) ==> ltedef(a, c); // Transitive

	predicate method ltedef(a: Element, b: Element)
}
