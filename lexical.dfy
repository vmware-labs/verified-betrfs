include "total_order.dfy"
	
module Lexical_Order_Strings refines Total_Order {

 	type Element = string

	predicate method lte(a: Element, b: Element)
	{
        ltedef_properties(a, b);
        ltedef(a, b)
	}

	predicate method ltedef(a: Element, b: Element)
	{
		if |a| == 0 && |b| == 0 then true
		else if |a| == 0       then true
		else if |b| == 0       then false
		else if a[0] < b[0]    then true
		else if a[0] > b[0]    then false
		else ltedef(a[1..], b[1..])
	}

  lemma ltedef_properties(a: Element, b: Element)
		ensures ltedef(a, b) || ltedef(b, a); // Total
		ensures ltedef(a, b) && ltedef(b, a) ==> a == b; // Antisymmetric
  {
  }

}
