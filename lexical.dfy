include "total_order.dfy"
	
module Lexical_Order_Strings refines Total_Order {

 	type Element = string

	predicate method lte(a: Element, b: Element)
	{
		if |a| == 0 && |b| == 0 then true
		else if |a| == 0       then true
		else if |b| == 0       then false
		else if a[0] < b[0]    then true
		else if a[0] > b[0]    then false
		else lte(a[1..], b[1..])
	}

	predicate ltedef(a: Element, b: Element)
	{
		if |a| == 0 && |b| == 0 then true
		else if |a| == 0       then true
		else if |b| == 0       then false
		else if a[0] < b[0]    then true
		else if a[0] > b[0]    then false
		else ltedef(a[1..], b[1..])
	}
}
