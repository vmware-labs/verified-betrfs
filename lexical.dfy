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

    function method longest_common_prefix<T(==)>(a: seq<T>, b: seq<T>) : seq<T>
        ensures longest_common_prefix<T>(a, b) <= a;
        ensures longest_common_prefix<T>(a, b) <= b;
        ensures
            |longest_common_prefix<T>(a, b)| == |a| ||
            |longest_common_prefix<T>(a, b)| == |b| ||
            a[|longest_common_prefix<T>(a, b)|] != b[|longest_common_prefix<T>(a, b)|];
    {
        if |a| == 0 || |b| == 0 || a[0] != b[0] then []
        else [a[0]] + longest_common_prefix<T>(a[1..], b[1..])
    }

    lemma lexical_cmp_between_implies_common_prefix(a: string, b: string, c: string)
        requires lte(a, b);
        requires lte(b, c);
        ensures
            longest_common_prefix<char>(a, c) == longest_common_prefix<char>(a, b) ||
            longest_common_prefix<char>(a, c) == longest_common_prefix<char>(b, c);
    {
        if |longest_common_prefix<char>(a, c)| > 0 {
            assert a[0] == b[0] && b[0] == c[0];
            lexical_cmp_between_implies_common_prefix(a[1..], b[1..], c[1..]);
        }
    }

    lemma lexical_cmp_between_implies_common_prefix_forall()
        ensures forall a, b, c :: lte(a, b) && lte(b, c) ==>
        longest_common_prefix<char>(a, c) == longest_common_prefix<char>(a, b) ||
        longest_common_prefix<char>(a, c) == longest_common_prefix<char>(b, c);
    {
    }

  
}

// Local Variables:
// tab-width: 4
// End:
