include "total_order.dfy"
	
module Lexically_Ordered_Strings refines Totally_Ordered_Type {

 	type Element = string

	predicate method lt(a: Element, b: Element)
		ensures lt(a, b) == ltdef(a, b);
	{
		if |a| == 0 && |b| == 0 then false
		else if |a| == 0       then true
		else if |b| == 0       then false
		else if a[0] < b[0]    then true
		else if a[0] > b[0]    then false
		else lt(a[1..], b[1..])
		// ltlte_is_transitive_forall();
		// if |a| == 0 && |b| == 0 {
		// 	r := false;
		// } else if |a| == 0 {
		// 	r := true;
		// } else if |b| == 0 {
		// 	r := false;
		// } else if a[0] < b[0] {
		// 	r := true;
		// } else if a[0] > b[0] {
		// 	r := false;
		// } else {
		// 	r := lt(a[1..], b[1..]);
		// }
	}

	predicate method lte(a: Element, b: Element) 
	{
		ltedef_is_transitive_forall();
		ltlte_is_transitive_forall();
		ltedef_is_anti_symmetric_forall();
		if a == b then
			true
		else
			lt(a, b)
	}

	predicate ltdef(a: Element, b: Element)
	{
		if |a| == 0 && |b| == 0 then false
		else if |a| == 0       then true
		else if |b| == 0       then false
		else if a[0] < b[0]    then true
		else if a[0] > b[0]    then false
		else ltdef(a[1..], b[1..])
	}


	predicate ltedef(a: Element, b: Element)
	{
		a == b || ltdef(a, b)
	}

	/////////////////////////////////////////
	
	lemma ltdef_is_transitive(a: string, b: string, c: string)
		requires ltdef(a, b);
		requires ltdef(b, c);
		ensures ltdef(a, c);
	{
	}

	lemma ltedef_is_transitive(a: string, b: string, c: string)
		requires ltedef(a, b);
		requires ltedef(b, c);
		ensures ltedef(a, c);
	{
		if ltdef(a,b) && ltdef(b,c) {
			ltdef_is_transitive(a, b, c);
		}
	}

	lemma ltedef_is_transitive_forall()
		ensures forall a, b, c :: ltedef(a, b) && ltedef(b, c) ==> ltedef(a, c);
	{
		forall a, b, c | ltedef(a, b) && ltedef(b, c) {
			ltedef_is_transitive(a, b, c);
		}
	}

	lemma ltlte_is_transitive(a: string, b: string, c: string)
		requires ltdef(a, b);
		requires ltedef(b, c);
		ensures ltdef(a, c);
	{
		if ltdef(a,b) && ltdef(b,c) {
			ltdef_is_transitive(a, b, c);
		}
	}

	lemma ltlte_is_transitive_forall()
		ensures forall a, b, c :: ltdef(a, b) && ltedef(b, c) ==> ltdef(a, c);
	{
		forall a, b, c | ltdef(a, b) && ltedef(b, c) {
			ltlte_is_transitive(a, b, c);
		}
	}

	lemma ltedef_is_anti_symmetric(a: string, b: string)
		requires ltedef(a, b);
		requires ltedef(b, a);
		ensures a == b;
	{
		if |a| > 0 && |b| > 0 {
			ltedef_is_anti_symmetric(a[1..], b[1..]);
		}
	}

	lemma ltedef_is_anti_symmetric_forall()
		ensures forall a, b :: ltedef(a, b) && ltedef(b, a) ==> a == b;
	{
		forall a, b | ltedef(a, b) && ltedef(b, a) {
			ltedef_is_anti_symmetric(a, b);
		}
	}




	
// predicate method lte(a: string, b: string)
	// 	ensures forall a, b, c :: lexical_lte(a, b) && lexical_lte(b, c) ==> lexical_lte(a, c);
	// 	ensures forall a, b :: lexical_lte(a, b) && lexical_lte(b, a) ==> a == b;
	// {
	// 	lexical_lte_is_transitive_forall();
	// 	lexical_lte_is_anti_symmetric_forall();
	// 	lexical_lte(a, b)
	// }

	// function method lcp<T(==)>(a: seq<T>, b: seq<T>) : seq<T>
	// 	ensures lcp<T>(a, b) <= a;
	// 	ensures lcp<T>(a, b) <= b;
	// 	ensures	|lcp<T>(a, b)| == |a| ||	|lcp<T>(a, b)| == |b| ||	a[|lcp<T>(a, b)|] != b[|lcp<T>(a, b)|];
	// 	ensures forall a, b, c :: lte(a, b) && lte(b, c) ==>
	// 		longest_common_prefix<char>(a, c) == longest_common_prefix<char>(a, b) ||
	// 		longest_common_prefix<char>(a, c) == longest_common_prefix<char>(b, c);
	// {
	// 	longest_common_prefix(a, b)
	// }
	
	// ///////////// Not revealed ///////////////////
	
	// predicate method lexical_lt(a: string, b: string)
	// 	ensures lexical_lt(a, b) ==> a != b;
	// {
	// 	if |a| == 0 && |b| == 0 then false
	// 	else if |a| == 0       then true
	// 	else if |b| == 0       then false
	// 	else if a[0] < b[0]    then true
	// 	else if a[0] > b[0]    then false
	// 	else lexical_lt(a[1..], b[1..])
	// }


	// predicate method lexical_lte(a: string, b: string)
	// {
	// 	a == b || lexical_lt(a, b)
	// }



	// function method longest_common_prefix<T(==)>(a: seq<T>, b: seq<T>) : seq<T>
	// 	ensures longest_common_prefix<T>(a, b) <= a;
	// 	ensures longest_common_prefix<T>(a, b) <= b;
	// 	ensures
	// 		|longest_common_prefix<T>(a, b)| == |a| ||
	// 		|longest_common_prefix<T>(a, b)| == |b| ||
	// 		a[|longest_common_prefix<T>(a, b)|] != b[|longest_common_prefix<T>(a, b)|];
	// {
	// 	if |a| == 0 || |b| == 0 || a[0] != b[0] then []
	// 	else [a[0]] + longest_common_prefix<T>(a[1..], b[1..])
	// }

	// lemma lexical_cmp_between_implies_common_prefix(a: string, b: string, c: string)
	// 	requires lexical_lte(a, b);
	// 	requires lexical_lte(b, c);
	// 	ensures
	// 		longest_common_prefix<char>(a, c) == longest_common_prefix<char>(a, b) ||
	// 		longest_common_prefix<char>(a, c) == longest_common_prefix<char>(b, c);
	// {
	// 	if |longest_common_prefix<char>(a, c)| > 0 {
	// 		assert a[0] == b[0] && b[0] == c[0];
	// 		lexical_cmp_between_implies_common_prefix(a[1..], b[1..], c[1..]);
	// 	}
	// }

	// lemma lexical_cmp_between_implies_common_prefix_forall()
	// 	ensures forall a, b, c :: lexical_lte(a, b) && lexical_lte(b, c) ==>
	// 	longest_common_prefix<char>(a, c) == longest_common_prefix<char>(a, b) ||
	// 	longest_common_prefix<char>(a, c) == longest_common_prefix<char>(b, c);
	// {
	// }

}
