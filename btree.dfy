function method lexical_cmp(a: string, b: string) : int
	ensures a == b ==> lexical_cmp(a, b) == 0;
{
	if |a| == 0 && |b| == 0 then  0
	else if |a| == 0       then -1
	else if |b| == 0       then  1
	else if a[0] < b[0]    then -1
	else if a[0] > b[0]    then  1
	else lexical_cmp(a[1..], b[1..])
}

lemma lexical_cmp_is_transitive(a: string, b: string, c: string)
	requires lexical_cmp(a, b) <= 0;
	requires lexical_cmp(b, c) <= 0;
	ensures lexical_cmp(a, c) <= 0;
{}

lemma lexical_cmp_is_anti_symmetric(a: string, b: string)
	requires lexical_cmp(a, b) <= 0;
	requires lexical_cmp(b, a) <= 0;
	ensures a == b;
{}

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
	requires lexical_cmp(a, b) <= 0;
	requires lexical_cmp(b, c) <= 0;
	ensures
		longest_common_prefix<char>(a, c) == longest_common_prefix<char>(a, b) ||
		longest_common_prefix<char>(a, c) == longest_common_prefix<char>(b, c);
{
	if |longest_common_prefix<char>(a, c)| > 0 {
		assert a[0] == b[0] && b[0] == c[0];
		lexical_cmp_between_implies_common_prefix(a[1..], b[1..], c[1..]);
	}
}



// datatype Node<Key, Value> =
// 	Leaf(keys: array<Key>, values: array<Value>) |
// 	Index(pivots: array<int>, children: array<Node>)

// datatype BtreeConfig<!Key, Value> = BtreeConfig(
// 	min_leaf_size: int, max_leaf_size: int,
//   min_fanout: int, max_fanout: int,
// 	comparator: (Key, Key) -> int)

// predicate is_total_order<Key>(cmp: (int, int) -> int) {
//  	forall a: int :: forall b: int :: cmp(a,b) < 0 <==> cmp(b, a) > 0
// }
	
// // predicate valid_btree_config<Key, Value>(cfg: BtreeConfig<Key, Value>) {
// // 	1 <= cfg.min_leaf_size &&
// // 		  cfg.min_leaf_size < cfg.max_leaf_size &&
// // 	2 <= cfg.min_fanout &&
// // 	    cfg.min_fanout < cfg.max_fanout &&
// // 	forall a: Key :: forall b: Key :: cfg.comparator(a,b) < 0 <==> cfg.comparator(b, a) > 0 &&
// // 	forall a: Key :: forall b: Key :: cfg.comparator(a,b) == 0 <==> cfg.comparator(b, a) == 0 &&
// // 	forall a: Key :: forall b: Key :: forall c: Key :: cfg.comparator(a, b) < 0 && cfg.comparator(b, c) < 0 ==> cfg.comparator(a, c) < 0
// // }

// function method int_compare(a: int, b: int) : int {
// 	a - b
// }

// method dummy(x: int) returns (nada: int) {
// 	var cfg: BtreeConfig<int, int> := BtreeConfig(12, 24, 80, 160, int_compare);
// 	nada := 0;
// }
