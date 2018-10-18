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

///////////////////////////////////////////

function method seq_map<U,T>(f: T-> U, inputs: seq<T>) : seq<U>
	decreases inputs;
{
	if |inputs| == 0 then []
	else [f(inputs[0])] + seq_map(f, inputs[1..])
}

function method seq_fold_left<U,T>(f: (U, T) -> U, acc: U, inputs: seq<T>) : U
{
	if |inputs| == 0 then acc
	else seq_fold_left(f, f(acc, inputs[0]), inputs[1..])
}

datatype Node =
	Leaf(keys: seq<string>, values: seq<int>) |
	Index(pivots: seq<string>, children: seq<Node>)

// function num_nodes(node: Node) : int
// {
// 	match node {
// 		case Leaf(keys, values) => 1
// 		case Index(pivots, children) =>
			
// 	}
// }

function method set_of_keys_of_children(nodes: seq<Node>, ghost height: int, ghost max_fanout: int) : set<string>
	decreases height * max_fanout;
{
	if |nodes| == 0 then {}
	else set_of_keys(nodes[0], m-1) + set_of_keys_of_children(nodes[1..], m)
}

function method set_of_keys(node: Node, ghost m: int) : set<string>
	requires m == num_nodes(node);
	//requires subtree_is_well_formed(node);
	//decreases node;
	decreases m;
{	
	match node {
		case Leaf(keys, values) =>
			set k | k in multiset(keys)
		case Index(pivots, children) =>
			children_have_lower_max_height(node);
			//seq_fold_left((a, b) => a + b, {}, seq_map(x => set_of_keys(x), children))
			set_of_keys_of_children(children, m-1)
	}
}

// predicate subtree_is_well_formed(node: Node) {
// 	match node {
// 		case Leaf(keys, values) =>
// 			|keys| > 0 &&
// 			|keys| == |values|
// 		case Index(pivots, children) =>
// 			|pivots| > 0 &&
// 			|pivots| == |children| - 1 &&
// 			forall i :: 0 <= i < |children| ==> subtree_is_well_formed(children[i])
// 	}
// }

// predicate seq_is_strictly_increasing(ss: seq<string>) {
// 	forall i :: 0 <= i < |ss|-1 ==> lexical_cmp(ss[i], ss[i+1]) < 0
// }		

// predicate subtree_is_sorted(node: Node)
// 	requires subtree_is_well_formed(node);
// {
// 	match node {
// 		case Leaf(keys, values) =>
// 			seq_is_strictly_increasing(keys)
// 		case Index(pivots, children) =>
// 			seq_is_strictly_increasing(pivots) &&
// 			(forall i :: 0 <= i < |children|-1 ==>
// 			  (forall x :: x in set_of_keys(children[i]) ==>
// 			    lexical_cmp(x, pivots[i]) < 0)) &&
// 			(forall i :: 1 <= i < |children| ==>
// 			  (forall x :: x in set_of_keys(children[i]) ==>
// 			    lexical_cmp(pivots[i-1], x) <= 0)) &&
// 			forall i :: 0 <= i < |children| ==> subtree_is_sorted(children[i])
// 	}
// }

// function map_of_kvpairs(acc: map<string, int>, keys: seq<string>, values: seq<int>) : map<string, int>
// 	requires |keys| == |values|;
// {
// 	if |keys| == 0 then acc
// 	else map_of_kvpairs(acc, keys[1..], values[1..])[keys[0] := values[0]]
// }

// function map_of_children(acc: map<string, int>, nodes: seq<Node>) : map<string, int>
// 	requires forall i :: 0 <= i < |nodes| ==> subtree_is_well_formed(nodes[i]);
// 	requires forall i :: 0 <= i < |nodes| ==> subtree_is_sorted(nodes[i]);
// {
// 	if |nodes| == 0 then acc
// 	else map_of_children(map_of_subtree(acc, nodes[0]), nodes[1..])
// }

// function map_of_subtree(acc: map<string, int>, node: Node) : map<string, int>
// 	requires subtree_is_well_formed(node);
// 	requires subtree_is_sorted(node);
// {
// 	match node {
// 		case Leaf(keys, values) =>
// 			map_of_kvpairs(acc, keys, values)
// 		case Index(pivots, children) =>
// 			max_height_is_nonnegative(node);
// 			assert forall i :: 0 <= i < |children| ==> max_height(children[i]) < max_height(node);
// 			map_of_children(acc, children)
// 	}
// }

// function subtree_map_contents(node: Node) : map<string, int>
// 	requires subtree_is_well_formed(node);
// 	requires subtree_is_sorted(node);
// {
// 	map_of_subtree(map[], node)
// }

// function method min(a: int, b: int) : int
// {
// 	if a < b
// 		then a
// 	else
// 		b
// }

function method max(a: int, b: int) : int
{
	if a < b
		then b
	else
		a
}

// function min_height_of_children(nodes: seq<Node>) : int
// 	requires forall i :: 0 <= i < |nodes| ==> subtree_is_well_formed(nodes[i]);
// 	requires |nodes| > 0;
// {
// 	if |nodes| == 1 then min_height(nodes[0])
// 	else min(min_height(nodes[0]), min_height_of_children(nodes[1..]))
// }

// function min_height(node: Node) : int
// 	requires subtree_is_well_formed(node);
// {
// 	match node {
// 		case Leaf(keys, values) => 0
// 		case Index(pivots, children) => 1 + min_height_of_children(children)
// 	}
// }

function max_height_of_children(nodes: seq<Node>) : int
	//requires forall i :: 0 <= i < |nodes| ==> subtree_is_well_formed(nodes[i]);
	//requires |nodes| > 0;
	ensures max_height_of_children(nodes) >= 0;
	ensures forall i :: 0 <= i < |nodes| ==> max_height(nodes[i]) <= max_height_of_children(nodes);
{
	if |nodes| == 0 then 0
	else if |nodes| == 1 then max_height(nodes[0])
	else max(max_height(nodes[0]), max_height_of_children(nodes[1..]))
}

function max_height(node: Node) : int
	//requires subtree_is_well_formed(node);
	ensures max_height(node) >= 0;
{
	match node {
		case Leaf(keys, values) => 0
		case Index(pivots, children) => 1 + max_height_of_children(children)
	}
}

lemma max_height_is_nonnegative(node: Node)
	//requires subtree_is_well_formed(node);
	ensures max_height(node) >= 0;
{
}

lemma children_have_lower_max_height(node: Node)
	requires node.Index?;
	ensures forall i :: 0 <= i < |node.children| ==> max_height(node.children[i]) == max_height(node) - 1;
{
	assume false;
	if |node.children| > 0 {
		assert max_height(node.children[0]) == max_height(node) - 1;
	}
}

// predicate subtree_is_balanced(node: Node)
// 	requires subtree_is_well_formed(node);
// {
// 	min_height(node) == max_height(node)
// }

// datatype Config = Config(
// 	min_leaf_size: int, max_leaf_size: int,
//   min_fanout: int, max_fanout: int)

// predicate well_formed_config(cfg: Config) {
// 	1 <= cfg.min_leaf_size < cfg.max_leaf_size &&
// 	2 <= cfg.min_fanout < cfg.max_fanout
// }

// predicate subtree_satisfies_config(node: Node, cfg: Config) {
// 	match node {
// 		case Leaf(keys, pivots) =>
// 			cfg.min_leaf_size <= |keys| <= cfg.max_leaf_size
// 		case Index(pivots, children) =>
// 			cfg.min_fanout <= |children| < cfg.max_fanout &&
// 			forall i :: 0 <= i < |children| ==> subtree_satisfies_config(children[i], cfg)
// 	}
// }

// predicate is_valid_b_subtree(node: Node, cfg: Config) {
// 	subtree_is_well_formed(node) &&
// 		subtree_is_sorted(node) &&
// 		subtree_is_balanced(node) &&
// 		subtree_satisfies_config(node, cfg)
// }

// datatype QueryResult = KeyDoesNotExist | Value(v: int)

// function method search_seq(keys: seq<string>, values: seq<int>, key: string) : QueryResult
// 	requires seq_is_strictly_increasing(keys);
// 	requires |keys| == |values|;
// 	ensures key !in map_of_kvpairs(map[], keys, values) ==>
// 		search_seq(keys, values, key) == KeyDoesNotExist;
// 	ensures key in map_of_kvpairs(map[], keys, values) ==>
// 		search_seq(keys, values, key) == Value(map_of_kvpairs(map[], keys, values)[key]);
// {
// 	if |keys| == 0 then KeyDoesNotExist
// 	else if keys[0] == key then Value(values[0])
// 	else search_seq(keys[1..], values[1..], key)
// }
	
// // function method query(node: Node, key: string) : QueryResult
// // 	requires subtree_is_well_formed(node);
// // 	requires subtree_is_sorted(node);
// // 	ensures key !in subtree_map_contents(node) <==> query(node, key) == KeyDoesNotExist;
// // 	ensures key in subtree_map_contents(node) <==> query(node, key) == Value(subtree_map_contents(node)[key]);
// // {
// // 	match node {
// // 		case Leaf(keys, values) =>
			
// // 		case Index(pivots, children) =>
// // 	}
// // }
