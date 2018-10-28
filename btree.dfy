include "lexical.dfy"
	
import Lex = Lexically

	//////////////////////////////////////////////

function method min(a: int, b: int) : int
{
	if a < b
		then a
	else
		b
}

function method max(a: int, b: int) : int
{
	if a < b
		then b
	else
		a
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

function method seq_min(s: seq<int>) : int
	requires |s| > 0;
{
	seq_fold_left((a, b) => min(a, b), s[0], s[1..])
}

function method seq_max(s: seq<int>) : int
	requires |s| > 0;
{
	seq_fold_left((a, b) => max(a, b), s[0], s[1..])
}

function method seq_sum(s: seq<int>) : int
	requires |s| > 0;
{
	seq_fold_left((a, b) => a + b, 0, s)
}

function method seq_union<T>(s: seq<set<T> >) : set<T>
	requires |s| > 0;
{
	seq_fold_left((a, b) => a + b, {}, s)
}

////////////////////////////////////////////

datatype Node<Value> =
	Leaf(keys: seq<string>, values: seq<Value>) |
	Index(pivots: seq<string>, children: seq<Node>)

predicate subtree_is_well_formed(node: Node) {
	match node {
		case Leaf(keys, values) =>
			|keys| > 0 &&
			|keys| == |values|
		case Index(pivots, children) =>
			|pivots| > 0 &&
			|pivots| == |children| - 1 &&
			forall child :: child in children ==> subtree_is_well_formed(child)
	}
}

function min_height_of_children(nodes: seq<Node>) : int
	requires forall i :: 0 <= i < |nodes| ==> subtree_is_well_formed(nodes[i]);
	requires |nodes| > 0;
{
	if |nodes| == 1 then min_height(nodes[0])
	else min(min_height(nodes[0]), min_height_of_children(nodes[1..]))
}

function min_height(node: Node) : int
	requires subtree_is_well_formed(node);
{
	match node {
		case Leaf(keys, values) => 0
		case Index(pivots, children) =>
			1 + min_height_of_children(children)
	}
}

function max_height_of_children(nodes: seq<Node>) : int
	requires forall i :: 0 <= i < |nodes| ==> subtree_is_well_formed(nodes[i]);
	requires |nodes| > 0;
{
	if |nodes| == 0 then 0
	else if |nodes| == 1 then max_height(nodes[0])
	else max(max_height(nodes[0]), max_height_of_children(nodes[1..]))
}

function max_height(node: Node) : int
	requires subtree_is_well_formed(node);
	ensures max_height(node) >= 0;
{
	match node {
		case Leaf(keys, values) => 0
		case Index(pivots, children) =>
			1 + max_height_of_children(children)
	}
}

predicate subtree_is_balanced(node: Node)
	requires subtree_is_well_formed(node);
{
	min_height(node) == max_height(node) &&
		(node.Index? ==> (forall child :: child in node.children ==> subtree_is_balanced(child))) &&
		(node.Index? ==> (forall child :: child in node.children ==> max_height(child) == max_height(node.children[0])))
}

function method height(node: Node) : int
	requires subtree_is_well_formed(node);
	requires subtree_is_balanced(node);
	ensures min_height(node) <= height(node) <= max_height(node);
{
	match node {
		case Leaf(keys, values) => 0
		case Index(pivots, children) =>
			1 + height(children[0])
	}
}

lemma children_have_one_less_height(node: Node)
	requires subtree_is_well_formed(node);
	requires subtree_is_balanced(node);
	ensures node.Index? ==> forall child :: child in node.children ==> height(child) == height(node) - 1;
{
	if node.Index? {
		assert forall child :: child in node.children ==> height(child) == height(node) - 1;
		// Why da fuq does repeating this line cause the proof to check out?!?
		assert forall child :: child in node.children ==> height(child) == height(node) - 1;
	}
}

predicate is_child_list(pivots: seq<string>, nodes: seq<Node>)
{
	|nodes| > 0 &&
		|pivots| == |nodes| - 1 &&
		(forall node :: node in nodes ==> subtree_is_well_formed(node)) &&
		(forall node :: node in nodes ==> subtree_is_balanced(node)) &&
		(forall node :: node in nodes ==> height(node) == height(nodes[0])) &&
		(
		forall i :: 0 <= i < |nodes| - 1 ==> forall k :: k in set_of_keys(nodes[i]) ==> Lex.lt(k, pivots[i])) &&
		(forall i :: 1 <= i < |nodes| ==> forall k :: k in set_of_keys(nodes[i]) ==> Lex.lte(pivots[i-1], k))
}

function set_of_keys_of_children(pivots: seq<string>, nodes: seq<Node>) : set<string>
	requires is_child_list(pivots, nodes);
{
	if |nodes| == 1 then set_of_keys(nodes[0])
	else set_of_keys(nodes[0]) + set_of_keys_of_children(pivots[1..], nodes[1..])
}

function set_of_keys(node: Node) : set<string>
	requires subtree_is_well_formed(node);
	requires subtree_is_balanced(node);
{	
	match node {
		case Leaf(keys, values) =>
			set k | k in multiset(keys)
		case Index(pivots, children) =>
			children_have_one_less_height(node);
			set_of_keys_of_children(pivots, children)
	}
}

predicate seq_is_strictly_increasing(ss: seq<string>) {
	forall i :: forall j :: 0 <= i < j < |ss| ==> Lex.lt(ss[i], ss[j])
}		

lemma seq_sorting_transitivity(ss: seq<string>, key: string)
	requires seq_is_strictly_increasing(ss);
	requires |ss| > 0;
	requires Lex.lt(key, ss[0]);
	ensures forall i :: 0 <= i < |ss| ==> Lex.lt(key, ss[i]);
{
}

predicate subtree_is_sorted(node: Node)
	requires subtree_is_well_formed(node);
	requires subtree_is_balanced(node);
{
	match node {
		case Leaf(keys, values) =>
			seq_is_strictly_increasing(keys)
		case Index(pivots, children) =>
			seq_is_strictly_increasing(pivots) &&
			(forall i :: 0 <= i < |children|-1 ==>
			  (forall x :: x in set_of_keys(children[i]) ==>
			    Lex.lt(x, pivots[i]))) &&
			(forall i :: 1 <= i < |children| ==>
			  (forall x :: x in set_of_keys(children[i]) ==>
			    Lex.lte(pivots[i-1], x))) &&
			forall i :: 0 <= i < |children| ==> subtree_is_sorted(children[i])
	}
}

predicate subtree_is_b_tree(node: Node) {
	subtree_is_well_formed(node) &&
		subtree_is_balanced(node) &&
		subtree_is_sorted(node)
}

function merge_disjoint_maps<U,T>(mapa: map<U,T>, mapb: map<U,T>) : map<U,T>
	requires mapa.Keys !! mapb.Keys;
	ensures merge_disjoint_maps(mapa, mapb).Keys == mapa.Keys + mapb.Keys;
	ensures forall k :: k in merge_disjoint_maps(mapa, mapb).Keys && k in mapa.Keys ==>
		merge_disjoint_maps(mapa, mapb)[k] == mapa[k];
	ensures forall k :: k in merge_disjoint_maps(mapa, mapb).Keys && k in mapb.Keys ==>
		merge_disjoint_maps(mapa, mapb)[k] == mapb[k];
{
	map x : U | (x in mapa.Keys + mapb.Keys) :: if x in mapa then mapa[x] else mapb[x]
}

function map_of_kvpairs<Value>(keys: seq<string>, values: seq<Value>) : map<string, Value>
	requires |keys| == |values|;
	requires seq_is_strictly_increasing(keys);
	ensures forall k :: k in map_of_kvpairs(keys, values) <==> k in keys;
	ensures forall k :: k in map_of_kvpairs(keys, values) ==>
		(exists i :: 0 <= i < |keys| && k == keys[i] && map_of_kvpairs(keys, values)[k] == values[i]);
{
	if |keys| == 0 then map[]
	else map_of_kvpairs(keys[1..], values[1..])[keys[0] := values[0]]
}

function map_of_children<Value>(pivots: seq<string>, nodes: seq<Node<Value> >) : map<string, Value>
	requires is_child_list(pivots, nodes);
	requires forall node :: node in nodes ==> subtree_is_b_tree(node);
	ensures map_of_children(pivots, nodes).Keys == set_of_keys_of_children(pivots, nodes);
	decreases height(nodes[0]), |nodes|, 1;
{
	if |nodes| == 1 then map_of_subtree(nodes[0])
	else
		var map1 := map_of_subtree(nodes[0]);
		assert forall k :: k in set_of_keys(nodes[0]) ==> Lex.lt(k, pivots[0]);
		assert map1.Keys == set_of_keys(nodes[0]);
		assert forall k :: k in map1.Keys ==> Lex.lt(k, pivots[0]);
		var map2 := map_of_children(pivots[1..], nodes[1..]);
		assert map2.Keys == set_of_keys_of_children(pivots[1..], nodes[1..]);
		assert forall k :: k in map2.Keys ==> Lex.lte(pivots[0], k);
		merge_disjoint_maps(map1, map2)
}

function map_of_subtree<Value>(node: Node<Value>) : map<string, Value>
	requires subtree_is_b_tree(node);
	ensures map_of_subtree(node).Keys == set_of_keys(node);
	decreases height(node), 0;
{
	match node {
		case Leaf(keys, values) =>
			map_of_kvpairs(keys, values)
		case Index(pivots, children) =>
			children_have_one_less_height(node);
			map_of_children(pivots, children)
	}
}

// lemma subtree_map_delegation(node: Node, key: string, index: int)
// 	requires subtree_is_b_tree(node);
// 	requires node.Index?;
// 	requires 0 <= index <= |node.pivots|;
// 	requires forall i :: 0 <= i < index ==> lexical_cmp(node.pivots[i], key) <= 0;
// 	requires forall i :: index <= i < |node.pivots| ==> lexical_cmp(key, node.pivots[i]) < 0;
// 	ensures true;
// 	// ensures key in subtree_map_contents(node) <==> key in subtree_map_contents(node.children[index]);
// 	// ensures key in subtree_map_contents(node) ==>
// 	// 	subtree_map_contents(node)[key] == subtree_map_contents(node.children[index])[key];
// {
// 	assert forall k :: k in subtree_map_contents(node) ==> k in set_of_keys(node);
// }

datatype Config = Config(
	min_leaf_size: int, max_leaf_size: int,
  min_fanout: int, max_fanout: int)

predicate well_formed_config(cfg: Config) {
	1 <= cfg.min_leaf_size < cfg.max_leaf_size &&
	2 <= cfg.min_fanout < cfg.max_fanout
}

predicate subtree_satisfies_config(node: Node, cfg: Config)
	requires subtree_is_b_tree(node);
{
	match node {
		case Leaf(keys, pivots) =>
			cfg.min_leaf_size <= |keys| <= cfg.max_leaf_size
		case Index(pivots, children) =>
			cfg.min_fanout <= |children| < cfg.max_fanout &&
			forall i :: 0 <= i < |children| ==> subtree_satisfies_config(children[i], cfg)
	}
}

datatype QueryResult<Value> = KeyDoesNotExist | ValueForKey(v: Value)

	// TODO: binary search
function method search_seq<Value>(keys: seq<string>, values: seq<Value>, key: string) : QueryResult<Value>
	requires seq_is_strictly_increasing(keys);
	requires |keys| == |values|;
	ensures key !in map_of_kvpairs(keys, values) ==>
		search_seq(keys, values, key) == KeyDoesNotExist;
	ensures key in map_of_kvpairs(keys, values) ==>
		search_seq(keys, values, key) == ValueForKey(map_of_kvpairs(keys, values)[key]);
{
	if |keys| == 0 then KeyDoesNotExist
	else if keys[0] == key then ValueForKey(values[0])
	else search_seq(keys[1..], values[1..], key)
}

	// TODO: binary search
method search_seq_for_least_greater(keys: seq<string>, key: string) returns (r: int)
	requires seq_is_strictly_increasing(keys);
	ensures 0 <= r <= |keys|;
	ensures forall i :: 0 <= i < r ==> Lex.lte(keys[i], key);
	ensures forall i :: r <= i < |keys| ==> Lex.lt(key, keys[i]);
{
	if |keys| == 0 {
		r := 0;
	} else if Lex.lt(key, keys[0]) {
		r := 0;
	} else {
		var t := search_seq_for_least_greater(keys[1..], key);
		r := 1 + t;
	}
}

// method query(node: Node, key: string) returns (qr: QueryResult)
// 	requires subtree_is_b_tree(node);
// 	ensures key !in subtree_map_contents(node) <==> qr == KeyDoesNotExist;
// 	ensures key in subtree_map_contents(node) <==> qr == Value(subtree_map_contents(node)[key]);
// {
// 	match node {
// 		case Leaf(keys, values) =>
// 			qr := search_seq(keys, values, key);
// 		case Index(pivots, children) =>
// 			var i := search_seq_for_least_greater(pivots, key);
// 			qr := query(children[i], key);
// 	}
// }
