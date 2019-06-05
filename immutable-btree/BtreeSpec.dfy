include "../lib/total_order.dfy"
include "../lib/map_utils.dfy"
include "../lib/mathematics.dfy"
include "../lib/sequences.dfy"

abstract module BtreeSpec {
  import Keyspace = Bounded_Total_Order
  import opened Sequences

  type Key = Keyspace.Element

  datatype Node<Value> =
    Leaf(keys: seq<Key>, values: seq<Value>, lb: Key, ub: Key) |
    Index(pivots: seq<Key>, children: seq<Node>, lb: Key, ub: Key)

  datatype Constants = Constants()
  datatype Variables<Value> = Variables(root: Node<Value>)

  predicate Init(k: Constants, s: Variables) {
    s.root == Leaf([], [], Keyspace.Min_Element, Keyspace.Max_Element)
  }

  predicate WFTree(tree: Node) {
    if tree.Leaf? then
      && |tree.keys| > 0
      && NoDupes(tree.keys)
      && Keyspace.IsSorted(tree.keys)
      && |tree.keys| == |tree.values|
      && (forall i :: 0 <= i < |tree.keys| ==>
          && Keyspace.lte(tree.lb, tree.keys[i])
          && Keyspace.lt(tree.keys[i], tree.ub)
         )
    else
      && |tree.pivots| > 0
      && Keyspace.IsSorted(tree.pivots)
      && (forall i :: 0 <= i < |tree.pivots| ==> Keyspace.lt(tree.lb, tree.pivots[i]) && Keyspace.lt(tree.pivots[i], tree.ub))
      && |tree.children| == |tree.pivots| + 1
      && (forall i {:trigger WFTree(tree.children[i]) } :: 0 <= i < |tree.children| ==> WFTree(tree.children[i]))
      && tree.lb == tree.children[0].lb
      && tree.ub == tree.children[|tree.children| - 1].ub
      && (forall i :: 0 <= i < |tree.pivots| ==>
          && tree.pivots[i] == tree.children[i].ub
          && tree.pivots[i] == tree.children[i+1].lb
         )
  }

  predicate WFRoot(tree: Node) {
    if tree.Leaf? then
      && Keyspace.IsSorted(tree.keys)
      && |tree.keys| == |tree.values|
    else 
      WFTree(tree)
  }

  datatype Layer<Value(!new)> = Layer(node: Node<Value>, slot: int)
  type Lookup<Value(!new)> = seq<Layer<Value>>
 
  predicate ValidLookup(lookup: Lookup)
  {
    if |lookup| == 0 then true
    else
      && (forall i :: 0 <= i < |lookup| - 1 ==> WFTree(lookup[i].node))
      && (forall i :: 0 <= i < |lookup| - 1 ==> lookup[i].node.Index?)
      && (forall i :: 0 <= i < |lookup| - 1 ==> 0 <= lookup[i].slot < |lookup[i].node.children|)
      && (forall i :: 0 <= i < |lookup| - 1 ==> lookup[i+1].node == lookup[i].node.children[lookup[i].slot])
      && WFTree(Last(lookup).node)
      && Last(lookup).node.Leaf?
      && 0 <= Last(lookup).slot < |Last(lookup).node.keys|
  }

  predicate IsSatisfyingLookup<Value(!new)>(tree: Node, key: Key, value: Value, lookup: Lookup)
  {
    && ValidLookup(lookup)
    && |lookup| > 0
    && lookup[0].node == tree
    && Last(lookup).node.keys[Last(lookup).slot] == key 
    && Last(lookup).node.values[Last(lookup).slot] == value
  }

  predicate Get<Value>(k: Constants, s: Variables, s': Variables, key: Key, value: Value, lookup: Lookup)
  {
    && IsSatisfyingLookup(s.root, key, value, lookup)
    && s' == s
  }

  predicate PutTransform<Value>(tree:Node, newtree:Node, key:Key, value:Value)
    requires WFTree(tree)
    decreases tree;
  {
    && Keyspace.lte(tree.lb, key)
    && Keyspace.lt(key, tree.ub)
    && tree.lb == newtree.lb
    && tree.ub == newtree.ub
    && (if tree.Leaf? then (
      var pos := Keyspace.LargestLte(tree.keys, key);
      if pos >= 0 && key == tree.keys[pos] then (
        newtree == Leaf(tree.keys, tree.values[pos := value], tree.lb, tree.ub)
      ) else (
        var newkeys := tree.keys[..pos+1] + [key] + tree.keys[pos+1..];
        var newvals := tree.values[..pos+1] + [value] + tree.values[pos+1..];
        newtree == Leaf(newkeys, newvals, tree.lb, tree.ub)
      )
    ) else (
      && var pos := Keyspace.LargestLte(tree.pivots, key) + 1;

      && newtree.Index?
      && newtree.pivots == tree.pivots
      && |newtree.children| == |tree.children|
      && newtree.children == tree.children[pos := newtree.children[pos]]
      && PutTransform(tree.children[pos], newtree.children[pos], key, value)
    ))
  }

  predicate Put<Value>(k: Constants, s: Variables, s': Variables, key: Key, value: Value)
  {
    && WFTree(s.root)
    && PutTransform(s.root, s'.root, key, value)
  }

  datatype Step<Value(!new)> =
    | GetStep(key: Key, value: Value, lookup: Lookup)
    | PutStep(key: Key, value: Value)
    //| SplitStep()
    //| GrowStep()
    /*| ContractStep()*/

  predicate NextStep(k: Constants, s: Variables, s': Variables, step:Step) {
    match step {
      case GetStep(key, value, lookup) => Get(k, s, s', key, value, lookup)
      case PutStep(key, value) => Put(k, s, s', key, value)
      /*case SplitStep() => Split(k, s, s')
      case GrowStep() => GrowStep(k, s, s')*/
    }
  }

  predicate Next<Value(!new)>(k: Constants, s: Variables, s': Variables) {
    exists step:Step :: NextStep(k, s, s', step)
  }

} // module BtreeSpec
