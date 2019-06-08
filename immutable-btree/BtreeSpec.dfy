include "../lib/total_order.dfy"
include "../lib/map_utils.dfy"
include "../lib/mathematics.dfy"
include "../lib/sequences.dfy"
include "CrashableMap.dfy"

abstract module BtreeSpec {
  import CMap : CrashableMap
  import Keyspace = CrashableMap.Keyspace
  import opened Sequences

  type Key = CrashableMap.Key

  datatype Node<Value> =
    Leaf(keys: seq<Key>, values: seq<Value>, ghost lb: Key, ghost ub: Key) |
    Index(pivots: seq<Key>, children: seq<Node>, ghost lb: Key, ghost ub: Key)

  datatype Constants = Constants()
  datatype Variables<Value> = Variables(root: Node<Value>)

  predicate Init(k: Constants, s: Variables) {
    s.root == Leaf([], [], Keyspace.Min_Element, Keyspace.Max_Element)
  }

  predicate WFTree(tree: Node) {
    if tree.Leaf? then
      && |tree.keys| > 0
      && Keyspace.IsStrictlySorted(tree.keys)
      && |tree.keys| == |tree.values|
      && (forall i :: 0 <= i < |tree.keys| ==>
          && Keyspace.lte(tree.lb, tree.keys[i])
          && Keyspace.lt(tree.keys[i], tree.ub)
         )
    else
      && |tree.pivots| > 0
      && Keyspace.IsStrictlySorted(tree.pivots)
      && (forall i :: 0 <= i < |tree.pivots| ==> Keyspace.lt(tree.lb, tree.pivots[i]) && Keyspace.lt(tree.pivots[i], tree.ub))
      && |tree.children| == |tree.pivots| + 1
      && (forall i {:trigger WFTree(tree.children[i]) } :: 0 <= i < |tree.children| ==> WFTree(tree.children[i]))
      && tree.lb == tree.children[0].lb
      && tree.ub == tree.children[|tree.children| - 1].ub
      && (forall i :: 0 <= i < |tree.pivots| ==>
          tree.pivots[i] == tree.children[i].ub)
      && (forall i :: 0 <= i < |tree.pivots| ==>
          tree.pivots[i] == tree.children[i+1].lb)
  }

  predicate WFRoot(tree: Node) {
    && tree.lb == Keyspace.Min_Element
    && tree.ub == Keyspace.Max_Element
    && (
      if (tree.Leaf? && tree.keys == []) then
        tree.values == []
      else
        WFTree(tree)
    )
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
    && Keyspace.lte(tree.lb, key) // TODO enabling condition?
    && Keyspace.lt(key, tree.ub)
    && tree.lb == newtree.lb
    && tree.ub == newtree.ub
    && (if tree.Leaf? then (
      var pos := Keyspace.LargestLte(tree.keys, key);
      if pos >= 0 && key == tree.keys[pos] then (
        newtree == Leaf(tree.keys, tree.values[pos := value], tree.lb, tree.ub)
      ) else (
        var newkeys := insert(tree.keys, key, pos+1);
        var newvals := insert(tree.values, value, pos+1);
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
    if (s.root.Leaf? && |s.root.keys| == 0) then (
      && Keyspace.lte(s.root.lb, key)
      && Keyspace.lt(key, s.root.ub)
      && s' == Variables(Leaf([key], [value], s.root.lb, s.root.ub))
    ) else (
      && WFTree(s.root)
      && PutTransform(s.root, s'.root, key, value)
    )
  }

  predicate GrowLeaf(tree:Node, newtree:Node, childrenToLeft:int)
  requires WFRoot(tree)
  requires tree.Leaf?
  {
    && 1 < childrenToLeft < |tree.keys| - 1
    && newtree == Index(
        [tree.keys[childrenToLeft]],
        [
          Leaf(
            tree.keys[ .. childrenToLeft],
            tree.values[ .. childrenToLeft],
            tree.lb,
            tree.keys[childrenToLeft] // ub
          ),
          Leaf(
            tree.keys[childrenToLeft .. ],
            tree.values[childrenToLeft .. ],
            tree.keys[childrenToLeft], // lb
            tree.ub
          )
        ],
        tree.lb,
        tree.ub
      )
  }

  predicate GrowIndex(tree:Node, newtree:Node, childrenToLeft:int)
  requires WFTree(tree)
  requires tree.Index?
  {
    && 1 < childrenToLeft < |tree.children| - 1
    && newtree == Index(
        [tree.pivots[childrenToLeft - 1]],
        [
          Index(
            tree.pivots[ .. childrenToLeft - 1],
            tree.children[ .. childrenToLeft],
            tree.lb,
            tree.pivots[childrenToLeft - 1] // ub
          ),
          Index(
            tree.pivots[childrenToLeft .. ],
            tree.children[childrenToLeft .. ],
            tree.pivots[childrenToLeft - 1], // lb
            tree.ub
          )
        ],
        tree.lb,
        tree.ub
      )
  }

  predicate Grow<Value>(k: Constants, s: Variables, s': Variables, childrenToLeft: int)
  {
    && WFRoot(s.root)
    && (
      if s.root.Leaf? then
        GrowLeaf(s.root, s'.root, childrenToLeft)
      else
        GrowIndex(s.root, s'.root, childrenToLeft)
    )
  }

  predicate IsSplit(node: Node, left_node: Node, pivot: Key, right_node: Node, childrenToLeft: int)
  {
    && node.lb == left_node.lb
    && left_node.ub == pivot
    && pivot == right_node.ub
    && right_node.ub == node.ub
    && (if node.Leaf? then (
      && left_node.Leaf?
      && right_node.Leaf?
      && |left_node.keys| == childrenToLeft
      && |left_node.values| == childrenToLeft
      && |left_node.keys| > 0
      && |right_node.keys| > 0
      && node.keys == left_node.keys + right_node.keys
      && node.values == left_node.values + right_node.values
      && pivot == right_node.keys[0]
    ) else (
      && left_node.Index?
      && right_node.Index?
      && |left_node.children| == childrenToLeft
      && |left_node.pivots| == childrenToLeft - 1
      && |left_node.children| >= 2
      && |right_node.children| >= 2
      && node.children == left_node.children + right_node.children
      && node.pivots == left_node.pivots + [pivot] + right_node.pivots
    ))
  }

  // Suppose one of tree's children `child` satisfies
  // has (lb, ub) equal to (l, u). Then we are going to split
  // `child` and augment the pivot-list of `tree` by 1,
  // and splice out `child` and add the two new nodes.
  predicate SplitTransform(tree: Node, newtree: Node, l: Key, u: Key,
      childrenToLeft: int)
  requires WFTree(tree)
  decreases tree
  {
    && tree.Index?
    && newtree.Index?
    && newtree.lb == tree.lb
    && newtree.ub == tree.ub
    && var child_pos := Keyspace.LargestLte(tree.pivots, l) + 1;
    && var child := tree.children[child_pos];
    && (if child.lb == l && child.ub == u then (
      // location of the newly inserted pivot is child_pos
      // child at child_pos gets replaced by two nodes
      && |newtree.children| == |tree.children| + 1
      && |newtree.pivots| == |tree.pivots| + 1
      && IsSplit(child, newtree.children[child_pos], newtree.pivots[child_pos], newtree.children[child_pos + 1], childrenToLeft)
      && newtree.pivots == insert(tree.pivots, newtree.pivots[child_pos], child_pos)
      && newtree.children == replace1with2(
          tree.children,
          newtree.children[child_pos],
          newtree.children[child_pos + 1],
          child_pos)
    ) else (
      && newtree.pivots == tree.pivots
      && |newtree.children| == |tree.children|
      && newtree.children == tree.children[child_pos := newtree.children[child_pos]]
      && SplitTransform(tree.children[child_pos], newtree.children[child_pos], l, u, childrenToLeft)
    ))
  }

  // Split the (non-root) node bound by l...u into two nodes
  // with `childrenToLeft` of its children going on the left.
  predicate Split(k: Constants, s: Variables, s': Variables,
      l: Key, u: Key, childrenToLeft: int)
  {
    && s.root.Index?
    && WFTree(s.root)
    && SplitTransform(s.root, s'.root, l, u, childrenToLeft)
  }

  datatype Step<Value(!new)> =
    | GetStep(key: Key, value: Value, lookup: Lookup)
    | PutStep(key: Key, value: Value)
    //| SplitStep()
    | GrowStep(childrenToLeft: int)
    /*| ContractStep()*/

  predicate NextStep(k: Constants, s: Variables, s': Variables, step:Step) {
    match step {
      case GetStep(key, value, lookup) => Get(k, s, s', key, value, lookup)
      case PutStep(key, value) => Put(k, s, s', key, value)
      //case SplitStep() => Split(k, s, s')
      case GrowStep(childrenToLeft) => Grow(k, s, s', childrenToLeft)
    }
  }

  predicate Next<Value(!new)>(k: Constants, s: Variables, s': Variables) {
    exists step:Step :: NextStep(k, s, s', step)
  }

} // module BtreeSpec
