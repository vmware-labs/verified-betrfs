include "../lib/total_order.dfy"
include "../lib/map_utils.dfy"
include "../lib/mathematics.dfy"
include "../lib/sequences.dfy"

abstract module BtreeSpec {
  import Keyspace = Bounded_Total_Order

  type Key = Keyspace.Element

  datatype Node<Value> =
    Leaf(keys: seq<Key>, values: seq<Value>) |
    Index(pivots: seq<Key>, children: seq<Node>)

  datatype Constants = Constants();
  datatype Variables = Variables(root: Node);

  predicate Init(k: Constants, s: Variables) {
  }

  datatype Layer<Value(!new)> = Layer(lb: Key, ub: Key, node: Node<Value>, slot: int)
  type Lookup<Value(!new)> = seq<Layer<Value>>

  predicate Get(k: Constants, s: Variables, s': Variables, key: Key, value: Value, lookup: Lookup)
  {
    && IsSatisfyingLookup(s.root, key, value, lookup)
    && s' == s
  }

  predicate PutTransform(tree:Node, newtree:Node, key:Key, value:Value)
    decreases tree;
  {
    if tree.Leaf? then (
      var pos := Keyspace.LargestLte(tree.keys, query);
      if pos >= 0 && query == tree.keys[pos] (
        newtree == Leaf(tree.keys, tree.values[pos := value]);
      ) else (
        var newkeys := tree.keys[..pos+1] + [query] + tree.keys[pos+1..];
        var newvals := tree.values[..pos+1] + [value] + tree.values[pos+1..];
        newtree == Leaf(newkeys, newvals);
      )
    ) else (
      var pos := Keyspace.LargestLte(tree.pivots, query) + 1;
      var newlb := LeftBound(lb, tree.pivots, tree.children, pos);
      var newub := RightBound(tree.pivots, tree.children, ub, pos);

      // Before we can call Define recursively, we must prove that the child CantEquivocate.
      var newchild := PutTransform(newlb, tree.children[pos], newub, query, value);
      newtree := Index(tree.pivots, tree.children[pos := newchild]);
    )
  }

  predicate Put(k: Constants, s: Variables, s': Variables, key: Key, value: Value)
  {
    && PutTransform(s.root, s'.root, key, value)
  }

  datatype Step =
    | GetStep(key: Key, value: Value, lookup: Lookup)
    | PutStep(key: Key, value: Value)
    | SplitStep()
    | GrowStep()

  predicate NextStep(k: Constants, s: Variables, s': Variables, step:Step) {
    match step {
      case GetStep(key, value, lookup) => Get(k, s, s', key, value, lookup)
      case PutStep() => Put(k, s, s', key, value)
      case SplitStep() => Split(k, s, s')
      case GrowStep() => GrowStep(k, s, s')
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables) {
    exists step:Step :: NextStep(k, s, s', step)
  }

} // module BtreeSpec
