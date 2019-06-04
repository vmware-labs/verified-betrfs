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

  datatype Step =
    | GetStep(key: Key, value: Value, lookup: Lookup)
    | PutStep(key: Key, value: Value, lookup: Lookup)
    | SplitStep()
    | GrowStep()

  datatype Layer<Value(!new)> = Layer(lb: Key, ub: Key, node: Node<Value>, slot: int)
  type Lookup<Value(!new)> = seq<Layer<Value>>

  predicate Get(k: Constants, s: Variables, s': Variables, key: Key, value: Value, lookup: Lookup)
  {
    && IsSatisfyingLookup(s.root, key, value, lookup)
    && s' == s
  }

  predicate Put(k: Constants, s: Variables, s': Variables, key: Key, value: Value, lookup: Lookup)
  {
    
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, step:Step) {
    match step {
      case GetStep(key, value, lookup) => Get(k, s, s', key, value, lookup)
      case PutStep() => 
      case SplitStep() => 
      case GrowStep() => 
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables) {
    exists step:Step :: NextStep(k, s, s', step)
  }

} // module BtreeSpec
