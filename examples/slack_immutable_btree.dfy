include "total_order.dfy"
//include "lexical.dfy"
include "map_utils.dfy"
include "mathematics.dfy"
include "sequences.dfy"

abstract module ImmutableBTree {
  import Keyspace : Bounded_Total_Order
  import Maps = Map_Utils
  import Math = Mathematics
  import opened Sequences

  type Key = Keyspace.Element
  
  function method min_pivots()   : int { 5 }
  function method max_pivots()   : int { 10 }
  function method min_leafsize() : int { 5 }
  function method max_leafsize() : int { 10 }

  datatype Node<Value> =
    Leaf(keys: seq<Key>, values: seq<Value>) |
    Index(pivots: seq<Key>, children: seq<Node>)

  predicate WFTree(tree: Node) {
    if tree.Leaf? then
      && |tree.keys| > 0
      && NoDupes(tree.keys)
      && Keyspace.IsSorted(tree.keys)
      && |tree.keys| == |tree.values|
    else
      && |tree.pivots| > 0
      && Keyspace.IsSorted(tree.pivots)
      && |tree.children| == |tree.pivots| + 1
      && (forall i {:trigger WFTree(tree.children[i]) } :: 0 <= i <|tree.children| ==> WFTree(tree.children[i]))
  }

  predicate WFRoot(tree: Node) {
    if tree.Leaf? then
      && Keyspace.IsSorted(tree.keys)
      && |tree.keys| == |tree.values|
    else 
      WFTree(tree)
  }

  datatype Layer<Value(!new)> = Layer(lb: Key, ub: Key, node: Node<Value>, slot: int)
  type Lookup<Value(!new)> = seq<Layer<Value>>
    
  function method LeftBound(lb: Key, pivots: seq<Key>, trees: seq<Node>, child: int) : Key
    requires WFTree(Index(pivots, trees));
    requires 0 <= child < |trees|;
  {
    if child == 0 then lb
    else Keyspace.Max(lb, pivots[child-1])
  }

  function method RightBound(pivots: seq<Key>, trees: seq<Node>, ub: Key, child: int) : Key
    requires WFTree(Index(pivots, trees));
    requires 0 <= child < |trees|;
  {
    if child == |trees|-1 then ub
    else Keyspace.Min(ub, pivots[child])
  }
  
  predicate ValidLookup(lookup: Lookup)
  {
    if |lookup| == 0 then true
    else
      && (forall i :: 0 <= i < |lookup| - 1 ==> WFTree(lookup[i].node))
      && (forall i :: 0 <= i < |lookup| - 1 ==> lookup[i].node.Index?)
      && (forall i :: 0 <= i < |lookup| - 1 ==> 0 <= lookup[i].slot < |lookup[i].node.children|)
      && (forall i :: 0 <= i < |lookup| - 1 ==>
         lookup[i+1].lb == LeftBound(lookup[i].lb, lookup[i].node.pivots, lookup[i].node.children, lookup[i].slot))
      && (forall i :: 0 <= i < |lookup| - 1 ==>
         lookup[i+1].ub == RightBound(lookup[i].node.pivots, lookup[i].node.children, lookup[i].ub, lookup[i].slot))
      && (forall i :: 0 <= i < |lookup| - 1 ==> lookup[i+1].node == lookup[i].node.children[lookup[i].slot])
      && WFTree(Last(lookup).node)
      && Last(lookup).node.Leaf?
      && 0 <= Last(lookup).slot < |Last(lookup).node.keys|
      && Keyspace.lte(Last(lookup).lb, Last(lookup).node.keys[Last(lookup).slot])
      && Keyspace.lt(Last(lookup).node.keys[Last(lookup).slot], Last(lookup).ub)
  }

  predicate IsSatisfyingLookup<Value(!new)>(lb: Key, tree: Node, ub: Key, query: Key, value: Value, lookup: Lookup)
  {
    && ValidLookup(lookup)
    && |lookup| > 0
    && lookup[0].lb == lb
    && lookup[0].ub == ub
    && lookup[0].node == tree
    && Last(lookup).node.keys[Last(lookup).slot] == query
    && Last(lookup).node.values[Last(lookup).slot] == value
  }

  lemma SatisfyingLookupsNest<Value(!new)>(lb: Key, tree: Node, ub: Key, query: Key, value: Value, lookup: Lookup)
    requires IsSatisfyingLookup(lb, tree, ub, query, value, lookup);
    requires tree.Index?;
    ensures IsSatisfyingLookup(LeftBound(lb, tree.pivots, tree.children, lookup[0].slot),
                               tree.children[lookup[0].slot],
                               RightBound(tree.pivots, tree.children, ub, lookup[0].slot),
                               query, value,
                               lookup[1..]);
  {
  }

  lemma SatisfyingLookupsAllBoundsContainQuery<Value>(lb: Key, tree: Node, ub: Key, query: Key, value: Value, lookup: Lookup)
    requires IsSatisfyingLookup(lb, tree, ub, query, value, lookup);
    ensures Keyspace.lte(lookup[0].lb, query);
    ensures Keyspace.lt(query, lookup[0].ub);
    decreases tree;
  {
    if tree.Leaf? {
      assert |lookup| == 1;
    } else {
      SatisfyingLookupsNest(lb, tree, ub, query, value, lookup);
      SatisfyingLookupsAllBoundsContainQuery(lookup[1].lb, tree.children[lookup[0].slot], lookup[1].ub, query, value, lookup[1..]);
    }
  }
  
  datatype QueryResult<Value> = NotDefined | Defined(value: Value) //, ghost lookup: Lookup<Value>)
    
  method Query<Value>(lb: Key, tree: Node, ub: Key, query: Key) returns (result: QueryResult)
    requires WFTree(tree);
    ensures result.NotDefined? ==> !exists lookup, value :: IsSatisfyingLookup(lb, tree, ub, query, value, lookup);
    ensures result.Defined? ==> exists lookup: Lookup :: IsSatisfyingLookup(lb, tree, ub, query, result.value, lookup);
    decreases tree;
  {
    if tree.Leaf? {
      var pos := Keyspace.LargestLte(tree.keys, query);
      if pos >= 0 && tree.keys[pos] == query && Keyspace.lte(lb, query) && Keyspace.lt(query, ub) {
        result := Defined(tree.values[pos]); //, [Layer(lb, ub, tree, pos)]);
        assert IsSatisfyingLookup(lb, tree, ub, query, result.value, [Layer(lb, ub, tree, pos)]); //result.lookup);
      } else {
        result := NotDefined;
      }
    } else {
      var pos := Keyspace.LargestLte(tree.pivots, query) + 1;
      var sublb := LeftBound(lb, tree.pivots, tree.children, pos);
      var subub := RightBound(tree.pivots, tree.children, ub, pos);
      var subresult := Query(sublb, tree.children[pos], subub, query);
      if subresult.NotDefined? {
        result := NotDefined;
        forall lookup: Lookup, value: Value | IsSatisfyingLookup(lb, tree, ub, query, value, lookup)
          ensures !IsSatisfyingLookup(lb, tree, ub, query, value, lookup);
        {
          SatisfyingLookupsNest(lb, tree, ub, query, value, lookup);
          assert lookup[0].slot != pos;
          if lookup[0].slot < pos {
            assert Keyspace.lte(lookup[1].ub, tree.pivots[lookup[0].slot]);
            assert Keyspace.lte(tree.pivots[lookup[0].slot], tree.pivots[pos-1]);
            assert Keyspace.lte(tree.pivots[pos-1], query);
            assert Keyspace.lte(lookup[1].ub, query);
            SatisfyingLookupsAllBoundsContainQuery(lookup[1].lb, tree.children[lookup[0].slot], lookup[1].ub, query, value, lookup[1..]);
            assert !IsSatisfyingLookup(lookup[1].lb, tree.children[lookup[0].slot], lookup[1].ub, query, value, lookup[1..]);
            assert !IsSatisfyingLookup(lb, tree, ub, query, value, lookup);
          } else {
            assert Keyspace.lt(query, tree.pivots[pos]);
            assert Keyspace.lte(tree.pivots[pos], tree.pivots[lookup[0].slot-1]);
            assert Keyspace.lte(tree.pivots[lookup[0].slot-1], lookup[1].lb);
            assert Keyspace.lt(query, lookup[1].lb);
            SatisfyingLookupsAllBoundsContainQuery(lookup[1].lb, tree.children[lookup[0].slot], lookup[1].ub, query, value, lookup[1..]);
            assert !IsSatisfyingLookup(lookup[1].lb, tree.children[lookup[0].slot], lookup[1].ub, query, value, lookup[1..]);
            assert !IsSatisfyingLookup(lb, tree, ub, query, value, lookup);
          }
        }
      } else {
        result := Defined(subresult.value); //, [Layer(lb, ub, tree, pos)] + subresult.lookup);
        ghost var sublookup :| IsSatisfyingLookup(sublb, tree.children[pos], subub, query, result.value, sublookup);
        assert IsSatisfyingLookup(lb, tree, ub, query, result.value, [Layer(lb, ub, tree, pos)] + sublookup);
      }
    }
  }

  predicate CantEquivocate<Value(!new)>(lb: Key, tree: Node<Value>, ub: Key)
  {
    forall query', value, value', lookup: Lookup<Value>, lookup': Lookup<Value> /*{:trigger dummy(query',value,value',lookup,lookup') }*/ ::
      && IsSatisfyingLookup(lb, tree, ub, query', value, lookup)
      && IsSatisfyingLookup(lb, tree, ub, query', value', lookup') ==>
      value == value'
  }

  predicate PreservesLookups<Value(!new)>(lb: Key, tree: Node, newtree: Node, ub: Key)
  {
    forall lookup, query', value' :: IsSatisfyingLookup(lb, tree, ub, query', value', lookup) ==>
    exists lookup' :: IsSatisfyingLookup(lb, newtree, ub, query', value', lookup')
  }

  predicate PreservesLookupsExcept<Value(!new)>(lb: Key, tree: Node, newtree: Node, ub: Key, exceptQuery: Key)
  {
    forall lookup, query', value' :: query' != exceptQuery && IsSatisfyingLookup(lb, tree, ub, query', value', lookup) ==>
    exists lookup' :: IsSatisfyingLookup(lb, newtree, ub, query', value', lookup')
  }

  lemma SatisfyingLookupSlotIsLargestLte<Value>(lb: Key, tree: Node, ub: Key, query: Key, value: Value, lookup: Lookup)
    requires IsSatisfyingLookup(lb, tree, ub, query, value, lookup);
    requires tree.Index?;
    ensures lookup[0].slot == Keyspace.LargestLte(tree.pivots, query) + 1;
  {
    var pos := Keyspace.LargestLte(tree.pivots, query) + 1;
    if lookup[0].slot < pos {
      SatisfyingLookupsNest(lb, tree, ub, query, value, lookup);
      SatisfyingLookupsAllBoundsContainQuery(lookup[1].lb, lookup[1].node, lookup[1].ub, query, value, lookup[1..]);
      assert Keyspace.lt(query, lookup[1].ub);
      assert Keyspace.lte(lookup[1].ub, tree.pivots[lookup[0].slot]);
      assert Keyspace.lte(tree.pivots[lookup[0].slot], tree.pivots[pos-1]);
      assert Keyspace.lte(tree.pivots[pos-1], query);
      assert false;
    } else if lookup[0].slot > pos {
      SatisfyingLookupsNest(lb, tree, ub, query, value, lookup);
      SatisfyingLookupsAllBoundsContainQuery(lookup[1].lb, lookup[1].node, lookup[1].ub, query, value, lookup[1..]);
      assert Keyspace.lt(query, tree.pivots[pos]);
      assert Keyspace.lte(tree.pivots[pos], tree.pivots[lookup[0].slot-1]);
      assert Keyspace.lte(tree.pivots[lookup[0].slot-1], lookup[1].lb);
      assert Keyspace.lte(lookup[1].lb, query);
      assert false;
    }
  }
  
  method Define<Value>(lb: Key, tree: Node, ub: Key, query: Key, value: Value) returns (newtree: Node)
    requires WFTree(tree);
    requires CantEquivocate(lb, tree, ub);
    requires Keyspace.lte(lb, query);
    requires Keyspace.lt(query, ub);
    ensures PreservesLookupsExcept(lb, tree, newtree, ub, query);
    ensures PreservesLookupsExcept(lb, newtree, tree, ub, query);
    ensures exists lookup :: IsSatisfyingLookup(lb, newtree, ub, query, value, lookup);
    ensures CantEquivocate(lb, newtree, ub);
    decreases tree;
  {
    reveal_NoDupes();
    if tree.Leaf? {
      var pos := Keyspace.LargestLte(tree.keys, query);
      if pos >= 0 && query == tree.keys[pos] {
        newtree := Leaf(tree.keys, tree.values[pos := value]);
        
        forall lookup: Lookup, query', value'
          | query' != query && IsSatisfyingLookup(lb, tree, ub, query', value', lookup)
          ensures exists lookup' :: IsSatisfyingLookup(lb, newtree, ub, query', value', lookup');
        {
          var lookup' := [Layer(lookup[0].lb, lookup[0].ub, newtree, lookup[0].slot)];
          assert IsSatisfyingLookup(lb, newtree, ub, query', value', lookup');
        }
        forall lookup': Lookup, query', value'
          | query' != query && IsSatisfyingLookup(lb, newtree, ub, query', value', lookup')
          ensures exists lookup :: IsSatisfyingLookup(lb, tree, ub, query', value', lookup);
        {
          var lookup := [Layer(lookup'[0].lb, lookup'[0].ub, tree, lookup'[0].slot)];
          assert IsSatisfyingLookup(lb, tree, ub, query', value', lookup);
        }

        assert IsSatisfyingLookup(lb, newtree, ub, query, value, [Layer(lb, ub, newtree, pos)]);

      } else {
        var newkeys := tree.keys[..pos+1] + [query] + tree.keys[pos+1..];
        var newvals := tree.values[..pos+1] + [value] + tree.values[pos+1..];
        newtree := Leaf(newkeys, newvals);
        //assert Keyspace.IsSorted(newtree.keys);
        assert IsSatisfyingLookup(lb, newtree, ub, query, value, [Layer(lb, ub, newtree, pos + 1)]);
        
        forall lookup: Lookup, query', value'
          | query' != query && IsSatisfyingLookup(lb, tree, ub, query', value', lookup)
          ensures exists lookup' :: IsSatisfyingLookup(lb, newtree, ub, query', value', lookup');
        {
          if lookup[0].slot <= pos {
            var lookup' := [Layer(lookup[0].lb, lookup[0].ub, newtree, lookup[0].slot)];
            assert IsSatisfyingLookup(lb, newtree, ub, query', value', lookup');
          } else {
            var lookup' := [Layer(lookup[0].lb, lookup[0].ub, newtree, lookup[0].slot + 1)];
            assert IsSatisfyingLookup(lb, newtree, ub, query', value', lookup');
          }
        }
        forall lookup': Lookup, query', value'
          | query' != query && IsSatisfyingLookup(lb, newtree, ub, query', value', lookup')
          ensures exists lookup :: IsSatisfyingLookup(lb, tree, ub, query', value', lookup);
        {
          assert lookup'[0].slot != pos+1;
          if lookup'[0].slot <= pos {
            var lookup := [Layer(lookup'[0].lb, lookup'[0].ub, tree, lookup'[0].slot)];
            assert IsSatisfyingLookup(lb, tree, ub, query', value', lookup);
          } else {
            var lookup := [Layer(lookup'[0].lb, lookup'[0].ub, tree, lookup'[0].slot - 1)];
            assert IsSatisfyingLookup(lb, tree, ub, query', value', lookup);
          }
        }

      }
    } else {
      var pos := Keyspace.LargestLte(tree.pivots, query) + 1;
      var newlb := LeftBound(lb, tree.pivots, tree.children, pos);
      var newub := RightBound(tree.pivots, tree.children, ub, pos);

      // Before we can call Define recursively, we must prove that the child CantEquivocate.
      forall query', valueA, valueB, lookup, lookup'
      |
      && IsSatisfyingLookup(newlb, tree.children[pos], newub, query', valueA, lookup)
      && IsSatisfyingLookup(newlb, tree.children[pos], newub, query', valueB, lookup')
      ensures valueA == valueB;
      {
        var plookup  := [Layer(lb, ub, tree, pos)] + lookup;
        var plookup' := [Layer(lb, ub, tree, pos)] + lookup';
        assert IsSatisfyingLookup(lb, tree, ub, query', valueA, plookup);
        assert IsSatisfyingLookup(lb, tree, ub, query', valueB, plookup');
      }
      var newchild := Define(newlb, tree.children[pos], newub, query, value);
      newtree := Index(tree.pivots, tree.children[pos := newchild]);

      // PreservesLookupsExcept proofs
      forall lookup: Lookup, query', value'
        | query' != query && IsSatisfyingLookup(lb, tree, ub, query', value', lookup)
        ensures exists lookup' :: IsSatisfyingLookup(lb, newtree, ub, query', value', lookup');
      {
        SatisfyingLookupsNest(lb, tree, ub, query', value', lookup);
        var clookup := lookup[1..];
        assert IsSatisfyingLookup(clookup[0].lb, tree.children[lookup[0].slot], clookup[0].ub, query', value', clookup);
        var clookup' :| IsSatisfyingLookup(clookup[0].lb, newtree.children[lookup[0].slot], clookup[0].ub, query', value', clookup');
        var lookup' := [Layer(lb, ub, newtree, lookup[0].slot)] + clookup';
        assert IsSatisfyingLookup(lb, newtree, ub, query', value', lookup');
      }
      forall lookup': Lookup, query', value'
        | query' != query && IsSatisfyingLookup(lb, newtree, ub, query', value', lookup')
        ensures exists lookup :: IsSatisfyingLookup(lb, tree, ub, query', value', lookup);
      {
        SatisfyingLookupsNest(lb, newtree, ub, query', value', lookup');
        var clookup' := lookup'[1..];
        assert IsSatisfyingLookup(clookup'[0].lb, newtree.children[lookup'[0].slot], clookup'[0].ub, query', value', clookup');
        var clookup: Lookup<Value> :| IsSatisfyingLookup(clookup'[0].lb, tree.children[lookup'[0].slot], clookup'[0].ub, query', value', clookup);
        var lookup := [Layer(lb, ub, tree, lookup'[0].slot)] + clookup;
        assert IsSatisfyingLookup(lb, tree, ub, query', value', lookup);
      }

      // Proof that we can lookup query and get value
      ghost var clookup :| IsSatisfyingLookup(newlb, newtree.children[pos], newub, query, value, clookup);
      ghost var lookup := [Layer(lb, ub, newtree, pos)] + clookup;
      assert IsSatisfyingLookup(lb, newtree, ub, query, value, lookup);

      // Proof that we CantEquivocate
      forall query', valueA, valueB, lookupA: Lookup, lookupB: Lookup
      |
      && IsSatisfyingLookup(lb, newtree, ub, query', valueA, lookupA)
      && IsSatisfyingLookup(lb, newtree, ub, query', valueB, lookupB)
      ensures valueA == valueB;
      {
        SatisfyingLookupSlotIsLargestLte(lb, newtree, ub, query', valueA, lookupA);
        SatisfyingLookupSlotIsLargestLte(lb, newtree, ub, query', valueB, lookupB);
        SatisfyingLookupsNest(lb, newtree, ub, query', valueA, lookupA);
        SatisfyingLookupsNest(lb, newtree, ub, query', valueB, lookupB);
      }
      assert CantEquivocate(lb, newtree, ub);
    }
  }

  method Improve<Value>(lb: Key, tree: Node, ub: Key) returns (newtree: Node)
    requires WFTree(tree);
    requires CantEquivocate(lb, tree, ub);
    ensures PreservesLookups(lb, tree, newtree, ub);
    ensures PreservesLookups(lb, newtree, tree, ub);
    ensures CantEquivocate(lb, newtree, ub);
    decreases tree;
  {
    if (tree.Leaf?) {
      return tree;
    }

    var descend:bool :| true;
    if (descend) {
      var slot:int :| 0 <= slot < |tree.children|;
      var new_child := Improve(LeftBound(lb, tree.pivots, tree.children, slot),
          tree.children[slot],
          RightBound(tree.pivots, tree.children, ub, slot));
      return Index(tree.pivots, tree.children[.. slot] + [new_child] + tree.children[slot + 1 .. ]);
    } else {
      // TODO replace slot with the two children of the returned node
      var sp := Split(lb, tree, ub);
      return sp;
    }
  }
  
  method Split<Value>(lb: Key, tree: Node, ub: Key) returns (newtree: Node)
    requires WFTree(tree);
    requires CantEquivocate(lb, tree, ub);
    ensures PreservesLookups(lb, tree, newtree, ub);
    ensures PreservesLookups(lb, newtree, tree, ub);
    ensures CantEquivocate(lb, newtree, ub);
    decreases tree;
  {
    if (tree.Leaf?) {
      assert PreservesLookups(lb, tree, tree, ub);
      return tree;
    }

    if (|tree.children| < 4) {
      assert PreservesLookups(lb, tree, tree, ub);
      return tree;
    }

    var split:int :| 1 < split < |tree.children| - 1;
    var left_child := Index(
        tree.pivots[ .. split - 1],
        tree.children[ .. split]);

    var right_child := Index(
        tree.pivots[split .. ],
        tree.children[split .. ]);

    var nt := Index(
        [tree.pivots[split - 1]],
        [left_child, right_child]);

    assert WFTree(left_child);
    assert WFTree(right_child);

    forall lookup:Lookup<Value>, query', value' | IsSatisfyingLookup(lb, tree, ub, query', value', lookup)
    ensures exists lookup' :: IsSatisfyingLookup(lb, nt, ub, query', value', lookup')
    {
      var original_top_layer := lookup[0];
      if (original_top_layer.slot < split) {
        var layer1 := Layer(lb, ub, nt, 0);
        var layer2 := Layer(lb, RightBound(nt.pivots, nt.children, ub, 0), left_child, original_top_layer.slot);
        var lookup' := [layer1, layer2] + lookup[1 .. ];

        assert lookup'[1].ub == RightBound(lookup'[0].node.pivots, lookup'[0].node.children, lookup'[0].ub, lookup'[0].slot);

        assert IsSatisfyingLookup(lb, nt, ub, query', value', lookup');
      } else {
        var layer1 := Layer(lb, ub, nt, 1);
        var layer2 := Layer(LeftBound(lb, nt.pivots, nt.children, 1), ub, right_child, original_top_layer.slot - split);
        var lookup' := [layer1, layer2] + lookup[1 .. ];
        assert IsSatisfyingLookup(lb, nt, ub, query', value', lookup');
      }
    }

    forall lookup:Lookup<Value>, query', value' | IsSatisfyingLookup(lb, nt, ub, query', value', lookup)
    ensures exists lookup' :: IsSatisfyingLookup(lb, tree, ub, query', value', lookup')
    {
      var layer1 := lookup[0];
      var layer2 := lookup[1];
      if (layer1.slot == 0) {
        var layer := Layer(lb, ub, tree, layer2.slot);
        var lookup' := [layer] + lookup[2 .. ];
        assert IsSatisfyingLookup(lb, tree, ub, query', value', lookup');
      } else {
        assert layer1.slot == 1;
        var layer := Layer(lb, ub, tree, layer2.slot + split);
        var lookup' := [layer] + lookup[2 .. ];
        assert IsSatisfyingLookup(lb, tree, ub, query', value', lookup');
      }
    }

    assert PreservesLookups(lb, tree, nt, ub);

    return nt;

  }
}
