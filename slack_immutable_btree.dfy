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
    forall query', value, value', lookup: Lookup<Value>, lookup': Lookup<Value> ::
      && IsSatisfyingLookup(lb, tree, ub, query', value, lookup)
      && IsSatisfyingLookup(lb, tree, ub, query', value', lookup') ==>
      value == value'
  }

  predicate PreservesLookups<Value(!new)>(lb: Key, tree: Node, newtree: Node, ub: Key, exceptQuery: Key)
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
    ensures PreservesLookups(lb, tree, newtree, ub, query);
    ensures PreservesLookups(lb, newtree, tree, ub, query);
    ensures exists lookup :: IsSatisfyingLookup(lb, newtree, ub, query, value, lookup);
    ensures CantEquivocate(lb, newtree, ub);
    decreases tree;
  {
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

      // PreservesLookups proofs
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
  
  // function TreeContentsSeq<Value>(lb: Key, pivots: seq<Key>, trees: seq<Node<Value>>, ub: Key)
  //   : map<Key, Value>
  //   requires WFTree(Index(pivots, trees));
  //   ensures Keyspace.SetAllLte({lb}, TreeContentsSeq(lb, pivots, trees, ub).Keys);
  //   ensures Keyspace.SetAllLt(TreeContentsSeq(lb, pivots, trees, ub).Keys, {ub});
  //   decreases trees;
  // {
  //   if |pivots| == 1 then
  //     var left_contents := TreeContents(lb, trees[0], Keyspace.Min(ub, pivots[0]));
  //     var right_contents := TreeContents(Keyspace.Max(lb, pivots[0]), trees[1], ub);
  //     Maps.disjoint_union(left_contents, right_contents)
  //   else
  //     var map_0 := TreeContents(lb, trees[0], Keyspace.Min(ub, pivots[0]));
  //     var map_rest := TreeContentsSeq(Keyspace.Max(lb, pivots[0]), pivots[1..], trees[1..], ub);
  //     Maps.disjoint_union(map_0, map_rest)
  // }

  // function TreeContents<Value>(lb: Key, tree: Node<Value>, ub: Key)
  //   : map<Key, Value>
  //   requires WFTree(tree);
  //   ensures Keyspace.SetAllLte({lb}, TreeContents(lb, tree, ub).Keys);
  //   ensures Keyspace.SetAllLt(TreeContents(lb, tree, ub).Keys, {ub});
  //   decreases tree;
  // {
  //   if tree.Leaf? then
  //     map x : Key
  //     | x in tree.keys && Keyspace.lte(lb, x) && Keyspace.lt(x, ub)
  //     :: tree.values[IndexOf(tree.keys, x)]
  //   else
  //     TreeContentsSeq(lb, tree.pivots, tree.children, ub)
  // }

  // //
  // // Lookup(Insert(M, k, v), k') = { if k' == k then v else Lookup(M, k')
  // //
  
  // datatype QueryResult<Value> = NotFound | Found(value: Value)
  
  // function method Query<Value>(lb: Key, tree: Node<Value>, ub: Key, query: Key) : QueryResult<Value>
  //   requires WFTree(tree);
  //   decreases tree;
  // {
  //   if tree.Leaf? then
  //     if Keyspace.lt(query, lb) || Keyspace.lte(ub, query) then NotFound
  //     else 
  //       var pos := Keyspace.LargestLte(tree.keys, query);
  //       if pos >= 0 && tree.keys[pos] == query then Found(tree.values[pos])
  //       else NotFound
  //   else 
  //     var pos := Keyspace.LargestLte(tree.pivots, query);
  //     var newlb := LeftBound(lb, tree.pivots, tree.children, pos+1);
  //     var newub := RightBound(tree.pivots, tree.children, ub, pos+1);
  //     Query(newlb, tree.children[pos+1], newub, query)
  // }


  // function method Define<Value>(lb: Key, tree: Node<Value>, ub: Key, query: Key, value: Value) : Node<Value>
  //   requires WFTree(tree);
  //   ensures WFTree(Define(lb, tree, ub, query, value));
  //   ensures Query(lb, Define(lb, tree, ub, query, value), ub, query) == Found(value);
  //   ensures forall key :: key != query ==> Query(lb, Define(lb, tree, ub, query, value), ub, key) == Query(lb, tree, ub, query);
  //   decreases tree;
  // {
  //   if tree.Leaf? then
  //     var pos := Keyspace.LargestLte(tree.keys, query);
  //     if pos >= 0 && tree.keys[pos] == query then
  //       var result := Leaf(tree.keys, tree.values[pos := value]);
  //       // assert forall key :: key in tree.keys <==> key in result.keys;
  //       // assert forall key :: key !in tree.keys ==> Query(lb, tree, ub, key) == Query(lb, result, ub, key) == NotFound;
  //       // assert forall key :: key in tree.keys ==> Keyspace.LargestLte(result.keys, key) == Keyspace.LargestLte(tree.keys, key);
  //       // assert forall key :: key in tree.keys && key != query ==>
  //       //   Keyspace.LargestLte(result.keys, key) != Keyspace.LargestLte(result.keys, query);
  //       // assert forall key :: key in tree.keys && key != query ==>
  //       //     result.values[Keyspace.LargestLte(result.keys, key)] == tree.values[Keyspace.LargestLte(tree.keys, key)];
  //       assert forall key :: key != query ==> Query(lb, result, ub, key) == Query(lb, tree, ub, query);
  //       result
  //     else
  //       var newkeys := tree.keys[..pos+1] + [query] + tree.keys[pos+1..];
  //       var newvals := tree.values[..pos+1] + [value] + tree.values[pos+1..];
  //       assert forall i :: 0 <= i <= pos+1 ==> Keyspace.lte(newkeys[i], query);
  //       assert forall i :: pos+2 <= i < |newkeys| ==> Keyspace.lt(query, newkeys[i]);
  //       var result := Leaf(newkeys, newvals);
  //       assert forall key :: key != query ==> Query(lb, result, ub, key) == Query(lb, tree, ub, query);
  //       result
  //   else
  //     var pos := Keyspace.LargestLte(tree.pivots, query);
  //     var newlb := LeftBound(lb, tree.pivots, tree.children, pos+1);
  //     var newub := RightBound(tree.pivots, tree.children, ub, pos+1);
  //     var newchild := Define(newlb, tree.children[pos+1], newub, query, value);
  //     var result := Index(tree.pivots, tree.children[..pos+1] + [newchild] + tree.children[pos+2..]);
  //     assert forall key :: key != query ==> Query(lb, result, ub, key) == Query(lb, tree, ub, query);
  //     result
  // }
  
  // lemma TreeContentsDelegation<Value>(lb: Key, tree: Node<Value>, ub: Key, query: Key, pos: int, newlb: Key, newub: Key)
  //   requires WFTree(tree);
  //   requires tree.Index?;
  //   requires query in TreeContents(lb, tree, ub);
  //   requires pos == Keyspace.LargestLte(tree.pivots, query);
  //   requires newlb == LeftBound(lb, tree.pivots, tree.children, pos+1);
  //   requires newub == RightBound(tree.pivots, tree.children, ub, pos+1);
  //   ensures query in TreeContents(newlb, tree.children[pos+1], newub);
  //   ensures TreeContents(lb, tree, ub)[query] == TreeContents(newlb, tree.children[pos+1], newub)[query];
  // {
  //   assert query in TreeContentsSeq(lb, tree.pivots, tree.children, ub);
  //   assert exists i ::
  //     && 0 <= i < |tree.children|
  //     && query in TreeContents(LeftBound(lb, tree.pivots, tree.children, i),
  //                            tree.children[i], 
  //                            RightBound(tree.pivots, tree.children, ub, i));
  // }

  /*
  predicate PivotLteNextSubtree(tree: Node, pivot: int)
    requires WFTree(tree);
    requires tree.Index?;
    requires 0 <= pivot < |tree.pivots|;
  {
    Keyspace.SetAllLte({tree.pivots[pivot]}, TreeAllKeys(RightChild(tree, pivot)))
  }

  predicate SubtreeLtNextPivot(tree: Node, pivot: int)
    requires WFTree(tree);
    requires tree.Index?;
    requires 0 <= pivot < |tree.pivots|;
  {
    Keyspace.SetAllLt(TreeAllKeys(LeftChild(tree, pivot)), {tree.pivots[pivot]})
  }

  predicate SubtreeIsOrdered(tree: Node, child: int)
    requires WFTree(tree);
    requires tree.Index?;
    requires 0 <= child < |tree.children|;
  {
    TreeIsOrdered(tree.children[child])
  }
  
  predicate TreeIsOrdered(tree: Node)
    requires WFTree(tree);
  {
    if tree.Leaf? then
      && Keyspace.IsSorted(tree.keys)
      && NoDupes(tree.keys)
    else
      && Keyspace.IsSorted(tree.pivots)
      && NoDupes(tree.pivots)
      && (forall i :: 0 <= i < |tree.pivots|   ==> SubtreeLtNextPivot(tree, i))
      && (forall i :: 0 <= i < |tree.pivots|   ==> PivotLteNextSubtree(tree, i))
      && (forall i :: 0 <= i < |tree.children| ==> SubtreeIsOrdered(tree, i))
  }

  lemma EvaluateIsCorrect(tree: Node, key: Keyspace.Element, pos: int)
    requires WFTree(tree);
    requires TreeIsOrdered(tree);
    requires tree.Index?;
    requires key in TreeContents(tree);
    requires -1 <= pos < |tree.pivots|;
    requires 0 <= pos ==> Keyspace.lte(tree.pivots[pos], key);
    requires pos < |tree.pivots|-1 ==> Keyspace.lt(key, tree.pivots[pos+1]);
    ensures key in TreeContents(tree.children[pos+1]);
    ensures TreeContents(tree)[key] == TreeContents(tree.children[pos+1])[key];
  {
    forall i | 0 <= i < |tree.children| && i != pos+1
      ensures key !in TreeAllKeys(tree.children[i]);
    {
      if i <= pos {
        assert SubtreeLtNextPivot(tree, i); // TRIGGER
      } else {
        assert PivotLteNextSubtree(tree, i-1); // TRIGGER
      }
    }
    TreeContentsSeqExistentialForm(tree.children, key); // OBSERVE
  }

  function method Split(node: Node) : (Node, Keyspace.Element, Node)
    requires WFTree(node);
    requires node.Leaf? ==> |node.keys| >= 2;
    requires node.Index? ==> |node.pivots| >= 3;
    ensures WFTree(Split(node).0);
    ensures WFTree(Split(node).2);
  {
    if node.Leaf? then
      var half := |node.keys| / 2;
      (Leaf(node.keys[..half], node.values[..half]),
        node.keys[half],
        Leaf(node.keys[half..], node.values[half..]))
    else
      var half := (|node.pivots|) / 2;
      var new_left := Index(node.pivots[..half], node.children[..half+1]);
      var new_right := Index(node.pivots[half+1..], node.children[half+1..]);
      (new_left, node.pivots[half], new_right)
  }

  function method NeedsSplit(node: Node) : bool
    requires WFTree(node);
  {
    || (node.Leaf? && |node.keys| > max_leafsize())
      || (node.Index? && |node.pivots| > max_pivots())
  }
   */
  
  /*
  method Define<Value>(tree: Node<Value>, key: Keyspace.Element, value: Value) returns (new_tree: Node<Value>)
    requires WFTree(tree);
    requires TreeIsOrdered(tree);
    ensures WFTree(new_tree);
    ensures TreeAllKeys(new_tree) == TreeAllKeys(tree) + {key};
    ensures TreeIsOrdered(new_tree);
    ensures TreeContents(new_tree) == TreeContents(tree)[key := value];
  {
    if tree.Leaf? {
      var pos := Keyspace.FindLargestLTE(tree.keys, key);
      if pos >= 0 && tree.keys[pos] == key {
        new_tree := Leaf(tree.keys, tree.values[pos := value]);
      } else {
        assert forall i :: 0 <= i < pos+1 ==> Keyspace.lte(tree.keys[i], key);
        assert forall i :: pos + 1 <= i < |tree.keys| ==> Keyspace.lt(key, tree.keys[i]);
        new_tree := Leaf(tree.keys[..pos+1]   + [key]   + tree.keys[pos+1..],
                        tree.values[..pos+1] + [value] + tree.values[pos+1..]);
          assert WFTree(new_tree); // TRIGGER
      } 
    } else {
      var pos := Keyspace.FindLargestLTE(tree.pivots, key);
      assert SubtreeIsOrdered(tree, pos+1); // TRIGGER
      var new_subtree := Define(tree.children[pos+1], key, value);
      var new_children := tree.children[..pos+1] + [new_subtree] + tree.children[pos+2..];

      forall i | 0 <= i < |new_children|
        ensures WFTree(new_children[i]);
      {
      }
      
      ///////////// Le proof for AllKeys //////////////////////////
      forall key' | key' in TreeAllKeysSeq(tree.children) + {key}
        ensures key' in TreeAllKeysSeq(new_children);
      {
        if key' == key {
          assert key' in TreeAllKeys(new_subtree);
          assert key' in TreeAllKeys(new_children[pos+1]);
          TreeAllKeysSeqExistentialForm(new_children, key');
        } else {
          TreeAllKeysSeqExistentialForm(tree.children, key');
          var i :| 0 <= i < |tree.children| && key' in TreeAllKeys(tree.children[i]);
          if i < pos + 1 {
            assert key' in TreeAllKeys(new_children[i]);
          } else if i == pos + 1 {
            assert key' in TreeAllKeys(new_children[i]);
          } else {
            assert key' in TreeAllKeys(new_children[i]);
          }
          TreeAllKeysSeqExistentialForm(new_children, key');
        }
      }
      assert TreeAllKeysSeq(tree.children) <= TreeAllKeysSeq(new_children);
      assert key in TreeAllKeysSeq(new_children);
      
      forall key' | key' in TreeAllKeysSeq(new_children)
        ensures key' in TreeAllKeysSeq(tree.children) + {key};
      {
        TreeAllKeysSeqExistentialForm(new_children, key');
        var i :| 0 <= i < |new_children| && key' in TreeAllKeys(new_children[i]);
        if i < pos + 1 {
          assert key' in TreeAllKeys(tree.children[i]);
        } else if i == pos + 1 {
          assert key' in TreeAllKeys(tree.children[i]) + {key};
        } else {
          assert key' in TreeAllKeys(tree.children[i]);
        }
        TreeAllKeysSeqExistentialForm(tree.children, key');
      }
      assert TreeAllKeysSeq(tree.children) + {key} >= TreeAllKeysSeq(new_children);
      assert TreeAllKeysSeq(tree.children) + {key} == TreeAllKeysSeq(new_children);

      ///////////// Le proof for DefinedKeys //////////////////////////
      forall key' | key' in TreeDefinedKeysSeq(tree.children) + {key}
        ensures key' in TreeDefinedKeysSeq(new_children);
      {
        if key' == key {
          assert key' in TreeDefinedKeys(new_subtree);
          assert key' in TreeDefinedKeys(new_children[pos+1]);
          TreeDefinedKeysSeqExistentialForm(new_children, key');
        } else {
          TreeDefinedKeysSeqExistentialForm(tree.children, key');
          var i :| 0 <= i < |tree.children| && key' in TreeDefinedKeys(tree.children[i]);
          if i < pos + 1 {
            assert key' in TreeDefinedKeys(new_children[i]);
          } else if i == pos + 1 {
            assert key' in TreeDefinedKeys(new_children[i]);
          } else {
            assert key' in TreeDefinedKeys(new_children[i]);
          }
          TreeDefinedKeysSeqExistentialForm(new_children, key');
        }
      }
      assert TreeDefinedKeysSeq(tree.children) <= TreeDefinedKeysSeq(new_children);
      assert key in TreeDefinedKeysSeq(new_children);
      
      forall key' | key' in TreeDefinedKeysSeq(new_children)
        ensures key' in TreeDefinedKeysSeq(tree.children) + {key};
      {
        TreeDefinedKeysSeqExistentialForm(new_children, key');
        var i :| 0 <= i < |new_children| && key' in TreeDefinedKeys(new_children[i]);
        if i < pos + 1 {
          assert key' in TreeDefinedKeys(tree.children[i]);
        } else if i == pos + 1 {
          assert key' in TreeDefinedKeys(tree.children[i]) + {key};
        } else {
          assert key' in TreeDefinedKeys(tree.children[i]);
        }
        TreeDefinedKeysSeqExistentialForm(tree.children, key');
      }
      assert TreeDefinedKeysSeq(tree.children) + {key} >= TreeDefinedKeysSeq(new_children);
      assert TreeDefinedKeysSeq(tree.children) + {key} == TreeDefinedKeysSeq(new_children);

      new_tree := Index(tree.pivots, new_children);

      assert TreeAllKeys(new_tree) == TreeAllKeys(tree) + {key};
      assert TreeDefinedKeys(new_tree) == TreeDefinedKeys(tree) + {key};
      
      forall i | 0 <= i < |new_tree.pivots|
        ensures SubtreeLtNextPivot(new_tree, i);
        ensures PivotLteNextSubtree(new_tree, i);
      {
        if i < pos + 1 {
          assert SubtreeLtNextPivot(tree, i);
          assert PivotLteNextSubtree(tree, i);
        } else if i == pos + 1 {
          assert SubtreeLtNextPivot(tree, i);                
          assert PivotLteNextSubtree(tree, i);
        } else {
          assert SubtreeLtNextPivot(tree, i);
          assert PivotLteNextSubtree(tree, i);
        }
      }
        
      forall i | 0 <= i < |new_tree.children|
        ensures SubtreeIsOrdered(new_tree, i);
      {
        if i < pos + 1 {
          assert SubtreeIsOrdered(tree, i);
        } else if i == pos + 1 {
          assert SubtreeIsOrdered(new_tree, i);
        } else {
          assert SubtreeIsOrdered(tree, i);
        }
      }

      TreeContentsSeqExistentialForm(new_children, key);
      assert key in TreeDefinedKeys(new_tree);
      assert key in TreeContentsSeq(new_children);
      forall i | 0 <= i < |new_children| && i != pos+1
        ensures key !in TreeContents(new_children[i]);
      {
        if i < pos+1 {
          assert SubtreeLtNextPivot(new_tree, i);
          assert Keyspace.lte(new_tree.pivots[i], new_tree.pivots[pos]);
          Keyspace.SetLtLteTransitivity(TreeDefinedKeys(new_children[i]), {new_tree.pivots[pos]}, {key});
        } else {
          assert i > pos + 1;
          assert Keyspace.lte(new_tree.pivots[pos+1], new_tree.pivots[i-1]);
          assert PivotLteNextSubtree(new_tree, i-1);
          Keyspace.SetLtLteTransitivity({key}, {new_tree.pivots[pos+1]}, TreeDefinedKeys(new_children[i]));
        }
      }
      assert forall i :: 0 <= i < |new_children| && i != pos+1 ==> key !in TreeContents(new_children[i]);
      assert TreeContents(new_tree.children[pos+1])[key] == value;
      assert TreeContents(new_tree)[key] == value;

      forall key' | key' in TreeContents(tree) && key' != key
        ensures TreeContents(new_tree)[key'] == TreeContents(tree)[key'];
      {
        TreeContentsSeqExistentialForm(new_tree.children, key');
        TreeContentsSeqExistentialForm(tree.children, key');
        var newi :| 0 <= newi < |new_tree.children| && key' in TreeContents(new_tree.children[newi]);
        var oldi :| 0 <= oldi < |tree.children| && key' in TreeContents(tree.children[oldi]);
        assert PivotLteNextSubtree(new_tree, newi-1);
        assert forall i :: 0 <= i < newi ==> Keyspace.lte(new_tree.pivots[i], key');
        assert SubtreeLtNextPivot(new_tree, newi);
        assert forall i :: newi <= i < |new_tree.pivots| ==> Keyspace.lt(key', new_tree.pivots[i]);
        assert newi == oldi;
      }
      assert forall key' :: key' in TreeContents(tree) && key' != key ==> TreeContents(new_tree)[key'] == TreeContents(tree)[key'];

      forall key' | key' in TreeContents(new_tree) && key' != key
        ensures TreeContents(new_tree)[key'] == TreeContents(tree)[key'];
      {
      }

      assert TreeContents(new_tree).Keys == TreeContents(tree).Keys + {key};
      forall key' | key' in TreeContents(new_tree)
        ensures TreeContents(new_tree)[key'] == TreeContents(tree)[key := value][key'];
      {
        if key' == key {
          assert TreeContents(new_tree)[key'] == value;
        } else {
          assert TreeContents(new_tree)[key'] == TreeContents(tree)[key'];
        }
      }
      assert TreeContents(new_tree) == TreeContents(tree)[key := value];
    }
  }
*/
}
