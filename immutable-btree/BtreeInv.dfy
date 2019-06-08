include "../lib/total_order.dfy"
include "../lib/map_utils.dfy"
include "../lib/mathematics.dfy"
include "../lib/sequences.dfy"
include "BtreeSpec.dfy"

abstract module BtreeInv {
  import opened Spec : BtreeSpec
  import opened Sequences

  predicate CantEquivocate<Value(!new)>(tree: Node<Value>)
  {
    forall key, value, value', lookup: Lookup<Value>, lookup': Lookup<Value> ::
      && IsSatisfyingLookup(tree, key, value, lookup)
      && IsSatisfyingLookup(tree, key, value', lookup') ==>
      value == value'
  }


  predicate Invariant(k: Constants, s: Variables) {
    && WFRoot(s.root)
    && CantEquivocate(s.root)
  }


  predicate PreservesLookups<Value(!new)>(tree: Node, newtree: Node)
  {
    forall lookup, key, value :: IsSatisfyingLookup(tree, key, value, lookup) ==>
    exists lookup' :: IsSatisfyingLookup(newtree, key, value, lookup')
  }

  predicate PreservesLookupsExcept<Value(!new)>(tree: Node, newtree: Node, exceptQuery: Key)
  {
    forall lookup, key, value :: key != exceptQuery && IsSatisfyingLookup(tree, key, value, lookup) ==>
    exists lookup' :: IsSatisfyingLookup(newtree, key, value, lookup')
  }

  lemma SatisfyingLookupsNest<Value(!new)>(tree: Node, key: Key, value: Value, lookup: Lookup)
    requires IsSatisfyingLookup(tree, key, value, lookup);
    requires tree.Index?;
    ensures IsSatisfyingLookup(tree.children[lookup[0].slot],
                               key, value,
                               lookup[1..]);
  {
  }

  lemma BoundsNest(tree: Node, child: int)
    requires WFTree(tree);
    requires tree.Index?;
    requires 0 <= child < |tree.children|;
    ensures CSMap.Keyspace.lte(tree.lb, tree.children[child].lb);
    ensures CSMap.Keyspace.lte(tree.children[child].ub, tree.ub);
  {
    if child == 0 {
      assert CSMap.Keyspace.lte(tree.lb, tree.children[child].lb);
    } else {
      assert CSMap.Keyspace.lte(tree.lb, tree.pivots[child-1]);
      assert CSMap.Keyspace.lte(tree.lb, tree.children[child].lb);
    }

    if child == |tree.children| - 1 {
      assert CSMap.Keyspace.lte(tree.children[child].ub, tree.ub);
    } else {
      assert CSMap.Keyspace.lte(tree.pivots[child], tree.ub);
      assert CSMap.Keyspace.lte(tree.children[child].ub, tree.ub);
    }
  }
  
  lemma SatisfyingLookupsAllBoundsContainQuery<Value>(tree: Node, key: Key, value: Value, lookup: Lookup)
    requires WFTree(tree)
    requires IsSatisfyingLookup(tree, key, value, lookup);
    ensures CSMap.Keyspace.lte(lookup[0].node.lb, key);
    ensures CSMap.Keyspace.lt(key, lookup[0].node.ub);
    decreases tree;
  {
    if tree.Leaf? {
    } else {
      SatisfyingLookupsAllBoundsContainQuery(tree.children[lookup[0].slot], key, value, lookup[1..]);
      BoundsNest(tree, lookup[0].slot);
    }
  }

  lemma SatisfyingLookupSlotIsLargestLte<Value>(tree: Node, key: Key, value: Value, lookup: Lookup)
    requires WFTree(tree)
    requires IsSatisfyingLookup(tree, key, value, lookup);
    requires tree.Index?;
    ensures lookup[0].slot == CSMap.Keyspace.LargestLte(tree.pivots, key) + 1;
  {
    var pos := CSMap.Keyspace.LargestLte(tree.pivots, key) + 1;
    if lookup[0].slot < pos {
      SatisfyingLookupsAllBoundsContainQuery(lookup[1].node, key, value, lookup[1..]);
      assert false;
    } else if lookup[0].slot > pos {
      SatisfyingLookupsNest(tree, key, value, lookup);
      SatisfyingLookupsAllBoundsContainQuery(lookup[1].node, key, value, lookup[1..]);
      assert CSMap.Keyspace.lte(tree.pivots[lookup[0].slot-1], lookup[1].node.lb);
      assert false;
    }
  }

  lemma valueEqValue<Value>(tree:Node, k: Key, value: Value, value': Value, lookup: Lookup<Value>, lookup': Lookup<Value>)
  requires IsSatisfyingLookup(tree, k, value, lookup);
  requires IsSatisfyingLookup(tree, k, value', lookup');
  requires tree.Leaf?
  requires CSMap.Keyspace.IsStrictlySorted(tree.keys);
  ensures value == value'
  {
    CSMap.Keyspace.reveal_IsStrictlySorted();
  }

  lemma leafCantEquivocate<Value>(newtree: Node)
  requires newtree.Leaf?
  requires CSMap.Keyspace.IsStrictlySorted(newtree.keys)
  ensures CantEquivocate(newtree);
  {
    forall k, value, value', lookup: Lookup<Value>, lookup': Lookup<Value> |
      && IsSatisfyingLookup(newtree, k, value, lookup)
      && IsSatisfyingLookup(newtree, k, value', lookup')
      ensures value == value'
    {
      assert CSMap.Keyspace.IsStrictlySorted(newtree.keys);
      assert CSMap.Keyspace.IsSorted(newtree.keys);
      valueEqValue(newtree, k, value, value', lookup, lookup');
    }
    assert CantEquivocate(newtree);
  }

  lemma leafPreservesLookupsExcept<Value>(tree:Node, newtree:Node, key:Key, value:Value, pos:int)
  requires WFTree(tree);
  requires WFTree(newtree);
  requires tree.Leaf?
  requires newtree.Leaf?
  requires pos == CSMap.Keyspace.LargestLte(tree.keys, key);
  requires pos < 0 || key != tree.keys[pos];
  requires newtree.keys == insert(tree.keys, key, pos+1);
  requires newtree.values == insert(tree.values, value, pos+1);
  ensures PreservesLookupsExcept(tree, newtree, key);
  {
    forall lookup: Lookup, key', value'
      | key' != key && IsSatisfyingLookup(tree, key', value', lookup)
      ensures exists lookup' :: IsSatisfyingLookup(newtree, key', value', lookup');
    {
      if lookup[0].slot < pos+1 {
        var lookup' := [Layer(newtree, lookup[0].slot)];
        assert IsSatisfyingLookup(newtree, key', value', lookup');
      } else {
        var lookup' := [Layer(newtree, lookup[0].slot + 1)];
        assert newtree.keys[lookup[0].slot + 1]
            == tree.keys[lookup[0].slot]
            == key';
        assert IsSatisfyingLookup(newtree, key', value', lookup');
      }
    }
  }

  lemma keysRemainBetweenLbAndUb(newkeys: seq<Key>, lb: Key, ub: Key, keys: seq<Key>, key: Key, pos: int)
  requires 0 <= pos <= |keys|
  requires newkeys == insert(keys, key, pos);
  requires CSMap.Keyspace.lte(lb, key);
  requires CSMap.Keyspace.lt(key, ub);
  requires && (forall i :: 0 <= i < |keys| ==>
           && CSMap.Keyspace.lte(lb, keys[i])
           && CSMap.Keyspace.lt(keys[i], ub));
  ensures && (forall i :: 0 <= i < |newkeys| ==>
          && CSMap.Keyspace.lte(lb, newkeys[i])
          && CSMap.Keyspace.lt(newkeys[i], ub));
  {
    reveal_insert();
  }

  lemma PutIsCorrect<Value>(tree: Node, newtree: Node, key: Key, value: Value)
  requires WFTree(tree)
  requires CantEquivocate(tree)
  requires PutTransform(tree, newtree, key, value);
  ensures PreservesLookupsExcept(tree, newtree, key);
  ensures PreservesLookupsExcept(newtree, tree, key);
  ensures exists lookup :: IsSatisfyingLookup(newtree, key, value, lookup);
  ensures CantEquivocate(newtree)
  decreases tree
  {
    if tree.Leaf? {
      var pos := CSMap.Keyspace.LargestLte(tree.keys, key);
      if pos >= 0 && key == tree.keys[pos] {
        assert newtree == Leaf(tree.keys, tree.values[pos := value], tree.lb, tree.ub);
        
        forall lookup: Lookup, key', value'
          | key' != key && IsSatisfyingLookup(tree, key', value', lookup)
          ensures exists lookup' :: IsSatisfyingLookup(newtree, key', value', lookup');
        {
          var lookup' := [Layer(newtree, lookup[0].slot)];
          assert IsSatisfyingLookup(newtree, key', value', lookup');
        }
        forall lookup': Lookup, key', value'
          | key' != key && IsSatisfyingLookup(newtree, key', value', lookup')
          ensures exists lookup :: IsSatisfyingLookup(tree, key', value', lookup);
        {
          var lookup := [Layer(tree, lookup'[0].slot)];
          assert IsSatisfyingLookup(tree, key', value', lookup);
        }

        assert IsSatisfyingLookup(newtree, key, value, [Layer(newtree, pos)]);
        leafCantEquivocate(newtree);

      } else {
        var newkeys := insert(tree.keys, key, pos+1);
        var newvals := insert(tree.values, value, pos+1);
        assert newtree == Leaf(newkeys, newvals, tree.lb, tree.ub);
        //assert CSMap.Keyspace.IsSorted(newtree.keys);
        var lookup := [Layer(newtree, pos + 1)];

        CSMap.Keyspace.strictlySortedInsert(tree.keys, key, pos);
        keysRemainBetweenLbAndUb(newkeys, newtree.lb, newtree.ub, tree.keys, key, pos+1);
        assert WFTree(newtree);
        assert IsSatisfyingLookup(newtree, key, value, lookup);

        leafPreservesLookupsExcept(tree, newtree, key, value, pos);

        forall lookup': Lookup, key', value'
          | key' != key && IsSatisfyingLookup(newtree, key', value', lookup')
          ensures exists lookup :: IsSatisfyingLookup(tree, key', value', lookup);
        {
          assert lookup'[0].slot != pos+1;
          if lookup'[0].slot <= pos {
            var lookup := [Layer(tree, lookup'[0].slot)];
            assert IsSatisfyingLookup(tree, key', value', lookup);
          } else {
            var lookup := [Layer(tree, lookup'[0].slot - 1)];
            assert IsSatisfyingLookup(tree, key', value', lookup);
          }
        }

        leafCantEquivocate(newtree);

      }
    } else {
      var pos := CSMap.Keyspace.LargestLte(tree.pivots, key) + 1;

      // Before we can call Define recursively, we must prove that the child CantEquivocate.
      forall key', valueA, valueB, lookup, lookup'
      |
      && IsSatisfyingLookup(tree.children[pos], key', valueA, lookup)
      && IsSatisfyingLookup(tree.children[pos], key', valueB, lookup')
      ensures valueA == valueB;
      {
        var plookup  := [Layer(tree, pos)] + lookup;
        var plookup' := [Layer(tree, pos)] + lookup';
        assert IsSatisfyingLookup(tree, key', valueA, plookup);
        assert IsSatisfyingLookup(tree, key', valueB, plookup');
      }
      var newchild := newtree.children[pos];
      PutIsCorrect(tree.children[pos], newchild, key, value);
      assert PutTransform(tree.children[pos], newchild, key, value);
      assert newtree == Index(tree.pivots, tree.children[pos := newchild], tree.lb, tree.ub);

      // PreservesLookupsExcept proofs
      forall lookup: Lookup, key', value'
        | key' != key && IsSatisfyingLookup(tree, key', value', lookup)
        ensures exists lookup' :: IsSatisfyingLookup(newtree, key', value', lookup');
      {
        var clookup := lookup[1..];
        assert IsSatisfyingLookup(tree.children[lookup[0].slot], key', value', clookup);
        var clookup' :| IsSatisfyingLookup(newtree.children[lookup[0].slot], key', value', clookup');
        var lookup' := [Layer(newtree, lookup[0].slot)] + clookup';
        assert IsSatisfyingLookup(newtree, key', value', lookup');
      }
      forall lookup': Lookup, key', value'
        | key' != key && IsSatisfyingLookup(newtree, key', value', lookup')
        ensures exists lookup :: IsSatisfyingLookup(tree, key', value', lookup);
      {
        var clookup' := lookup'[1..];
        assert IsSatisfyingLookup(newtree.children[lookup'[0].slot], key', value', clookup');
        var clookup: Lookup<Value> :| IsSatisfyingLookup(tree.children[lookup'[0].slot], key', value', clookup);
        var lookup := [Layer(tree, lookup'[0].slot)] + clookup;
        assert IsSatisfyingLookup(tree, key', value', lookup);
      }

      // Proof that we can lookup key and get value
      ghost var clookup :| IsSatisfyingLookup(newtree.children[pos], key, value, clookup);
      ghost var lookup := [Layer(newtree, pos)] + clookup;
      assert IsSatisfyingLookup(newtree, key, value, lookup);

      // Proof that we CantEquivocate
      forall key', valueA, valueB, lookupA: Lookup, lookupB: Lookup
      |
      && IsSatisfyingLookup(newtree, key', valueA, lookupA)
      && IsSatisfyingLookup(newtree, key', valueB, lookupB)
      ensures valueA == valueB;
      {
        SatisfyingLookupSlotIsLargestLte(newtree, key', valueA, lookupA);
        SatisfyingLookupSlotIsLargestLte(newtree, key', valueB, lookupB);
        SatisfyingLookupsNest(newtree, key', valueA, lookupA);
        SatisfyingLookupsNest(newtree, key', valueB, lookupB);
      }
      assert CantEquivocate(newtree);
    }
  }

  // TODO move these to total_order.dfy
  lemma strictlySortedImplLt(l: seq<Key>, a: int, b: int)
  requires 0 <= a;
  requires a < b;
  requires b < |l|;
  requires CSMap.Keyspace.IsStrictlySorted(l);
  ensures CSMap.Keyspace.lt(l[a], l[b]);
  {
    CSMap.Keyspace.reveal_IsStrictlySorted();
  }

  lemma strictlySortedSplit(l: seq<Key>, p: int)
  requires 0 <= p <= |l|
  requires CSMap.Keyspace.IsStrictlySorted(l);
  ensures CSMap.Keyspace.IsStrictlySorted(l[..p]);
  ensures CSMap.Keyspace.IsStrictlySorted(l[p..]);
  {
    CSMap.Keyspace.reveal_IsStrictlySorted();
  }

  lemma GrowLeafIsCorrect<Value>(tree: Node, newtree: Node, childrenToLeft: int)
  requires WFRoot(tree);
  requires CantEquivocate(tree);
  requires tree.Leaf?
  requires GrowLeaf(tree, newtree, childrenToLeft);
  ensures WFTree(newtree);
  ensures PreservesLookups(tree, newtree);
  ensures PreservesLookups(newtree, tree);
  ensures CantEquivocate(newtree);
  decreases tree;
  {
    var left_child := newtree.children[0];
    var right_child := newtree.children[1];

    strictlySortedSplit(tree.keys, childrenToLeft);

    forall i | 0 <= i < |left_child.keys|
      ensures
      && CSMap.Keyspace.lte(left_child.lb, left_child.keys[i])
      && CSMap.Keyspace.lt(left_child.keys[i], left_child.ub)
    {
      assert left_child.keys[i] == tree.keys[i];
      assert left_child.ub == tree.keys[childrenToLeft];
      assert i < childrenToLeft;
      strictlySortedImplLt(tree.keys, i, childrenToLeft);
    }

    forall i | 0 <= i < |right_child.keys|
      ensures
      && CSMap.Keyspace.lte(right_child.lb, right_child.keys[i])
      && CSMap.Keyspace.lt(right_child.keys[i], right_child.ub)
    {
      if (i == 0) {
      } else {
        assert right_child.keys[i] == tree.keys[i + childrenToLeft];
        assert right_child.lb == tree.keys[childrenToLeft];
        strictlySortedImplLt(tree.keys, childrenToLeft, i + childrenToLeft);
      }
    }

    assert WFTree(left_child);
    assert WFTree(right_child);

    CSMap.Keyspace.transitivity_le_lt(newtree.lb, tree.keys[0], newtree.pivots[0]);

    assert CSMap.Keyspace.lt(newtree.lb, newtree.pivots[0]);
    assert CSMap.Keyspace.lt(newtree.pivots[0], newtree.ub);

    assert WFTree(newtree);

    forall lookup:Lookup<Value>, key, value' | IsSatisfyingLookup(tree, key, value', lookup)
    ensures exists lookup' :: IsSatisfyingLookup(newtree, key, value', lookup')
    {
      var original_top_layer := lookup[0];
      if (original_top_layer.slot < childrenToLeft) {
        var layer1 := Layer(newtree, 0);
        var layer2 := Layer(left_child, original_top_layer.slot);
        var lookup' := [layer1, layer2];
        assert WFTree(layer1.node);
        assert WFTree(layer2.node);
        assert IsSatisfyingLookup(newtree, key, value', lookup');
      } else {
        var layer1 := Layer(newtree, 1);
        var layer2 := Layer(right_child, original_top_layer.slot - childrenToLeft);
        var lookup' := [layer1, layer2] + lookup[1 .. ];
        assert WFTree(layer1.node);
        assert WFTree(layer2.node);
        assert IsSatisfyingLookup(newtree, key, value', lookup');
      }
    }

    forall lookup:Lookup<Value>, key, value' | IsSatisfyingLookup(newtree, key, value', lookup)
    ensures exists lookup' :: IsSatisfyingLookup(tree, key, value', lookup')
    {
      var layer1 := lookup[0];
      var layer2 := lookup[1];
      if (layer1.slot == 0) {
        var layer := Layer(tree, layer2.slot);
        var lookup' := [layer] + lookup[2 .. ];
        assert IsSatisfyingLookup(tree, key, value', lookup');
      } else {
        assert layer1.slot == 1;
        var layer := Layer(tree, layer2.slot + childrenToLeft);
        var lookup' := [layer] + lookup[2 .. ];
        assert IsSatisfyingLookup(tree, key, value', lookup');
      }
    }
  }

  lemma GrowIndexIsCorrect<Value>(tree: Node, newtree: Node, childrenToLeft: int)
  requires WFTree(tree);
  requires CantEquivocate(tree);
  requires tree.Index?
  requires GrowIndex(tree, newtree, childrenToLeft);
  ensures WFTree(newtree);
  ensures PreservesLookups(tree, newtree);
  ensures PreservesLookups(newtree, tree);
  ensures CantEquivocate(newtree);
  decreases tree;
  {
    var left_child := newtree.children[0];
    var right_child := newtree.children[1];

    forall i | 0 <= i < |left_child.pivots|
      ensures
      && CSMap.Keyspace.lt(left_child.lb, left_child.pivots[i])
      && CSMap.Keyspace.lt(left_child.pivots[i], left_child.ub)
    {
      assert left_child.pivots[i] == tree.pivots[i];
      assert left_child.ub == tree.pivots[childrenToLeft - 1];
      assert i < childrenToLeft - 1;
      strictlySortedImplLt(tree.pivots, i, childrenToLeft - 1);
    }

    forall i | 0 <= i < |right_child.pivots|
      ensures
      && CSMap.Keyspace.lt(right_child.lb, right_child.pivots[i])
      && CSMap.Keyspace.lt(right_child.pivots[i], right_child.ub)
      && right_child.pivots[i] == right_child.children[i].ub
      && right_child.pivots[i] == right_child.children[i+1].lb
    {
      assert right_child.pivots[i] == tree.pivots[i + childrenToLeft];
      assert right_child.lb == tree.pivots[childrenToLeft - 1];
      assert childrenToLeft - 1 < i + childrenToLeft;
      strictlySortedImplLt(tree.pivots, childrenToLeft - 1, i + childrenToLeft);
    }

    strictlySortedSplit(tree.pivots, childrenToLeft - 1);
    strictlySortedSplit(tree.pivots, childrenToLeft);

    assert WFTree(left_child);

    assert right_child.lb == right_child.children[0].lb;
    assert WFTree(right_child);

    assert newtree.children == [left_child, right_child];

    forall lookup:Lookup<Value>, key, value' | IsSatisfyingLookup(tree, key, value', lookup)
    ensures exists lookup' :: IsSatisfyingLookup(newtree, key, value', lookup')
    {
      var original_top_layer := lookup[0];
      if (original_top_layer.slot < childrenToLeft) {
        var layer1 := Layer(newtree, 0);
        var layer2 := Layer(left_child, original_top_layer.slot);
        var lookup' := [layer1, layer2] + lookup[1 .. ];
        assert WFTree(layer1.node);
        assert WFTree(layer2.node);
        assert IsSatisfyingLookup(newtree, key, value', lookup');
      } else {
        var layer1 := Layer(newtree, 1);
        var layer2 := Layer(right_child, original_top_layer.slot - childrenToLeft);
        var lookup' := [layer1, layer2] + lookup[1 .. ];
        assert WFTree(layer1.node);
        assert WFTree(layer2.node);
        assert IsSatisfyingLookup(newtree, key, value', lookup');
      }
    }

    forall lookup:Lookup<Value>, key, value' | IsSatisfyingLookup(newtree, key, value', lookup)
    ensures exists lookup' :: IsSatisfyingLookup(tree, key, value', lookup')
    {
      var layer1 := lookup[0];
      var layer2 := lookup[1];
      if (layer1.slot == 0) {
        var layer := Layer(tree, layer2.slot);
        var lookup' := [layer] + lookup[2 .. ];
        assert IsSatisfyingLookup(tree, key, value', lookup');
      } else {
        assert layer1.slot == 1;
        var layer := Layer(tree, layer2.slot + childrenToLeft);
        var lookup' := [layer] + lookup[2 .. ];
        assert IsSatisfyingLookup(tree, key, value', lookup');
      }
    }
  }

  lemma PutPreservesInvariant<Value>(k: Constants, s: Variables, s': Variables, key: Key, value: Value)
  requires Invariant(k, s);
  requires Put(k, s, s', key, value);
  ensures Invariant(k, s');
  {
    if (s.root.Leaf? && |s.root.keys| == 0) {
      assert WFTree(s'.root);
      assert Invariant(k, s');
    } else {
      assert WFTree(s.root);
      PutIsCorrect(s.root, s'.root, key, value);
    }
  }

  lemma GrowPreservesInvariant<Value>(k: Constants, s: Variables, s': Variables, childrenToLeft: int)
  requires Invariant(k, s);
  requires Grow(k, s, s', childrenToLeft);
  ensures Invariant(k, s');
  {
    if (s.root.Leaf?) {
      GrowLeafIsCorrect(s.root, s'.root, childrenToLeft);
    } else {
      GrowIndexIsCorrect(s.root, s'.root, childrenToLeft);
    }
  }

  lemma pivotsAreCorrectAfterSplit(tree: Node, newtree: Node, l: Key, u: Key, childrenToLeft: int, pos: int)
  requires WFTree(tree);
  requires SplitTransform(tree, newtree, l, u, childrenToLeft);
  requires pos == CSMap.Keyspace.LargestLte(tree.pivots, l) + 1;
  requires 0 <= pos < |tree.children|;
  requires tree.children[pos].lb == l;
  requires tree.children[pos].ub == u;
  ensures CSMap.Keyspace.IsStrictlySorted(newtree.pivots);
  {
    var child := tree.children[pos];
    assert |newtree.children| == |tree.children| + 1;
    var left_child := newtree.children[pos];
    var right_child := newtree.children[pos+1];
    assert WFTree(child);
    if (pos < |tree.pivots|) {
      if (child.Leaf?) {
        assert newtree.pivots[pos]
            == right_child.keys[0]
            == child.keys[childrenToLeft];
        assert CSMap.Keyspace.lt(child.keys[childrenToLeft], child.ub);
      } else {
        assert newtree.pivots[pos] == child.pivots[childrenToLeft-1];
        assert CSMap.Keyspace.lt(child.pivots[childrenToLeft-1], child.ub);
      }
      assert child.ub == tree.pivots[pos];
      assert CSMap.Keyspace.lt(newtree.pivots[pos], tree.pivots[pos]);
    }
    if (pos > 0) {
      if (child.Leaf?) {
        assert CSMap.Keyspace.lte(child.lb, child.keys[0]);
        CSMap.Keyspace.reveal_IsStrictlySorted();
        assert CSMap.Keyspace.lt(child.keys[0], child.keys[childrenToLeft]);
        assert CSMap.Keyspace.lt(child.lb, child.keys[childrenToLeft]);
      } else {
        assert CSMap.Keyspace.lt(child.lb, child.pivots[childrenToLeft-1]);
      }
      assert child.lb == tree.pivots[pos-1];
      assert CSMap.Keyspace.lt(tree.pivots[pos-1], newtree.pivots[pos]);
    }
    CSMap.Keyspace.strictlySortedInsert2(tree.pivots, newtree.pivots[pos], pos);
  }

  lemma pivotsAreBoundedAfterSplit(tree: Node, newtree: Node, l: Key, u: Key, childrenToLeft: int, pos: int)
  requires WFTree(tree);
  requires SplitTransform(tree, newtree, l, u, childrenToLeft);
  requires pos == CSMap.Keyspace.LargestLte(tree.pivots, l) + 1;
  requires 0 <= pos < |tree.children|;
  requires tree.children[pos].lb == l;
  requires tree.children[pos].ub == u;
  requires CSMap.Keyspace.IsStrictlySorted(newtree.pivots);
  ensures (forall i :: 0 <= i < |newtree.pivots| ==>
      && CSMap.Keyspace.lt(newtree.lb, newtree.pivots[i])
      && CSMap.Keyspace.lt(newtree.pivots[i], newtree.ub))
  {
    forall i | 0 <= i < |newtree.pivots|
    ensures CSMap.Keyspace.lt(newtree.lb, newtree.pivots[i])
    ensures CSMap.Keyspace.lt(newtree.pivots[i], newtree.ub)
    {
      if (i < pos) {
        assert newtree.pivots[i] == tree.pivots[i];
        assert CSMap.Keyspace.lt(newtree.lb, newtree.pivots[i]);
        assert CSMap.Keyspace.lt(newtree.pivots[i], newtree.ub);
      } else if (i == pos) {
        var child := tree.children[pos];
        var left_child := newtree.children[pos];
        var right_child := newtree.children[pos+1];
        if (tree.children[pos].Leaf?) {
          assert CSMap.Keyspace.lte(newtree.lb, child.lb);
          assert WFTree(child);
          assert CSMap.Keyspace.lte(child.lb, child.keys[0]);
          CSMap.Keyspace.reveal_IsStrictlySorted();
          assert 0 < |left_child.keys|;
          assert CSMap.Keyspace.lt(child.keys[0], child.keys[|left_child.keys|]);
          assert child.keys[|left_child.keys|] == right_child.keys[0];
          assert right_child.keys[0] == newtree.pivots[i];

          assert CSMap.Keyspace.lt(right_child.keys[0], newtree.ub);

          assert CSMap.Keyspace.lt(newtree.lb, newtree.pivots[i]);
          assert CSMap.Keyspace.lt(newtree.pivots[i], newtree.ub);
        } else {
          assert CSMap.Keyspace.lte(newtree.lb, child.lb);
          assert WFTree(child);
          assert CSMap.Keyspace.lte(child.lb, child.pivots[0]);
          assert 0 < childrenToLeft;
          CSMap.Keyspace.reveal_IsStrictlySorted();
          assert CSMap.Keyspace.lt(child.pivots[0], child.pivots[childrenToLeft]);

          assert CSMap.Keyspace.lt(child.pivots[childrenToLeft], child.ub);
          assert CSMap.Keyspace.lte(child.ub, newtree.ub);

          assert CSMap.Keyspace.lt(newtree.lb, child.pivots[childrenToLeft]);
          assert CSMap.Keyspace.lt(child.pivots[childrenToLeft], newtree.ub);

          assert CSMap.Keyspace.lt(newtree.lb, newtree.pivots[i]);
          assert CSMap.Keyspace.lt(newtree.pivots[i], newtree.ub);
        }
      } else {
        assert newtree.pivots[i] == tree.pivots[i - 1];
        assert CSMap.Keyspace.lt(newtree.lb, newtree.pivots[i]);
        assert CSMap.Keyspace.lt(newtree.pivots[i], newtree.ub);
      }
    }
  }

  lemma keysSortedOfSplitChildren(tree: Node, tree_left: Node, pivot: Key, tree_right: Node, childrenToLeft: int)
  requires WFTree(tree);
  requires tree.Leaf?;
  requires IsSplit(tree, tree_left, pivot, tree_right, childrenToLeft);
  ensures CSMap.Keyspace.IsStrictlySorted(tree_left.keys);
  ensures CSMap.Keyspace.IsStrictlySorted(tree_right.keys);
  ensures (forall i :: 0 <= i < |tree_left.keys| ==> && CSMap.Keyspace.lte(tree_left.lb, tree_left.keys[i]))
  ensures (forall i :: 0 <= i < |tree_left.keys| ==> && CSMap.Keyspace.lt(tree_left.keys[i], tree_left.ub))
  ensures (forall i :: 0 <= i < |tree_right.keys| ==> && CSMap.Keyspace.lte(tree_right.lb, tree_right.keys[i]))
  ensures (forall i :: 0 <= i < |tree_right.keys| ==> && CSMap.Keyspace.lt(tree_right.keys[i], tree_right.ub))
  {
    CSMap.Keyspace.reveal_IsStrictlySorted();
    forall i, j | 0 <= i < j < |tree_left.keys|
    ensures CSMap.Keyspace.lt(tree_left.keys[i], tree_left.keys[j])
    {
      assert tree_left.keys[i] == tree.keys[i];
      assert tree_left.keys[j] == tree.keys[j];
    }
    forall i, j | 0 <= i < j < |tree_right.keys|
    ensures CSMap.Keyspace.lt(tree_right.keys[i], tree_right.keys[j])
    {
      assert tree_right.keys[i] == tree.keys[i + |tree_left.keys|];
      assert tree_right.keys[j] == tree.keys[j + |tree_left.keys|];
    }

    forall i | 0 <= i < |tree_left.keys|
    ensures CSMap.Keyspace.lte(tree_left.lb, tree_left.keys[i])
    ensures CSMap.Keyspace.lt(tree_left.keys[i], tree_left.ub)
    {
      assert tree_left.keys[i] == tree.keys[i];
      assert CSMap.Keyspace.lt(tree.keys[i], tree.keys[|tree_left.keys|]);
      assert tree_left.ub == tree.keys[|tree_left.keys|];
    }

    forall i | 0 <= i < |tree_right.keys|
    ensures CSMap.Keyspace.lte(tree_right.lb, tree_right.keys[i])
    ensures CSMap.Keyspace.lt(tree_right.keys[i], tree_right.ub)
    {
      assert tree_right.keys[i] == tree.keys[i + |tree_left.keys|];
    }
  }

  lemma pivotsSortedOfSplitChildren(tree: Node, tree_left: Node, pivot: Key, tree_right: Node, childrenToLeft: int)
  requires WFTree(tree);
  requires tree.Index?;
  requires IsSplit(tree, tree_left, pivot, tree_right, childrenToLeft);
  ensures CSMap.Keyspace.IsStrictlySorted(tree_left.pivots);
  ensures CSMap.Keyspace.IsStrictlySorted(tree_right.pivots);
  ensures (forall i :: 0 <= i < |tree_left.pivots| ==> && CSMap.Keyspace.lt(tree_left.lb, tree_left.pivots[i]))
  ensures (forall i :: 0 <= i < |tree_left.pivots| ==> && CSMap.Keyspace.lt(tree_left.pivots[i], tree_left.ub))
  ensures (forall i :: 0 <= i < |tree_right.pivots| ==> && CSMap.Keyspace.lt(tree_right.lb, tree_right.pivots[i]))
  ensures (forall i :: 0 <= i < |tree_right.pivots| ==> && CSMap.Keyspace.lt(tree_right.pivots[i], tree_right.ub))
  {
    CSMap.Keyspace.reveal_IsStrictlySorted();
    forall i, j | 0 <= i < j < |tree_left.pivots|
    ensures CSMap.Keyspace.lt(tree_left.pivots[i], tree_left.pivots[j])
    {
      assert tree_left.pivots[i] == tree.pivots[i];
      assert tree_left.pivots[j] == tree.pivots[j];
    }
    forall i, j | 0 <= i < j < |tree_right.pivots|
    ensures CSMap.Keyspace.lt(tree_right.pivots[i], tree_right.pivots[j])
    {
      assert tree_right.pivots[i] == tree.pivots[i + |tree_left.pivots| + 1];
      assert tree_right.pivots[j] == tree.pivots[j + |tree_left.pivots| + 1];
    }

    forall i | 0 <= i < |tree_left.pivots|
    ensures CSMap.Keyspace.lt(tree_left.lb, tree_left.pivots[i])
    ensures CSMap.Keyspace.lt(tree_left.pivots[i], tree_left.ub)
    {
      assert tree_left.pivots[i] == tree.pivots[i];
    }

    forall i | 0 <= i < |tree_right.pivots|
    ensures CSMap.Keyspace.lt(tree_right.lb, tree_right.pivots[i])
    ensures CSMap.Keyspace.lt(tree_right.pivots[i], tree_right.ub)
    {
      assert tree_right.pivots[i] == tree.pivots[i + |tree_left.pivots| + 1];
    }
  }

  lemma SplitImpliesPreservesLookups(tree: Node, newtree: Node, l: Key, u: Key, childrenToLeft: int, pos: int)
  requires WFTree(tree)
  requires WFTree(newtree)
  requires SplitTransform(tree, newtree, l, u, childrenToLeft);
  requires pos == CSMap.Keyspace.LargestLte(tree.pivots, l) + 1;
  requires tree.children[pos].lb == l && tree.children[pos].ub == u
  ensures PreservesLookups(tree, newtree)
  {
    var pos := CSMap.Keyspace.LargestLte(tree.pivots, l) + 1;
    forall lookup:Lookup, key:Key, value | IsSatisfyingLookup(tree, key, value, lookup)
    ensures exists lookup' :: IsSatisfyingLookup(newtree, key, value, lookup')
    {
      var slot := lookup[0].slot;
      if (slot < pos) {
        var lookup' := [Layer(newtree, slot)] + lookup[1..];
        assert IsSatisfyingLookup(newtree, key, value, lookup');
      }
      else if (slot == pos) {
        var slot2 := lookup[1].slot;
        if (slot2 < childrenToLeft) {
          var lookup' := [
              Layer(newtree, slot),
              Layer(newtree.children[slot], slot2)] +
              lookup[2..];
          assert IsSatisfyingLookup(newtree, key, value, lookup');
        } else {
          var lookup' := [
              Layer(newtree, slot+1),
              Layer(newtree.children[slot+1], slot2 - childrenToLeft)] +
              lookup[2..];
          assert IsSatisfyingLookup(newtree, key, value, lookup');
        }
      }
      else {
        var lookup' := [Layer(newtree, slot+1)] + lookup[1..];
        assert slot < |tree.children|;
        assert slot+1 < |newtree.children|;
        assert 0 <= lookup'[0].slot < |lookup'[0].node.children|;
        assert IsSatisfyingLookup(newtree, key, value, lookup');
      }
    }
  }

  lemma SplitImpliesPreservesLookupsRev(tree: Node, newtree: Node, l: Key, u: Key, childrenToLeft: int, pos: int)
  requires WFTree(tree)
  requires WFTree(newtree)
  requires SplitTransform(tree, newtree, l, u, childrenToLeft);
  requires pos == CSMap.Keyspace.LargestLte(tree.pivots, l) + 1;
  requires tree.children[pos].lb == l && tree.children[pos].ub == u
  ensures PreservesLookups(newtree, tree)
  {
    var pos := CSMap.Keyspace.LargestLte(tree.pivots, l) + 1;
    forall lookup:Lookup, key:Key, value | IsSatisfyingLookup(newtree, key, value, lookup)
    ensures exists lookup' :: IsSatisfyingLookup(tree, key, value, lookup')
    {
      var slot := lookup[0].slot;
      if (slot < pos) {
        var lookup' := [Layer(tree, slot)] + lookup[1..];
        assert IsSatisfyingLookup(tree, key, value, lookup');
      }
      else if (slot == pos) {
        var slot2 := lookup[1].slot;
        var lookup' := [
            Layer(tree, slot),
            Layer(tree.children[slot], slot2)] +
            lookup[2..];
        assert IsSatisfyingLookup(tree, key, value, lookup');
      } else if (slot == pos + 1) {
        var slot2 := lookup[1].slot;
        var lookup' := [
            Layer(tree, pos),
            Layer(tree.children[pos], slot2 + childrenToLeft)] +
            lookup[2..];
        assert IsSatisfyingLookup(tree, key, value, lookup');
      } else {
        var lookup' := [Layer(tree, slot-1)] + lookup[1..];
        assert lookup'[1].node
            == newtree.children[slot]
            == tree.children[slot-1];
        assert lookup'[0].node.children[lookup'[0].slot] == tree.children[slot-1];
        assert lookup'[1].node == lookup'[0].node.children[lookup'[0].slot];
        assert IsSatisfyingLookup(tree, key, value, lookup');
      }
    }
  }

  lemma PreservesLookupsImplCantEquivocate<Value>(tree: Node, newtree: Node)
  requires WFTree(tree)
  requires WFTree(newtree)
  requires CantEquivocate(tree)
  requires PreservesLookups(newtree, tree)
  ensures CantEquivocate(newtree)
  {
    forall key, value, value', lookup: Lookup<Value>, lookup': Lookup<Value> |
      && IsSatisfyingLookup(newtree, key, value, lookup)
      && IsSatisfyingLookup(newtree, key, value', lookup')
    ensures
      value == value'
    {
      var plookup :| IsSatisfyingLookup(tree, key, value, plookup); // from PreservesLookup
      var plookup' :| IsSatisfyingLookup(tree, key, value', plookup'); // from PreservesLookup
      assert value == value'; // comes from CantEquivocate(tree)
    }
  }

  lemma SplitIsCorrect<Value>(tree: Node, newtree: Node, l: Key, u: Key, childrenToLeft: int)
  requires WFTree(tree);
  requires CantEquivocate(tree);
  requires SplitTransform(tree, newtree, l, u, childrenToLeft);
  ensures WFTree(newtree);
  ensures PreservesLookups(tree, newtree);
  ensures PreservesLookups(newtree, tree);
  ensures CantEquivocate(newtree);
  decreases tree;
  {
    var pos := CSMap.Keyspace.LargestLte(tree.pivots, l) + 1;
    var child := tree.children[pos];
    if (child.lb == l && child.ub == u) {
      var left_child := newtree.children[pos];
      var right_child := newtree.children[pos+1];

      if (child.Leaf?) {
        keysSortedOfSplitChildren(child, left_child, newtree.pivots[pos], right_child, childrenToLeft);
      } else {
        pivotsSortedOfSplitChildren(child, left_child, newtree.pivots[pos], right_child, childrenToLeft);
      }

      assert WFTree(left_child);
      assert WFTree(right_child);

      pivotsAreCorrectAfterSplit(tree, newtree, l, u, childrenToLeft, pos);
      pivotsAreBoundedAfterSplit(tree, newtree, l, u, childrenToLeft, pos);

      forall i | 0 <= i < |newtree.children|
      ensures WFTree(newtree.children[i])
      {
        if (i < pos) {
          assert newtree.children[i] == tree.children[i];
          assert WFTree(tree.children[i]);
        } else if (i == pos) {
          assert newtree.children[i] == left_child;
        } else if (i == pos + 1) {
          assert newtree.children[i] == right_child;
        } else {
          assert 0 <= i-1 < |tree.children| ==> WFTree(tree.children[i-1]);
          assert 0 <= i-1 < |tree.children|; // this seems to help proof time a ton
          assert WFTree(tree.children[i-1]);
          assert newtree.children[i] == tree.children[i-1];
        }
      }

      forall i | 0 <= i < |newtree.pivots|
      ensures newtree.pivots[i] == newtree.children[i].ub
      {
        if (i < pos) {
          assert newtree.children[i] == tree.children[i];
          assert WFTree(tree.children[i]);
          assert tree.pivots[i] == tree.children[i].ub;
        } else if (i == pos) {
          assert newtree.children[i] == left_child;
          assert left_child.ub == newtree.pivots[i];
        } else if (i == pos+1) {
          assert newtree.children[i] == right_child;
          assert right_child.ub == newtree.pivots[i];
        } else {
          assert 0 <= i-1 < |tree.children| ==> WFTree(tree.children[i-1]);
          assert 0 <= i-1 < |tree.children|; // this seems to help proof time a ton
          assert WFTree(tree.children[i-1]);
          assert newtree.children[i] == tree.children[i-1];
          assert tree.pivots[i-1] == tree.children[i-1].ub;
        }
      }

      forall i | 0 <= i < |newtree.pivots|
      ensures newtree.pivots[i] == newtree.children[i+1].lb
      {
        if (i < pos-1) {
          assert 0 <= i+1 < |tree.children| ==> WFTree(tree.children[i+1]);
          assert 0 <= i+1 < |tree.children|; // this seems to help proof time a ton
          assert WFTree(tree.children[i+1]);
          assert newtree.children[i+1] == tree.children[i+1];
          assert tree.pivots[i] == tree.children[i+1].lb;
          assert 0 <= i < |tree.pivots|;
          assert newtree.pivots[i] == tree.pivots[i];
        } else if (i == pos-1) {
          assert newtree.children[i+1] == left_child;
          assert left_child.lb == newtree.pivots[i];
        } else if (i == pos) {
          assert newtree.children[i+1] == right_child;
          assert right_child.lb == newtree.pivots[i];
        } else {
          assert WFTree(tree.children[i]);
          assert newtree.children[i+1] == tree.children[i];
          assert newtree.children[i+1].lb == tree.children[i].lb
              == tree.pivots[i-1]
              == newtree.pivots[i];
        }
      }

      assert WFTree(newtree);

      /*assert PreservesLookups(tree, newtree);
      assert PreservesLookups(newtree, tree);
      assert CantEquivocate(newtree);*/
      SplitImpliesPreservesLookups(tree, newtree, l, u, childrenToLeft, pos);
      SplitImpliesPreservesLookupsRev(tree, newtree, l, u, childrenToLeft, pos);
      PreservesLookupsImplCantEquivocate(tree, newtree);
    } else {
      // Before we can call Define recursively, we must prove that the child CantEquivocate.
      forall key', valueA, valueB, lookup, lookup'
      |
      && IsSatisfyingLookup(tree.children[pos], key', valueA, lookup)
      && IsSatisfyingLookup(tree.children[pos], key', valueB, lookup')
      ensures valueA == valueB;
      {
        var plookup  := [Layer(tree, pos)] + lookup;
        var plookup' := [Layer(tree, pos)] + lookup';
        assert IsSatisfyingLookup(tree, key', valueA, plookup);
        assert IsSatisfyingLookup(tree, key', valueB, plookup');
      }
      var newchild := newtree.children[pos];

      SplitIsCorrect(tree.children[pos], newchild, l, u, childrenToLeft);

      assert newtree == Index(tree.pivots, tree.children[pos := newchild], tree.lb, tree.ub);

      // Proof that PreservesLookups
      forall lookup:Lookup, key:Key, value:Value | IsSatisfyingLookup(tree, key, value, lookup)
      ensures exists lookup' :: IsSatisfyingLookup(newtree, key, value, lookup')
      {
        var clookup := lookup[1..];
        assert IsSatisfyingLookup(tree.children[lookup[0].slot], key, value, clookup);
        var clookup' :| IsSatisfyingLookup(newtree.children[lookup[0].slot], key, value, clookup');
        var lookup' := [Layer(newtree, lookup[0].slot)] + clookup';
        assert IsSatisfyingLookup(newtree, key, value, lookup');
      }

      forall lookup':Lookup, key:Key, value:Value | IsSatisfyingLookup(newtree, key, value, lookup')
      ensures exists lookup' :: IsSatisfyingLookup(tree, key, value, lookup')
      {
        var clookup' := lookup'[1..];
        assert IsSatisfyingLookup(newtree.children[lookup'[0].slot], key, value, clookup');
        var clookup: Lookup<Value> :| IsSatisfyingLookup(tree.children[lookup'[0].slot], key, value, clookup);
        var lookup := [Layer(tree, lookup'[0].slot)] + clookup;
        assert IsSatisfyingLookup(tree, key, value, lookup);
      }

      // Proof that we CantEquivocate
      forall key', valueA, valueB, lookupA: Lookup, lookupB: Lookup
      |
      && IsSatisfyingLookup(newtree, key', valueA, lookupA)
      && IsSatisfyingLookup(newtree, key', valueB, lookupB)
      ensures valueA == valueB;
      {
        SatisfyingLookupSlotIsLargestLte(newtree, key', valueA, lookupA);
        SatisfyingLookupSlotIsLargestLte(newtree, key', valueB, lookupB);
        SatisfyingLookupsNest(newtree, key', valueA, lookupA);
        SatisfyingLookupsNest(newtree, key', valueB, lookupB);
      }
      assert CantEquivocate(newtree);

    }
  }

  lemma NextStepPreservesInvariant(k: Constants, s: Variables, s': Variables, step: Step)
  requires Invariant(k, s);
  requires NextStep(k, s, s', step);
  ensures Invariant(k, s');
  {
    match step {
      case GetStep(key, value, lookup) => {
      }
      case PutStep(key, value) => {
        PutPreservesInvariant(k, s, s', key, value);
      }
      case GrowStep(childrenToLeft) => {
        GrowPreservesInvariant(k, s, s', childrenToLeft);
      }
    }
  }

  lemma NextPreservesInvariant(k: Constants, s: Variables, s': Variables)
  requires Invariant(k, s)
  requires Next(k, s, s')
  ensures Invariant(k, s')
  {
    var step :| NextStep(k, s, s', step);
    NextStepPreservesInvariant(k, s, s', step);
  }
}
