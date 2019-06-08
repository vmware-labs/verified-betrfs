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
