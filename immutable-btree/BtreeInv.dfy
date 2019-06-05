include "../lib/total_order.dfy"
include "../lib/map_utils.dfy"
include "../lib/mathematics.dfy"
include "../lib/sequences.dfy"
include "BtreeSpec.dfy"

abstract module BtreeInv {
  import Keyspace = Bounded_Total_Order
  import opened Sequences
  import opened BtreeSpec

  predicate CantEquivocate<Value(!new)>(tree: Node<Value>)
  {
    forall key, value, value', lookup: Lookup<Value>, lookup': Lookup<Value> ::
      && IsSatisfyingLookup(tree, key, value, lookup)
      && IsSatisfyingLookup(tree, key, value', lookup') ==>
      value == value'
  }


  predicate Invariant(k: Constants, s: Variables) {
    && WFTree(s.root)
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

  lemma SatisfyingLookupSlotIsLargestLte<Value>(tree: Node, key: Key, value: Value, lookup: Lookup)
    requires IsSatisfyingLookup(tree, key, value, lookup);
    requires tree.Index?;
    ensures lookup[0].slot == Keyspace.LargestLte(tree.pivots, key) + 1;
  {
    var pos := Keyspace.LargestLte(tree.pivots, key) + 1;
    if lookup[0].slot < pos {
      SatisfyingLookupsNest(tree, key, value, lookup);
      assert Keyspace.lt(key, lookup[1].node.ub);
      assert Keyspace.lte(lookup[1].node.ub, tree.pivots[lookup[0].slot]);
      assert Keyspace.lte(tree.pivots[lookup[0].slot], tree.pivots[pos-1]);
      assert Keyspace.lte(tree.pivots[pos-1], key);
      assert false;
    } else if lookup[0].slot > pos {
      SatisfyingLookupsNest(tree, key, value, lookup);
      assert Keyspace.lt(key, tree.pivots[pos]);
      assert Keyspace.lte(tree.pivots[pos], tree.pivots[lookup[0].slot-1]);
      assert Keyspace.lte(tree.pivots[lookup[0].slot-1], lookup[1].node.lb);
      assert Keyspace.lte(lookup[1].node.lb, key);
      assert false;
    }
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
    reveal_NoDupes();
    if tree.Leaf? {
      var pos := Keyspace.LargestLte(tree.keys, key);
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

      } else {
        var newkeys := tree.keys[..pos+1] + [key] + tree.keys[pos+1..];
        var newvals := tree.values[..pos+1] + [value] + tree.values[pos+1..];
        assert newtree == Leaf(newkeys, newvals, tree.lb, tree.ub);
        //assert Keyspace.IsSorted(newtree.keys);
        assert IsSatisfyingLookup(newtree, key, value, [Layer(newtree, pos + 1)]);
        
        forall lookup: Lookup, key', value'
          | key' != key && IsSatisfyingLookup(tree, key', value', lookup)
          ensures exists lookup' :: IsSatisfyingLookup(newtree, key', value', lookup');
        {
          if lookup[0].slot <= pos {
            var lookup' := [Layer(newtree, lookup[0].slot)];
            assert IsSatisfyingLookup(newtree, key', value', lookup');
          } else {
            var lookup' := [Layer(newtree, lookup[0].slot + 1)];
            assert IsSatisfyingLookup(newtree, key', value', lookup');
          }
        }
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

      }
    } else {
      var pos := Keyspace.LargestLte(tree.pivots, key) + 1;

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
        SatisfyingLookupsNest(tree, key', value', lookup);
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
        SatisfyingLookupsNest(newtree, key', value', lookup');
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
}
