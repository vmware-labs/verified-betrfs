include "../lib/total_order.dfy"
include "../lib/map_utils.dfy"
include "../lib/mathematics.dfy"
include "../lib/sequences.dfy"
include "BtreeSpec.dfy"
include "BtreeInv.dfy"

module BtreeImpl {
  //import Keyspace : Bounded_Total_Order
  import opened Spec = BtreeSpec
  import opened Inv = BtreeInv
  import opened Sequences

  lemma strictlySortedInsert(l: seq<Key>, k: Key, pos: int)
  requires -1 <= pos < |l|;
  requires Keyspace.IsStrictlySorted(l);
  requires Keyspace.IsSorted(l);
  requires pos == Keyspace.LargestLte(l, k);
  requires pos < 0 || k != l[pos]
  ensures Keyspace.IsStrictlySorted(insert(l,k,pos+1));
  {
    var l' := insert(l,k,pos+1);
    Keyspace.reveal_IsStrictlySorted();

    forall i, j | 0 <= i < j < |l'|
    ensures Keyspace.lt(l'[i], l'[j])
    {
      reveal_insert();
    }
  }

  method empty<Value>()
  returns (newtree: Node)
  ensures WFRoot(newtree)
  ensures CantEquivocate(newtree)
  {
    Keyspace.reveal_IsStrictlySorted();
    return Leaf([], [], Keyspace.Min_Element, Keyspace.Max_Element);
  }

  method putInner<Value>(tree: Node, key: Key, value: Value)
  returns (newtree: Node)
  requires WFTree(tree)
  requires Keyspace.lte(tree.lb, key);
  requires Keyspace.lt(key, tree.ub);
  ensures Put(Constants(), Variables(tree), Variables(newtree), key, value)
  decreases tree
  {
    if (tree.Leaf?) {
      Keyspace.IsStrictlySortedImpliesIsSorted(tree.keys);
      var pos := Keyspace.LargestLte(tree.keys, key);
      if (pos >= 0 && key == tree.keys[pos]) {
        return Leaf(tree.keys, tree.values[pos := value], tree.lb, tree.ub);
      } else {
        var newkeys := insert(tree.keys, key, pos+1);
        var newvals := insert(tree.values, value, pos+1);
        strictlySortedInsert(tree.keys, key, pos);
        return Leaf(newkeys, newvals, tree.lb, tree.ub);
      }
    } else {
      Keyspace.IsStrictlySortedImpliesIsSorted(tree.pivots);
      var pos := Keyspace.LargestLte(tree.pivots, key) + 1;

      if (pos == 0) {
        assert tree.children[pos].lb == tree.lb;
        assert Keyspace.lte(tree.lb, key);
      } else { 
        assert tree.children[pos].lb == tree.pivots[pos-1];
        assert Keyspace.lte(tree.pivots[pos-1], key);
      }

      var new_child := putInner(tree.children[pos], key, value);
      var new_children := tree.children[pos := new_child];
      return Index(tree.pivots, new_children, tree.lb, tree.ub);
    }
  }

  method put<Value>(tree: Node, key: Key, value: Value)
  returns (newtree: Node)
  requires WFRoot(tree)
  requires Keyspace.lte(tree.lb, key);
  requires Keyspace.lt(key, tree.ub);
  ensures Put(Constants(), Variables(tree), Variables(newtree), key, value)
  decreases tree
  {
    if (tree.Leaf? && tree.keys == []) {
      return Leaf([key], [value], tree.lb, tree.ub);
    } else {
      newtree := putInner(tree, key, value);
      return newtree;
    }
  }
}
