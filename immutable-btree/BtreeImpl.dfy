include "../lib/total_order.dfy"
include "../lib/Maps.dfy"
include "../lib/mathematics.dfy"
include "../lib/sequences.dfy"
include "BtreeInv.dfy"

abstract module BtreeImpl {
  import opened Inv : BtreeInv
  import opened Sequences

  lemma strictlySortedInsert(l: seq<Spec.Key>, k: Spec.Key, pos: int)
  requires -1 <= pos < |l|;
  requires Spec.CSMap.Keyspace.IsStrictlySorted(l);
  requires Spec.CSMap.Keyspace.IsSorted(l);
  requires pos == Spec.CSMap.Keyspace.LargestLte(l, k);
  requires pos < 0 || k != l[pos]
  ensures Spec.CSMap.Keyspace.IsStrictlySorted(insert(l,k,pos+1));
  {
    var l' := insert(l,k,pos+1);
    Spec.CSMap.Keyspace.reveal_IsStrictlySorted();

    forall i, j | 0 <= i < j < |l'|
    ensures Spec.CSMap.Keyspace.lt(l'[i], l'[j])
    {
      reveal_insert();
    }
  }

  method empty<Value>()
  returns (newtree: Spec.Node)
  ensures Spec.WFRoot(newtree)
  ensures CantEquivocate(newtree)
  {
    Spec.CSMap.Keyspace.reveal_IsStrictlySorted();
    return Spec.Leaf([], [], Spec.CSMap.Keyspace.Min_Element, Spec.CSMap.Keyspace.Max_Element);
  }

  method putInner<Value>(tree: Spec.Node, key: Spec.Key, value: Value)
  returns (newtree: Spec.Node)
  requires Spec.WFTree(tree)
  requires Spec.CSMap.Keyspace.lte(tree.lb, key);
  requires Spec.CSMap.Keyspace.lt(key, tree.ub);
  ensures Spec.Put(Spec.Constants(), Spec.Variables(tree), Spec.Variables(newtree), key, value)
  decreases tree
  {
    if (tree.Leaf?) {
      Spec.CSMap.Keyspace.IsStrictlySortedImpliesIsSorted(tree.keys);
      var pos := Spec.CSMap.Keyspace.LargestLte(tree.keys, key);
      if (pos >= 0 && key == tree.keys[pos]) {
        return Spec.Leaf(tree.keys, tree.values[pos := value], tree.lb, tree.ub);
      } else {
        var newkeys := insert(tree.keys, key, pos+1);
        var newvals := insert(tree.values, value, pos+1);
        strictlySortedInsert(tree.keys, key, pos);
        return Spec.Leaf(newkeys, newvals, tree.lb, tree.ub);
      }
    } else {
      Spec.CSMap.Keyspace.IsStrictlySortedImpliesIsSorted(tree.pivots);
      var pos := Spec.CSMap.Keyspace.LargestLte(tree.pivots, key) + 1;

      if (pos == 0) {
        assert tree.children[pos].lb == tree.lb;
        assert Spec.CSMap.Keyspace.lte(tree.lb, key);
      } else { 
        assert tree.children[pos].lb == tree.pivots[pos-1];
        assert Spec.CSMap.Keyspace.lte(tree.pivots[pos-1], key);
      }

      var new_child := putInner(tree.children[pos], key, value);
      var new_children := tree.children[pos := new_child];
      return Spec.Index(tree.pivots, new_children, tree.lb, tree.ub);
    }
  }

  method put<Value>(tree: Spec.Node, key: Spec.Key, value: Value)
  returns (newtree: Spec.Node)
  requires Spec.WFRoot(tree)
  requires Spec.CSMap.Keyspace.lte(tree.lb, key);
  requires Spec.CSMap.Keyspace.lt(key, tree.ub);
  ensures Spec.Put(Spec.Constants(), Spec.Variables(tree), Spec.Variables(newtree), key, value)
  decreases tree
  {
    if (tree.Leaf? && tree.keys == []) {
      return Spec.Leaf([key], [value], tree.lb, tree.ub);
    } else {
      newtree := putInner(tree, key, value);
      return newtree;
    }
  }
}
