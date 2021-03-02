// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "../Lang/LinearSequence.s.dfy"
include "../Lang/LinearSequence.i.dfy"
include "../Base/sequences.i.dfy"
include "../Base/Maps.i.dfy"
include "../Base/total_order_impl.i.dfy"
include "../Base/mathematics.i.dfy"

abstract module BtreeModel {
  import opened LinearSequence_s
  import opened LinearSequence_i
  import opened Seq = Sequences
  import opened Maps
  import KeysImpl = Lexicographic_Byte_Order_Impl
  import Keys = KeysImpl.Ord
  import Integer_Order
  import Math = Mathematics
  
  type Key = Keys.Element
  type Value
    
  linear datatype Node =
    | Leaf(linear keys: seq<Key>, linear values: seq<Value>)
    | Index(linear pivots: seq<Key>, linear children: lseq<Node>)


  function {:opaque} AllKeys(node: Node) : set<Key>
    ensures node.Leaf? && 0 < |node.keys| ==> AllKeys(node) != {}
    ensures node.Index? && 0 < |node.pivots| ==> AllKeys(node) != {}
  {
    match node {
      case Leaf(keys, values) =>
        var result := set k | k in keys;
        if 0 < |node.keys| then
          assert node.keys[0] in result;
          result
        else
          result
      case Index(pivots, children) =>
        var pivotKeys := (set k | k in pivots);
        var indexKeys := (set i, k | 0 <= i < |children| && k in AllKeys(children[i]) :: k);
        var result := pivotKeys + indexKeys;
        if 0 < |node.pivots| then
          assert node.pivots[0] in result;
          result
        else
          result
    }    
  }

  predicate AllKeysBelowBound(node: Node, i: int)
    requires node.Index?
    requires 0 <= i < |node.children|-1
    requires 0 <= i < |node.pivots|
  {
    forall key :: key in AllKeys(node.children[i]) ==> Keys.lt(key, node.pivots[i])
  }

  predicate AllKeysAboveBound(node: Node, i: int)
    requires node.Index?
    requires 0 <= i < |node.children|
    requires 0 <= i-1 < |node.pivots|
  {
    forall key :: key in AllKeys(node.children[i]) ==> Keys.lte(node.pivots[i-1], key)
  }
  
  predicate WF(node: Node)
    decreases node, 1
  {
    if node.Leaf? then
      && |node.keys| == |node.values|
      && Keys.IsStrictlySorted(node.keys)
    else
      && |node.pivots| == |node.children| - 1
      && Keys.IsStrictlySorted(node.pivots)
      && (forall i :: 0 <= i < |node.children| ==> WF(node.children[i]))
      && (forall i :: 0 <= i < |node.children| ==> AllKeys(node.children[i]) != {})
      && (forall i :: 0 <= i < |node.children|-1 ==> AllKeysBelowBound(node, i))
      && (forall i :: 0 < i < |node.children|   ==> AllKeysAboveBound(node, i))
  }

  function {:opaque} Interpretation(node: Node) : map<Key, Value>
    requires WF(node)
    decreases node
  {
    if node.Leaf? then
      Keys.PosEqLargestLteForAllElts(node.keys);
      map k | (k in node.keys) :: node.values[Keys.LargestLte(node.keys, k)]
    else 
      map key |
      && key in AllKeys(node)
      && key in Interpretation(node.children[Keys.LargestLte(node.pivots, key) + 1])
      :: Interpretation(node.children[Keys.LargestLte(node.pivots, key) + 1])[key]
  }

  lemma InterpretationInheritance(node: Node, key: Key)
    requires WF(node)
    requires node.Index?
    requires key in Interpretation(node)
    ensures MapsTo(Interpretation(node.children[Keys.LargestLte(node.pivots, key)+1]), key, Interpretation(node)[key])
  {
    reveal_Interpretation();
  }

  lemma InterpretationDelegation(node: Node, key: Key)
    requires WF(node)
    requires node.Index?
    requires key in Interpretation(node.children[Keys.LargestLte(node.pivots, key)+1])
    ensures MapsTo(Interpretation(node), key, Interpretation(node.children[Keys.LargestLte(node.pivots, key)+1])[key])
  {
    reveal_Interpretation();
    reveal_AllKeys();
    var interp := Interpretation(node);
    assert key in AllKeys(node.children[Keys.LargestLte(node.pivots, key)+1]);
    assert key in AllKeys(node);
    assert key in interp;
  }

  lemma AllKeysIsConsistentWithInterpretation(node: Node, key: Key)
    requires WF(node)
    requires key in Interpretation(node)
    ensures key in AllKeys(node)
    ensures node.Index? ==> WF(node) && key in AllKeys(node.children[Keys.LargestLte(node.pivots, key) + 1])
  {
    reveal_Interpretation();
    reveal_AllKeys();
    if node.Index? {
      assert key in Interpretation(node.children[Keys.LargestLte(node.pivots, key) + 1]);
    }
  }

  lemma ChildInterpretationSubMap(node: Node, i: nat)
    requires WF(node)
    requires node.Index?
    requires i < |node.children|
    ensures IsSubMap(Interpretation(node.children[i]), Interpretation(node))
  {
    forall k | k in Interpretation(node.children[i])
      ensures MapsAgreeOnKey(Interpretation(node), Interpretation(node.children[i]), k)
    {
      AllKeysIsConsistentWithInterpretation(node.children[i], k);
      if 0 < i {
        assert AllKeysAboveBound(node, i);
      }
      if i < |node.children| - 1 {
        assert AllKeysBelowBound(node, i);
      }
      Keys.LargestLteIsUnique2(node.pivots, k, i as int - 1);
      InterpretationDelegation(node, k);
    }
  }
  
  lemma IndexesNonempty(node: Node)
    requires WF(node)
    requires node.Index?
    ensures 0 < |Interpretation(node)|
  {
    var child := node.children[0];
    if child.Leaf? {
      reveal_Interpretation();
      reveal_AllKeys();
      assert 0 < |child.keys|;
      var key := child.keys[0];
      assert key  in Interpretation(child);
      assert key in AllKeys(child);
      if 0 < |node.pivots| {
        assert AllKeysBelowBound(node, 0);
        assert Keys.LargestLte(node.pivots, key) == -1;
      } else {
        assert Keys.LargestLte(node.pivots, key) == -1;
      }
      InterpretationDelegation(node, key);
    } else {
      IndexesNonempty(child);
      var key :| key in Interpretation(child);
      AllKeysIsConsistentWithInterpretation(child, key);
      assert key in AllKeys(child);
      if 0 < |node.pivots| {
        assert AllKeysBelowBound(node, 0);
        assert Keys.LargestLte(node.pivots, key) == -1;
      } else {
        assert Keys.LargestLte(node.pivots, key) == -1;
      }
      InterpretationDelegation(node, key);      
    }
  }
  
  lemma ChildOfIndexNonempty(node: Node, i: nat)
    requires WF(node)
    requires node.Index?
    requires i < |node.children|
    ensures 0 < |Interpretation(node.children[i])|
  {
    var child := node.children[i];
    if child.Leaf? {
      reveal_Interpretation();
      reveal_AllKeys();
      assert 0 < |child.keys|;
      var key := child.keys[0];
      assert key  in Interpretation(child);      
    } else {
      IndexesNonempty(child);
    }
  }
  
  function MinKey(node: Node) : (result: Key)
    requires WF(node)
    requires 0 < |Interpretation(node)|
  {
    if node.Leaf? then (
      assert |node.keys| == 0 ==> Interpretation(node) == map[] by {
        reveal_Interpretation();
      }
      node.keys[0]
    ) else (
      ChildOfIndexNonempty(node, 0);
      MinKey(node.children[0])
    )
  }

  lemma MinKeyProperties(node: Node)
    requires WF(node)
    requires 0 < |Interpretation(node)|
    ensures MinKey(node) in Interpretation(node)
    ensures forall key | key in Interpretation(node) :: Keys.lte(MinKey(node), key)
  {
    var result := MinKey(node);
    if node.Leaf? {
      reveal_Interpretation();
    } else {
      var child := node.children[0];
      ChildOfIndexNonempty(node, 0);
      MinKeyProperties(child);
      if 0 < |node.pivots| {
        assert AllKeysBelowBound(node, 0);
        AllKeysIsConsistentWithInterpretation(child, result);
        assert Keys.LargestLte(node.pivots, result) == -1;
      } else {
        assert Keys.LargestLte(node.pivots, result) == -1;
      }
      InterpretationDelegation(node, result);
      forall key | key in Interpretation(node)
        ensures Keys.lte(result, key)
      {
        var keyidx := 1 + Keys.LargestLte(node.pivots, key);
        InterpretationInheritance(node, key);
        if keyidx == 0 {
        } else {
          assert AllKeysBelowBound(node, 0);
          Keys.IsStrictlySortedImpliesLte(node.pivots, 0, keyidx-1);
          assert AllKeysAboveBound(node, keyidx);
        }
      }
    }
  }

  function MaxKey(node: Node) : (result: Key)
    requires WF(node)
    requires 0 < |Interpretation(node)|
  {
    if node.Leaf? then (
      assert |node.keys| == 0 ==> Interpretation(node) == map[] by {
        reveal_Interpretation();
      }
      Last(node.keys)
    ) else (
      ChildOfIndexNonempty(node, |node.children| - 1);
      MaxKey(Last(lseqs(node.children)))
    )
  }

  lemma MaxKeyProperties(node: Node)
    requires WF(node)
    requires 0 < |Interpretation(node)|
    ensures MaxKey(node) in Interpretation(node)
    ensures forall key | key in Interpretation(node) :: Keys.lte(key, MaxKey(node))
  {
    var result := MaxKey(node);
    if node.Leaf? {
      reveal_Interpretation();
    } else {
      var child := Last(lseqs(node.children));
      ChildOfIndexNonempty(node, |node.children|-1);
      MaxKeyProperties(child);
      if 0 < |node.pivots| {
        assert AllKeysAboveBound(node, |node.children|-1);
        AllKeysIsConsistentWithInterpretation(child, result);
        assert Keys.LargestLte(node.pivots, result) == |node.pivots|-1;
      } else {
        assert Keys.LargestLte(node.pivots, result) == |node.pivots|-1;
      }
      InterpretationDelegation(node, result);
      forall key | key in Interpretation(node)
        ensures Keys.lte(key, result)
      {
        var keyidx := 1 + Keys.LargestLte(node.pivots, key);
        InterpretationInheritance(node, key);
        if keyidx == |node.children| - 1 {
        } else {
          assert AllKeysBelowBound(node, keyidx);
          Keys.IsStrictlySortedImpliesLte(node.pivots, keyidx, |node.pivots| - 1);
          assert AllKeysAboveBound(node, |node.children| - 1);
        }
      }
    }
  }
  
  predicate SplitLeaf(oldleaf: Node, leftleaf: Node, rightleaf: Node, pivot: Key)
  {
    && oldleaf.Leaf?
    && leftleaf.Leaf?
    && rightleaf.Leaf?
    && 0 < |leftleaf.keys| == |leftleaf.values|
    && 0 < |rightleaf.keys| == |rightleaf.values|
    && oldleaf.keys == leftleaf.keys + rightleaf.keys
    && oldleaf.values == leftleaf.values + rightleaf.values
    && Keys.lt(Last(leftleaf.keys), pivot)
    && Keys.lte(pivot, rightleaf.keys[0])
  }

  lemma SplitLeafPreservesWF(oldleaf: Node, leftleaf: Node, rightleaf: Node, pivot: Key)
    requires WF(oldleaf)
    requires SplitLeaf(oldleaf, leftleaf, rightleaf, pivot)
    ensures WF(leftleaf)
    ensures WF(rightleaf)
  {
    Keys.StrictlySortedSubsequence(oldleaf.keys, 0, |leftleaf.keys|);
    Keys.StrictlySortedSubsequence(oldleaf.keys, |leftleaf.keys|, |oldleaf.keys|);
    assert Keys.IsStrictlySorted(oldleaf.keys[|leftleaf.keys|..|oldleaf.keys|]);
    assert rightleaf.keys == oldleaf.keys[|leftleaf.keys|..|oldleaf.keys|];
  }

  lemma SplitLeafInterpretation(oldleaf: Node, leftleaf: Node, rightleaf: Node, pivot: Key)
    requires SplitLeaf(oldleaf, leftleaf, rightleaf, pivot)
    requires WF(oldleaf)
    requires WF(leftleaf)
    requires WF(rightleaf)
    ensures Interpretation(oldleaf) == Keys.MapPivotedUnion(Interpretation(leftleaf), pivot, Interpretation(rightleaf))
  {
    reveal_Interpretation();
    var oldint := Interpretation(oldleaf);
    var leftint := Interpretation(leftleaf);
    var rightint := Interpretation(rightleaf);
    var newint := Keys.MapPivotedUnion(leftint, pivot, rightint);

    forall key | key in oldint
      ensures key in newint && newint[key] == oldint[key]
    {
      var llte := Keys.LargestLte(oldleaf.keys, key);
      if llte < |leftleaf.keys| {
        Keys.PosEqLargestLte(leftleaf.keys, key, llte);
        Keys.IsStrictlySortedImpliesLt(oldleaf.keys, llte, |leftleaf.keys|);
      } else {
        var rightllte := llte - |leftleaf.keys|;
        Keys.PosEqLargestLte(rightleaf.keys, key, rightllte);
        if |leftleaf.keys| < llte {
          Keys.IsStrictlySortedImpliesLt(oldleaf.keys, |leftleaf.keys|, llte);
        }
      }
    }

    forall key | key in newint
      ensures key in oldint && oldint[key] == newint[key]
    {
      if Keys.lt(key, pivot) {
        var llte := Keys.LargestLte(leftleaf.keys, key);
        Keys.PosEqLargestLte(oldleaf.keys, key, llte);
      } else {
        var llte := Keys.LargestLte(rightleaf.keys, key);
        Keys.PosEqLargestLte(oldleaf.keys, key, |leftleaf.keys| + llte);
      }
    }
  }

  function SubIndex(node: Node, from: int, to: int) : Node
    requires node.Index?
    requires |node.children| == |node.pivots| + 1
    requires 0 <= from < to <= |node.children|
  {
    Index(node.pivots[from..to-1],
      imagine_lseq(lseqs(node.children)[from..to]))
  }

  lemma SubIndexPreservesWF(node: Node, from: int, to: int)
    requires WF(node)
    requires node.Index?
    requires 0 <= from < to <= |node.children|
    ensures WF(SubIndex(node, from, to))
  {
    Keys.StrictlySortedSubsequence(node.pivots, from, to-1);
    var subindex := SubIndex(node, from, to);
    forall i | 0 <= i < to - from - 1
      ensures AllKeysBelowBound(subindex, i)
    {
      assert AllKeysBelowBound(node, from + i);
    }
    forall i | 0 < i < to - from
      ensures AllKeysAboveBound(subindex, i)
    {
      assert AllKeysAboveBound(node, from + i);
    }
    assert |subindex.pivots| == |subindex.children| - 1;
    assert WF(subindex);
  }
  
  predicate SplitIndex(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
  {
    && oldindex.Index?
    && leftindex.Index?
    && rightindex.Index?
    && 0 < |leftindex.children| < |oldindex.children|
    && |oldindex.children| == |oldindex.pivots| + 1

    && leftindex == SubIndex(oldindex, 0, |leftindex.children|)
    && rightindex == SubIndex(oldindex, |leftindex.children|, |oldindex.children|)
    && (forall key :: key in AllKeys(linLast(leftindex.children)) ==> Keys.lt(key, pivot))
    && (forall key :: key in AllKeys(rightindex.children[0]) ==> Keys.lte(pivot, key))
    && pivot == oldindex.pivots[|leftindex.pivots|]
  }

  lemma SplitIndexPreservesWF(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
    requires WF(oldindex)
    requires SplitIndex(oldindex, leftindex, rightindex, pivot)
    ensures WF(leftindex)
    ensures WF(rightindex)
  {
    SubIndexPreservesWF(oldindex, 0, |leftindex.children|);
    SubIndexPreservesWF(oldindex, |leftindex.children|, |oldindex.children|);
  }
  
  //Timeout
  /* either ensures seem to cause a timeout 
     too many things to ensure? */
  lemma SplitIndexInterpretation1(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
    requires WF(oldindex)
    requires WF(leftindex)
    requires WF(rightindex)
    requires SplitIndex(oldindex, leftindex, rightindex, pivot)
    ensures forall key :: key in Interpretation(oldindex) ==>
    MapsTo(Keys.MapPivotedUnion(Interpretation(leftindex), pivot, Interpretation(rightindex)), key, Interpretation(oldindex)[key])
  {
    reveal_Interpretation();
    var oldint := Interpretation(oldindex);
    var leftint := Interpretation(leftindex);
    var rightint := Interpretation(rightindex);
    var newint := Keys.MapPivotedUnion(leftint, pivot, rightint);

    forall key | key in oldint
      ensures MapsTo(newint, key, oldint[key])
    {
      AllKeysIsConsistentWithInterpretation(oldindex, key);
      var llte := Keys.LargestLte(oldindex.pivots, key);
      if Keys.lt(key, pivot) { 
        Keys.LargestLteSubsequence(oldindex.pivots, key, 0, |leftindex.pivots|);
        assert leftindex.children[llte+1] == oldindex.children[llte+1];
      } else {
        Keys.LargestLteSubsequence(oldindex.pivots, key, |leftindex.pivots|+1, |oldindex.pivots|);
        assert rightindex.children[llte - |leftindex.children| + 1] == oldindex.children[llte + 1];
        InterpretationInheritance(oldindex, key);
        InterpretationDelegation(rightindex, key);
      }
      reveal_AllKeys();
    }
  }
  
  //Timeout
  /* Same with previous, either ensures causes timeout */
  lemma SplitIndexInterpretation2(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
    requires WF(oldindex)
    requires WF(leftindex)
    requires WF(rightindex)
    requires SplitIndex(oldindex, leftindex, rightindex, pivot)
    ensures Interpretation(oldindex).Keys >=
            Keys.MapPivotedUnion(Interpretation(leftindex), pivot, Interpretation(rightindex)).Keys
  {
    reveal_Interpretation();
    var oldint := Interpretation(oldindex);
    var leftint := Interpretation(leftindex);
    var rightint := Interpretation(rightindex);
    var newint := Keys.MapPivotedUnion(leftint, pivot, rightint);

    forall key | key in newint
      ensures key in oldint
    {
      if Keys.lt(key, pivot) {
        AllKeysIsConsistentWithInterpretation(leftindex, key);
        var llte := Keys.LargestLte(leftindex.pivots, key);
        Keys.LargestLteSubsequence(oldindex.pivots, key, 0, |leftindex.pivots|);
        assert oldindex.children[llte+1] == leftindex.children[llte+1];
        InterpretationInheritance(leftindex, key);
      } else {
        AllKeysIsConsistentWithInterpretation(rightindex, key);
        var llte := Keys.LargestLte(rightindex.pivots, key);
        Keys.LargestLteSubsequence(oldindex.pivots, key, |leftindex.pivots|+1, |oldindex.pivots|);
        assert oldindex.children[|leftindex.children| + llte + 1] == rightindex.children[llte+1];
      }
      reveal_AllKeys();
    }
  }

  lemma SplitIndexInterpretation(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
    requires WF(oldindex)
    requires WF(leftindex)
    requires WF(rightindex)
    requires SplitIndex(oldindex, leftindex, rightindex, pivot)
    ensures Interpretation(oldindex) ==
    Keys.MapPivotedUnion(Interpretation(leftindex), pivot, Interpretation(rightindex))
  {
    reveal_Interpretation();
    SplitIndexInterpretation1(oldindex, leftindex, rightindex, pivot);
    SplitIndexInterpretation2(oldindex, leftindex, rightindex, pivot);
  }

  predicate SplitNode(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
  {
    || SplitLeaf(oldnode, leftnode, rightnode, pivot)
    || SplitIndex(oldnode, leftnode, rightnode, pivot)
  }

  lemma SplitNodePreservesWF(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
    requires SplitNode(oldnode, leftnode, rightnode, pivot)
    requires WF(oldnode)
    ensures WF(leftnode)
    ensures WF(rightnode)
  {
    if SplitLeaf(oldnode, leftnode, rightnode, pivot) {
      SplitLeafPreservesWF(oldnode, leftnode, rightnode, pivot);
    } else {
      SplitIndexPreservesWF(oldnode, leftnode, rightnode, pivot);
    }
  }
    
  lemma SplitNodeInterpretation(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
    requires WF(oldnode)
    requires WF(leftnode)
    requires WF(rightnode)
    requires SplitNode(oldnode, leftnode, rightnode, pivot)
    ensures Interpretation(oldnode) == Keys.MapPivotedUnion(Interpretation(leftnode), pivot, Interpretation(rightnode))
  {
    if SplitLeaf(oldnode, leftnode, rightnode, pivot) {
      SplitLeafInterpretation(oldnode, leftnode, rightnode, pivot);
    } else {
      SplitIndexInterpretation(oldnode, leftnode, rightnode, pivot);
    }
  }

  lemma SplitLeafAllKeys(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
    requires WF(oldnode)
    requires WF(leftnode)
    requires WF(rightnode)
    requires SplitLeaf(oldnode, leftnode, rightnode, pivot)
    ensures AllKeys(oldnode) == AllKeys(leftnode) + AllKeys(rightnode)
    ensures AllKeys(leftnode) != {}
    ensures AllKeys(rightnode) != {}
    ensures forall key :: key in AllKeys(leftnode) ==> Keys.lt(key, pivot)
    ensures forall key :: key in AllKeys(rightnode) ==> Keys.lte(pivot, key)
  {
    reveal_AllKeys();
    assert leftnode.keys[0] in AllKeys(leftnode);
    assert rightnode.keys[0] in AllKeys(rightnode);
    forall key | key in AllKeys(leftnode)
      ensures Keys.lt(key, pivot)
    {
      var i :| 0 <= i < |leftnode.keys| && key == leftnode.keys[i];
      Keys.IsStrictlySortedImpliesLte(oldnode.keys, i, |leftnode.keys|-1);
    }
    forall key | key in AllKeys(rightnode)
      ensures Keys.lte(pivot, key)
    {
      var i :| 0 <= i < |rightnode.keys| && key == rightnode.keys[i];
      Keys.IsSortedImpliesLte(oldnode.keys, |leftnode.keys|, |leftnode.keys| + i);
    }
  }

  lemma SplitIndexAllKeys(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
    requires WF(oldnode)
    requires WF(leftnode)
    requires WF(rightnode)
    requires SplitIndex(oldnode, leftnode, rightnode, pivot)
    ensures AllKeys(oldnode) == AllKeys(leftnode) + AllKeys(rightnode) + {pivot}
    ensures AllKeys(leftnode) != {}
    ensures AllKeys(rightnode) != {}
    ensures forall key :: key in AllKeys(leftnode) ==> Keys.lt(key, pivot)
    ensures forall key :: key in AllKeys(rightnode) ==> Keys.lte(pivot, key)
  {
    reveal_AllKeys();
    var x :| x in AllKeys(leftnode.children[0]);
    assert x in AllKeys(leftnode);
    forall key | key in AllKeys(leftnode)
      ensures Keys.lt(key, pivot)
    {
      if i :| 0 <= i < |leftnode.pivots| && key == leftnode.pivots[i] {
        Keys.IsStrictlySortedImpliesLt(oldnode.pivots, i, |leftnode.pivots|);
      } else {
        var i :| 0 <= i < |leftnode.children| && key in AllKeys(leftnode.children[i]);
        assert AllKeysBelowBound(oldnode, i);
        if i < |leftnode.pivots| {
          Keys.IsStrictlySortedImpliesLt(oldnode.pivots, i, |leftnode.pivots|);
        }
      }
    }
    forall key | key in AllKeys(rightnode)
      ensures Keys.lte(pivot, key)
    {
      if i :| 0 <= i < |rightnode.pivots| && key == rightnode.pivots[i] {
        Keys.IsSortedImpliesLte(oldnode.pivots, |leftnode.pivots|, |leftnode.children| + i);
      } else {
        var i :| 0 <= i < |rightnode.children| && key in AllKeys(rightnode.children[i]);
        assert AllKeysAboveBound(oldnode, |leftnode.children| + i);
        Keys.IsSortedImpliesLte(oldnode.pivots, |leftnode.pivots|, |leftnode.children| + i - 1);
      }
    }
    assert linLast(rightnode.children) == linLast(oldnode.children);
  }
  
  lemma SplitNodeAllKeys(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
    requires WF(oldnode)
    requires WF(leftnode)
    requires WF(rightnode)
    requires SplitNode(oldnode, leftnode, rightnode, pivot)
    ensures AllKeys(oldnode) <= AllKeys(leftnode) + AllKeys(rightnode) + {pivot}
    ensures AllKeys(leftnode) + AllKeys(rightnode) <= AllKeys(oldnode)
    ensures AllKeys(leftnode) != {}
    ensures AllKeys(rightnode) != {}
    ensures forall key :: key in AllKeys(leftnode) ==> Keys.lt(key, pivot)
    ensures forall key :: key in AllKeys(rightnode) ==> Keys.lte(pivot, key)
  {
    if SplitLeaf(oldnode, leftnode, rightnode, pivot) {
      SplitLeafAllKeys(oldnode, leftnode, rightnode, pivot);
    } else {
      SplitIndexAllKeys(oldnode, leftnode, rightnode, pivot);
    }
  }
  
  predicate SplitChildOfIndex(oldindex: Node, newindex: Node, childidx: int)
  {
    && oldindex.Index?
    && newindex.Index?
    && 0 <= childidx < |oldindex.children|
    && |newindex.children| == |oldindex.children| + 1 // FIXME: Why can't Dafny get these from WF?
    && |newindex.pivots| == |oldindex.pivots| + 1
    && |oldindex.pivots| == |oldindex.children| - 1
    && SplitNode(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], newindex.pivots[childidx])
    && newindex.pivots == Seq.insert(oldindex.pivots, newindex.pivots[childidx], childidx)
    && lseqs(newindex.children) == Seq.replace1with2(lseqs(oldindex.children), newindex.children[childidx], newindex.children[childidx+1], childidx)
  }

  lemma SplitChildOfIndexPreservesWF(oldindex: Node, newindex: Node, childidx: int)
    requires WF(oldindex)
    requires SplitChildOfIndex(oldindex, newindex, childidx)
    ensures WF(newindex)
  {
    var pivot := newindex.pivots[childidx];
    var oldchild := oldindex.children[childidx];
    var leftchild := newindex.children[childidx];
    var rightchild := newindex.children[childidx+1];
    SplitNodePreservesWF(oldchild, leftchild, rightchild, pivot);
    SplitNodeAllKeys(oldchild, leftchild, rightchild, pivot);
    SplitNodePreservesWF(oldchild, leftchild, rightchild, pivot);
    assert 0 < childidx ==> AllKeysAboveBound(oldindex, childidx);
    assert childidx < |oldindex.pivots| ==> AllKeysBelowBound(oldindex, childidx);
    if childidx < |oldindex.pivots| {
      assert Keys.lt(pivot, oldindex.pivots[childidx]) by { reveal_AllKeys(); }
    }
    Keys.strictlySortedInsert2(oldindex.pivots, pivot, childidx);

    forall i | 0 <= i < |newindex.children|
      ensures WF(newindex.children[i])
      ensures AllKeys(newindex.children[i]) != {}
    {
      if i < childidx {
      } else if i == childidx {
      } else if i == childidx + 1 {
      } else {
        assert newindex.children[i] == oldindex.children[i-1];
      }
    }

    forall i, key | 0 <= i < |newindex.children| - 1 && key in AllKeys(newindex.children[i])
      ensures Keys.lt(key, newindex.pivots[i])
    {
      if i < childidx {
        assert AllKeysBelowBound(oldindex, i);
      } else if i == childidx {
      } else if i == childidx + 1 {
      } else {
        assert newindex.children[i] == oldindex.children[i-1];
        assert AllKeysBelowBound(oldindex, i-1);
      }      
    }

    forall i, key | 0 < i < |newindex.children| && key in AllKeys(newindex.children[i])
      ensures Keys.lte(newindex.pivots[i-1], key)
    {
      if i < childidx {
        assert AllKeysAboveBound(oldindex, i);
      } else if i == childidx {
      } else if i == childidx + 1 {
        assert Keys.lte(newindex.pivots[i-1], key);
      } else {
        assert newindex.children[i] == oldindex.children[i-1];
        assert AllKeysAboveBound(oldindex, i-1);
      }      
    }
  }

  lemma SplitChildOfIndexPreservesAllKeys(oldindex: Node, newindex: Node, childidx: int)
    requires WF(oldindex)
    requires WF(newindex)
    requires SplitChildOfIndex(oldindex, newindex, childidx)
    ensures AllKeys(newindex) == AllKeys(oldindex) + {newindex.pivots[childidx]}
  {
    reveal_AllKeys();
    SplitChildOfIndexPreservesWF(oldindex, newindex, childidx);
    SplitNodeAllKeys(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], newindex.pivots[childidx]);
    
    forall key | key in AllKeys(newindex)
      ensures key in AllKeys(oldindex) + {newindex.pivots[childidx]}
    {
      if i :| 0 <= i < |newindex.children| && key in AllKeys(newindex.children[i]) {
        if i < childidx {
        } else if i == childidx {
        } else if i == childidx + 1 {
        } else {
          assert newindex.children[i] == oldindex.children[i-1];
        }
      } else {
        var i :| 0 <= i < |newindex.pivots| && key == newindex.pivots[i];
        if i < childidx {
        } else if i == childidx {
          assert key in {newindex.pivots[childidx]};
        } else if i == childidx + 1 {
          assert key == oldindex.pivots[i-1];
        } else {
          assert key == oldindex.pivots[i-1];
        }
      }
    }
  }

  //Timeout  
  lemma SplitChildOfIndexPreservesInterpretationA(oldindex: Node, newindex: Node, childidx: int)
    requires WF(oldindex);
    requires WF(newindex);
    requires SplitChildOfIndex(oldindex, newindex, childidx)
    ensures forall key :: key in Interpretation(oldindex) ==> MapsTo(Interpretation(newindex), key, Interpretation(oldindex)[key])
  {
    reveal_Interpretation();
    var newint := Interpretation(newindex);
    var oldint := Interpretation(oldindex);

    // These speed up verification a bit, but we don't understand why.
    assert newint == Interpretation(newindex);
    assert oldint == Interpretation(oldindex);
    
    var oldchild := oldindex.children[childidx];
    var leftchild := newindex.children[childidx];
    var rightchild := newindex.children[childidx+1];
    var pivot := newindex.pivots[childidx];
    
    SplitChildOfIndexPreservesAllKeys(oldindex, newindex, childidx);
    
    forall key | key in oldint
      ensures MapsTo(newint, key, oldint[key])
    {
      var llte := Keys.LargestLte(oldindex.pivots, key);
      if llte + 1 < childidx {
        Keys.LargestLteIsUnique2(newindex.pivots, key, llte);
        assert newindex.children[llte+1] == oldindex.children[llte+1];
      } else if llte + 1 == childidx {
        SplitNodeInterpretation(oldchild, leftchild, rightchild, pivot);
        if Keys.lt(key, pivot) {
          Keys.LargestLteIsUnique2(newindex.pivots, key, llte);
          InterpretationDelegation(newindex, key);
          InterpretationDelegation(oldindex, key);
        } else {
          assert llte+2 < |newindex.pivots| ==> newindex.pivots[llte+2] == oldindex.pivots[llte+1];
          Keys.LargestLteIsUnique2(newindex.pivots, key, llte+1);
          InterpretationDelegation(newindex, key);
          InterpretationDelegation(oldindex, key);
        }
      } else {
        var newllte := llte + 1;
        assert newindex.pivots[newllte] == oldindex.pivots[llte];
        assert newllte+1 < |newindex.pivots| ==> newindex.pivots[newllte+1] == oldindex.pivots[llte+1];
        assert newllte+1 < |newindex.pivots| ==> Keys.lt(key, newindex.pivots[newllte+1]);
        assert Keys.lte(newindex.pivots[newllte], key);
        Keys.LargestLteIsUnique2(newindex.pivots, key, newllte);
        assert newindex.children[newllte+1] == oldindex.children[llte+1];
      }
    }
  }

  //Timeout
  lemma SplitChildOfIndexPreservesInterpretationB(oldindex: Node, newindex: Node, childidx: int)
    requires WF(oldindex);
    requires WF(newindex);
    requires SplitChildOfIndex(oldindex, newindex, childidx)
    ensures forall key :: key in Interpretation(newindex) ==> key in Interpretation(oldindex)
      //ensures Interpretation(newindex) == Interpretation(oldindex)
  {
    reveal_Interpretation();
    var newint := Interpretation(newindex);
    var oldint := Interpretation(oldindex);

    // Why can't Dafny see these (from emacs flycheck mode)!?
    assert WF(oldindex);
    assert WF(newindex);
    assert oldint == Interpretation(oldindex);
    assert newint == Interpretation(newindex);
    
    var oldchild := oldindex.children[childidx];
    var leftchild := newindex.children[childidx];
    var rightchild := newindex.children[childidx+1];
    var pivot := newindex.pivots[childidx];
    SplitNodeInterpretation(oldchild, leftchild, rightchild, pivot);
    SplitChildOfIndexPreservesAllKeys(oldindex, newindex, childidx);
    

    forall key | key in newint
      ensures key in oldint
    {
      reveal_AllKeys();
      var llte := Keys.LargestLte(newindex.pivots, key);
      if llte + 1 < childidx {
        Keys.LargestLteIsUnique2(oldindex.pivots, key, llte);
        assert key in oldint;
      } else if llte + 1 == childidx {
        Keys.LargestLteIsUnique2(oldindex.pivots, key, llte);
        assert key in oldint;
      } else if llte + 1 == childidx + 1 {
        var oldllte := llte - 1;
        Keys.LargestLteIsUnique2(oldindex.pivots, key, oldllte);
        assert oldllte == Keys.LargestLte(oldindex.pivots, key);
        assert key in Interpretation(oldindex.children[Keys.LargestLte(oldindex.pivots, key) + 1]);
        InterpretationDelegation(oldindex, key);
        assert key in oldint;
      } else {
        Keys.LargestLteIsUnique2(oldindex.pivots, key, llte-1);
        assert key in oldint;
      }
    }
  }

  lemma SplitChildOfIndexPreservesInterpretation(oldindex: Node, newindex: Node, childidx: int)
    requires WF(oldindex);
    requires WF(newindex);
    requires SplitChildOfIndex(oldindex, newindex, childidx)
    ensures Interpretation(newindex) == Interpretation(oldindex)
  {
    reveal_Interpretation();
    SplitChildOfIndexPreservesInterpretationA(oldindex, newindex, childidx);
    SplitChildOfIndexPreservesInterpretationB(oldindex, newindex, childidx);
  }
  
  function InsertLeaf(leaf: Node, key: Key, value: Value) : (result: Node)
    requires leaf.Leaf?
    requires WF(leaf)
    ensures result.Leaf?
    ensures WF(result)
  {
    var llte := Keys.LargestLte(leaf.keys, key);
    if 0 <= llte && leaf.keys[llte] == key then
      Leaf(leaf.keys, leaf.values[llte := value])
    else
      Keys.strictlySortedInsert(leaf.keys, key, llte);
      Leaf(Seq.insert(leaf.keys, key, llte+1), Seq.insert(leaf.values, value, llte+1))
  }

  lemma InsertLeafIsCorrect(leaf: Node, key: Key, value: Value)
    requires leaf.Leaf?
    requires WF(leaf)
    ensures Interpretation(InsertLeaf(leaf, key, value)) == Interpretation(leaf)[key := value]
    ensures AllKeys(InsertLeaf(leaf, key, value)) == AllKeys(leaf) + {key}
  {
    reveal_AllKeys();
    reveal_Interpretation();
    var result := InsertLeaf(leaf, key, value);
    var llte := Keys.LargestLte(leaf.keys, key);
    if 0 <= llte && leaf.keys[llte] == key {
      assert Interpretation(result) == Interpretation(leaf)[key := value];
    } else {
      Keys.reveal_IsStrictlySorted();
      forall k | k in Interpretation(result).Keys
        ensures k in Interpretation(leaf).Keys + {key}
      {
        var kpos := IndexOf(result.keys, k);
        if llte + 1 < kpos {
          assert k == leaf.keys[kpos-1];
        }
      }
      forall k | k in AllKeys(result)
        ensures k in AllKeys(leaf) + {key}
      {
        var i :| 0 <= i < |result.keys| && result.keys[i] == k;
        if i < llte+1 {
        } else if i == llte+1 {
        } else {
          assert k == leaf.keys[i-1];
        }
      }
    }
  }

  //Timeout
  lemma RecursiveInsertIsCorrect(node: Node, key: Key, value: Value, pos: int, newnode: Node, newchild: Node)
    requires WF(node)
    requires node.Index?
    requires WF(newchild)
    requires pos == Keys.LargestLte(node.pivots, key)+1
    requires Interpretation(newchild) == Interpretation(node.children[pos])[key := value]
//    requires newnode == node.(children := node.children[pos := newchild])
// Can't do update on linear datatype, so instead we'll break out the parts:
    requires newnode.Index?
    requires newnode.pivots == node.pivots
    requires lseqs(newnode.children) == lseqs(node.children)[pos := newchild]

    requires AllKeys(newchild) <= AllKeys(node.children[pos]) + {key}
    ensures WF(newnode)
    ensures Interpretation(newnode) == Interpretation(node)[key := value]
    ensures AllKeys(newnode) <= AllKeys(node) + {key}
  {
    reveal_AllKeys();
    reveal_Interpretation();
    var oldint := Interpretation(node);
    AllKeysIsConsistentWithInterpretation(newchild, key);
    forall i | 0 <= i < |newnode.children| - 1
      ensures AllKeysBelowBound(newnode, i);
    {
      if i == pos {
        forall key' | key' in AllKeys(newchild)
          ensures Keys.lt(key', node.pivots[i])
        {
          if key' == key {
          } else {
            assert AllKeysBelowBound(node, i);
          }
        }
      } else {
        assert AllKeysBelowBound(node, i);
      }
    }
    forall i | 0 < i < |newnode.children|
      ensures AllKeysAboveBound(newnode, i);
    {
      if i == pos {
        forall key' | key' in AllKeys(newchild)
          ensures Keys.lte(node.pivots[i-1], key')
        {
          if key' == key {
          } else {
            assert AllKeysAboveBound(node, i);
          }
        }
      } else {
        assert AllKeysAboveBound(node, i);
      }
    }
    var newint := Interpretation(newnode);

    forall key' | key' in oldint && key' != key
      ensures MapsTo(newint, key', oldint[key'])
    {
      var llte := Keys.LargestLte(node.pivots, key');
      assert key' in Interpretation(node.children[llte+1]);
      if llte + 1 < pos {
        assert key' in AllKeys(newnode.children[llte+1]);
      } else if llte + 1 == pos {
        assert Interpretation(newnode.children[llte+1])[key'] == Interpretation(node.children[llte+1])[key'];
        assert key' in AllKeys(newchild);
      } else {
        assert key' in AllKeys(newnode.children[llte+1]);
      }
    }
    forall key' | key' in newint && key' != key
      ensures key' in oldint
    {
      var llte := Keys.LargestLte(node.pivots, key');
      assert key' in Interpretation(node.children[llte+1]);
      if llte + 1 < pos {
        assert key' in AllKeys(node.children[llte+1]);
      } else if llte + 1 == pos {
        assert Interpretation(newnode.children[llte+1])[key'] == Interpretation(node.children[llte+1])[key'];
        assert key' in AllKeys(node.children[llte+1]);
      } else {
        assert key' in AllKeys(node.children[llte+1]);
      }
    }

    assert key in Interpretation(newchild);
    assert key in AllKeys(newchild);
    assert newnode.children[Keys.LargestLte(newnode.pivots, key)+1] == newchild;
  }

  function Grow(node: Node) : Node
  {
    Index([], imagine_lseq([node]))
  }

  lemma GrowPreservesWF(node: Node)
    requires WF(node)
    requires AllKeys(node) != {}
    ensures WF(Grow(node))
  {
    assert Keys.IsStrictlySorted([]) by {
      Keys.reveal_IsStrictlySorted();
    }
  }

  lemma GrowPreservesAllKeys(node: Node)
    requires WF(node)
    ensures AllKeys(Grow(node)) == AllKeys(node)
  {
    reveal_AllKeys();
    assert forall key :: key in AllKeys(node) ==> key in AllKeys(Grow(node).children[0]);
  }
  
  lemma GrowPreservesInterpretation(node: Node)
    requires WF(node)
    requires AllKeys(node) != {}
    ensures WF(Grow(node))
    ensures Interpretation(Grow(node)) == Interpretation(node)
  {
    reveal_Interpretation();
    var interp := Interpretation(node);
    GrowPreservesWF(node);
    var ginterp := Interpretation(Grow(node));
    
    forall key | key in interp
      ensures key in ginterp && ginterp[key] == interp[key]
    {
      InterpretationDelegation(Grow(node), key);
    }
  }

  function ReplacePivot(node: Node, pivotidx: int, pivot: Key) : Node
    requires WF(node)
    requires node.Index?
    requires 0 <= pivotidx < |node.pivots|
  {
    node.(pivots := node.pivots[pivotidx := pivot])
  }

  function NumElementsOfChildren(nodes: seq<Node>) : nat
    requires forall i :: 0 <= i < |nodes| ==> WF(nodes[i])
  {
    if |nodes| == 0 then 0
    else NumElementsOfChildren(DropLast(nodes)) + NumElements(Last(nodes))
  }
  
  function NumElements(node: Node) : nat
    requires WF(node)
  {
    if node.Leaf? then |node.keys|
    else NumElementsOfChildren(lseqs(node.children))
  }

  lemma InterpretationsDisjoint(node: Node)
    requires WF(node)
    requires node.Index?
    requires 1 < |node.children|
    ensures WF(SubIndex(node, 0, |node.children|-1))
    ensures Interpretation(SubIndex(node, 0, |node.children|-1)).Keys !!
            Interpretation(Last(lseqs(node.children))).Keys
  {
    var left := SubIndex(node, 0, |node.children|-1);
    var rightchild := Last(lseqs(node.children));
    SubIndexPreservesWF(node, 0, |node.children|-1);
    forall key | key in Interpretation(rightchild)
      ensures key !in Interpretation(left)
    {
      if key in Interpretation(left) {
        var childidx := Keys.LargestLte(left.pivots, key) + 1;
        InterpretationInheritance(left, key);
        AllKeysIsConsistentWithInterpretation(left.children[childidx], key);
        assert AllKeysBelowBound(node, childidx);
        AllKeysIsConsistentWithInterpretation(rightchild, key);
        assert AllKeysAboveBound(node, |node.children|-1);
      }
    }
    if Interpretation(left).Keys * Interpretation(rightchild).Keys != {} {
      assert false;
    }
    assert Interpretation(left).Keys !! Interpretation(rightchild).Keys;
  }

  //ASSUME FALSE;
  lemma InterpretationsDisjointUnion(node: Node)
    requires WF(node)
    requires node.Index?
    requires 1 < |node.children|
    ensures WF(SubIndex(node, 0, |node.children|-1))
    ensures Interpretation(SubIndex(node, 0, |node.children|-1)).Keys !!
            Interpretation(Last(lseqs(node.children))).Keys
    ensures Interpretation(node) ==
       MapDisjointUnion(Interpretation(SubIndex(node, 0, |node.children|-1)),
                        Interpretation(Last(lseqs(node.children))))
  {
    InterpretationsDisjoint(node);
    var inode := Interpretation(node);
    var left := SubIndex(node, 0, |node.children|-1);
    var ileft := Interpretation(left);
    var rightchild := Last(lseqs(node.children));
    var irightchild := Interpretation(rightchild);
    var right := Grow(rightchild);
    GrowPreservesWF(rightchild);
    GrowPreservesInterpretation(rightchild);
    GrowPreservesAllKeys(rightchild);
    var iright := Interpretation(right);
    var pivot := Last(node.pivots);

    assert AllKeysBelowBound(node, |node.pivots|-1);
    assert AllKeysAboveBound(node, |node.pivots|);
    //assume false;
    assert lseqs(right.children) == lseqs(SubIndex(node, |left.children|, |node.children|).children);
    assert SplitIndex(node, left, right, pivot);
    SplitNodeInterpretation(node, left, right, pivot);
    
    var rileft := Maps.MapIRestrict(ileft, iset k | Keys.lt(k, pivot));
    var riright := Maps.MapIRestrict(iright, iset k | Keys.lte(pivot, k));

    forall k | k in ileft
      ensures Keys.lt(k, pivot)
    {
      var childidx := Keys.LargestLte(left.pivots, k) + 1;
      InterpretationInheritance(left, k);
      if childidx < |left.children| - 1 {
        assert AllKeysBelowBound(left, childidx);
      }
      AllKeysIsConsistentWithInterpretation(left, k);
    }

    forall k | k in iright
      ensures Keys.lte(pivot, k)
    {
      AllKeysIsConsistentWithInterpretation(right, k);
    }
  }
  
  
  lemma NumElementsOfChildrenMatchesInterpretation(nodes: lseq<Node>, pivots: seq<Key>)
    requires WF(Index(pivots, nodes))
    ensures NumElements(Index(pivots, nodes)) == |Interpretation(Index(pivots, nodes))|
    decreases lseqs(nodes)
  {
    var parent := Index(pivots, nodes);
    if |nodes| == 1 {
      assert AllKeys(parent) == AllKeys(nodes[0]) by {
        reveal_AllKeys();
      }
      forall key | key in Interpretation(parent)
        ensures MapsTo(Interpretation(nodes[0]), key, Interpretation(parent)[key])
      {
        InterpretationInheritance(parent, key);
      }
      forall key | key in Interpretation(nodes[0])
        ensures MapsTo(Interpretation(parent), key, Interpretation(nodes[0])[key])
      {
        InterpretationDelegation(parent, key);
      }
      MapsEqualExtensionality(Interpretation(parent), Interpretation(nodes[0]));
      assert NumElementsOfChildren(lseqs(nodes)) == NumElements(nodes[0]);
      NumElementsMatchesInterpretation(nodes[0]);
      calc {
        |Interpretation(nodes[0])|;
        { assert Interpretation(nodes[0]) == Interpretation(parent); }
        |Interpretation(parent)|;
      }
    } else {
      var left := Index(DropLast(pivots), imagine_lseq(DropLast(lseqs(nodes))));
      var right := Index([], imagine_lseq(lseqs(nodes)[|nodes|-1..]));
      var pivot := Last(pivots);
      assert AllKeysBelowBound(parent, |nodes|-2);
      assert AllKeysAboveBound(parent, |nodes|-1);
      assert lseqs(right.children) == lseqs(SubIndex(parent, |left.children|, |parent.children|).children);
      SplitIndexPreservesWF(parent, left, right, pivot);
      NumElementsOfChildrenMatchesInterpretation(left.children, left.pivots);
      NumElementsMatchesInterpretation(right.children[0]);
      InterpretationsDisjointUnion(parent);
      calc {
        NumElements(parent);
        |Interpretation(left)| + |Interpretation(right.children[0])|;
        { MapDisjointUnionCardinality(Interpretation(left), Interpretation(right.children[0])); }
        |Interpretation(parent)|;
      }
    }
  }
  
  lemma NumElementsMatchesInterpretation(node: Node)
    requires WF(node)
    ensures NumElements(node) == |Interpretation(node)|
    decreases node
  {
    var interp := Interpretation(node);
    reveal_Interpretation();
    if node.Leaf? {
      assert NoDupes(node.keys) by {
        reveal_NoDupes();
        Keys.reveal_IsStrictlySorted();
      }
      NoDupesSetCardinality(node.keys);
      assert interp.Keys == Set(node.keys);
    } else {
      NumElementsOfChildrenMatchesInterpretation(node.children, node.pivots);
    }
  }
  
  lemma NumElementsOfChildrenNotZero(node: Node)
    requires WF(node)
    requires node.Index?
    ensures forall child :: 0 <= child < |node.children| ==> 0 < NumElements(node.children[child])
  {
    forall child | 0 <= child < |node.children|
      ensures 0 < NumElements(node.children[child])
    {
      reveal_AllKeys();
      if node.children[child].Leaf? {
      } else {
        NumElementsOfChildrenNotZero(node.children[child]);
      }
    }
  }
  
  lemma NumElementsOfChildrenDecreases(nodes: seq<Node>, prefix: int)
    requires forall i :: 0 <= i < |nodes| ==> WF(nodes[i])
    requires 0 <= prefix <= |nodes|
    ensures NumElementsOfChildren(nodes[..prefix]) <= NumElementsOfChildren(nodes)
  {
    if prefix == |nodes| {
      assert nodes[..prefix] == nodes;
    } else {
      NumElementsOfChildrenDecreases(DropLast(nodes), prefix);
      assert DropLast(nodes)[..prefix] == nodes[..prefix];
    }
  }

  function ToSeqChildren(nodes: seq<Node>) : (kvlists : (seq<seq<Key>>, seq<seq<Value>>))
    requires forall i :: 0 <= i < |nodes| ==> WF(nodes[i])
    ensures |kvlists.0| == |kvlists.1| == |nodes|
    ensures forall i :: 0 <= i < |nodes| ==> (kvlists.0[i], kvlists.1[i]) == ToSeq(nodes[i])
    ensures FlattenShape(kvlists.0) == FlattenShape(kvlists.1)
  {
    if |nodes| == 0 then ([], [])
    else
      var kv1 := ToSeqChildren(DropLast(nodes));
      var kv2 := ToSeq(Last(nodes));
      (kv1.0 + [kv2.0], kv1.1 + [kv2.1])
  }
    
  function {:opaque} ToSeq(node: Node) : (kvlists : (seq<Key>, seq<Value>))
    requires WF(node)
    ensures |kvlists.0| == |kvlists.1|
  {
    if node.Leaf? then (node.keys, node.values)
    else
      var (keylists, valuelists) := ToSeqChildren(lseqs(node.children));
      (Flatten(keylists), Flatten(valuelists))
  }

  lemma ToSeqChildrenDecomposition(nodes: seq<Node>)
    requires forall i :: 0 <= i < |nodes| ==> WF(nodes[i])
    requires 0 < |nodes|
    ensures Flatten(ToSeqChildren(nodes).0) == Flatten(ToSeqChildren(DropLast(nodes)).0) + ToSeq(Last(nodes)).0
    ensures Flatten(ToSeqChildren(nodes).1) == Flatten(ToSeqChildren(DropLast(nodes)).1) + ToSeq(Last(nodes)).1
  {
    reveal_Flatten();
  }

  lemma ToSeqChildrenAdditive(nodes1: seq<Node>, nodes2: seq<Node>)
    requires forall i :: 0 <= i < |nodes1| ==> WF(nodes1[i])
    requires forall i :: 0 <= i < |nodes2| ==> WF(nodes2[i])
    ensures ToSeqChildren(nodes1 + nodes2).0 == ToSeqChildren(nodes1).0 + ToSeqChildren(nodes2).0
    ensures Flatten(ToSeqChildren(nodes1 + nodes2).0)
         == Flatten(ToSeqChildren(nodes1).0) + Flatten(ToSeqChildren(nodes2).0)
    ensures ToSeqChildren(nodes1 + nodes2).1 == ToSeqChildren(nodes1).1 + ToSeqChildren(nodes2).1
    ensures Flatten(ToSeqChildren(nodes1 + nodes2).1)
         == Flatten(ToSeqChildren(nodes1).1) + Flatten(ToSeqChildren(nodes2).1)
  {
    FlattenAdditive(ToSeqChildren(nodes1).0, ToSeqChildren(nodes2).0);
    FlattenAdditive(ToSeqChildren(nodes1).1, ToSeqChildren(nodes2).1);
  }
  
  lemma ToSeqChildrenLength(nodes: seq<Node>)
    requires forall i :: 0 <= i < |nodes| ==> WF(nodes[i])
    ensures |Flatten(ToSeqChildren(nodes).0)| == NumElementsOfChildren(nodes)
  {
    reveal_Flatten();
    if |nodes| == 0 {
    } else {
      ToSeqChildrenLength(DropLast(nodes));
      ToSeqLength(Last(nodes));
    }
  }
  
  lemma ToSeqLength(node: Node)
    requires WF(node)
    ensures |ToSeq(node).0| == NumElements(node)
  {
    reveal_ToSeq();
    if node.Leaf? {
    } else {
      ToSeqChildrenLength(lseqs(node.children));
    }      
  }

  lemma ToSeqInAllKeys(node: Node)
    requires WF(node)
    ensures forall key :: key in ToSeq(node).0 ==> key in AllKeys(node)
  {
    var (keys, values) := ToSeq(node);
    reveal_ToSeq();
    reveal_AllKeys();
    
    if node.Index? {
      var (childkeys, chilvalues) := ToSeqChildren(lseqs(node.children));
      var shape := FlattenShape(childkeys);
      
      forall i | 0 <= i < |keys|
        ensures keys[i] in AllKeys(node)
        {
          var (child, offset) := UnflattenIndex(shape, i);
          UnflattenIndexIsCorrect(childkeys, i);
          ToSeqInAllKeys(node.children[child]);
          assert keys[i] in AllKeys(node.children[child]);
        }
    } 
  }
  
  lemma ToSeqIsStrictlySorted(node: Node)
    requires WF(node)
    ensures Keys.IsStrictlySorted(ToSeq(node).0);
  {
    var (keys, values) := ToSeq(node);

    reveal_ToSeq();
    
    if node.Index? {
      var (keylists, valuelists) := ToSeqChildren(lseqs(node.children));
      var shape := FlattenShape(keylists);
      
      forall i | 0 <= i < |keylists|
        ensures Keys.IsStrictlySorted(keylists[i])
      {
        ToSeqIsStrictlySorted(node.children[i]);
      }

      forall i, j, k1, k2 | 0 <= i < j < |keylists| && k1 in keylists[i] && k2 in keylists[j]
        ensures Keys.lt(k1, k2)
      {
        ToSeqInAllKeys(node.children[i]);
        ToSeqInAllKeys(node.children[j]);
        assert AllKeysBelowBound(node, i);
        assert AllKeysAboveBound(node, j);
        if i < j-1 {
          Keys.IsStrictlySortedImpliesLt(node.pivots, i, j-1);
        }
      }
      Keys.FlattenStrictlySorted(keylists);
    }
  }

  //Timeout
  lemma ToSeqInInterpretation(node: Node)
    requires WF(node)
    ensures forall i :: 0 <= i < |ToSeq(node).0| ==> MapsTo(Interpretation(node), ToSeq(node).0[i], ToSeq(node).1[i])
  {
    reveal_Interpretation();
    var (keys, values) := ToSeq(node);
    var interp := Interpretation(node);
    
    reveal_ToSeq();
    
    if node.Leaf? {
      forall i | 0 <= i < |keys|
        ensures MapsTo(interp, keys[i], values[i])
        {
          Keys.PosEqLargestLte(keys, keys[i], i);
        }
    } else {
      var (keylists, valuelists) := ToSeqChildren(lseqs(node.children));
      var shape := FlattenShape(keylists);

      forall i | 0 <= i < |keys|
        ensures MapsTo(Interpretation(node), keys[i], values[i])
      {
        var (child, offset) := UnflattenIndex(shape, i);
        UnflattenIndexIsCorrect(keylists, i);
        UnflattenIndexIsCorrect(valuelists, i);
        ToSeqInInterpretation(node.children[child]);
        AllKeysIsConsistentWithInterpretation(node.children[child], keys[i]);
        if 0 < child {
          assert AllKeysAboveBound(node, child);
        }
        if child < |node.children| - 1 {
          assert AllKeysBelowBound(node, child);
        }
        Keys.LargestLteIsUnique2(node.pivots, keys[i], child-1);
        InterpretationDelegation(node, keys[i]);
      }
    }
  }

  lemma ToSeqCoversInterpretation(node: Node)
    requires WF(node)
    ensures forall key :: key in Interpretation(node) ==> key in ToSeq(node).0
  {
    reveal_Interpretation();
    var (keys, values) := ToSeq(node);
    var interp := Interpretation(node);
    
    reveal_ToSeq();
    
    if node.Index? {
      var (keylists, valuelists) := ToSeqChildren(lseqs(node.children));
      var shape := FlattenShape(keylists);

      forall key | key in Interpretation(node)
        ensures key in keys
      {
        InterpretationInheritance(node, key);
        var child := Keys.LargestLte(node.pivots, key) + 1;
        var offset :| 0 <= offset < |keylists[child]| && keylists[child][offset] == key;
        FlattenIndexIsCorrect(keylists, child, offset);
      }
    }
  }

  lemma InterpretationNumElements(node: Node)
    requires WF(node)
    ensures NumElements(node) == |Interpretation(node)|
  {
    ToSeqLength(node);
    ToSeqCoversInterpretation(node);
    ToSeqInInterpretation(node);
    ToSeqIsStrictlySorted(node);
    
    var keys := ToSeq(node).0;
    var interp := Interpretation(node);
    Keys.StrictlySortedImpliesNoDupes(keys);
    NoDupesSetCardinality(keys);
    assert Set(keys) == interp.Keys;
  }
}
