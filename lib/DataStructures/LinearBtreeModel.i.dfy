include "../Lang/LinearSequence.s.dfy"
include "../Lang/LinearSequence.i.dfy"
include "../Base/sequences.i.dfy"
include "../Base/Maps.s.dfy"
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

//~  lemma WFIndexAllKeys(node: Node)
//~    requires node.Index?
//~    requires WF(node)
//~    ensures AllKeys(node) != {}
//~  {
//~    var x :| x in AllKeys(node.children[0]);
//~    reveal_AllKeys();
//~  }
  
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

//~  lemma MergeLeafPreservesWF(oldleaf: Node, leftleaf: Node, rightleaf: Node, pivot: Key)
//~    requires WF(leftleaf)
//~    requires WF(rightleaf)
//~    requires SplitLeaf(oldleaf, leftleaf, rightleaf, pivot)
//~    ensures WF(oldleaf)
//~  {
//~    forall i, j | 0 <= i < j < |oldleaf.keys|
//~      ensures Keys.lt(oldleaf.keys[i], oldleaf.keys[j])
//~    {
//~      if j < |leftleaf.keys| {
//~        Keys.IsStrictlySortedImpliesLt(leftleaf.keys, i, j);
//~      } else if i < |leftleaf.keys| {
//~        Keys.IsStrictlySortedImpliesLte(leftleaf.keys, i, |leftleaf.keys|-1);
//~        Keys.IsStrictlySortedImpliesLte(rightleaf.keys, 0, j - |leftleaf.keys|);
//~      } else {
//~        Keys.IsStrictlySortedImpliesLt(rightleaf.keys, i - |leftleaf.keys|, j - |leftleaf.keys|);
//~      }
//~    }
//~    Keys.reveal_IsStrictlySorted();
//~  }
  
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
  
//~  lemma MergeIndexPreservesWF(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
//~    requires WF(leftindex)
//~    requires WF(rightindex)
//~    requires SplitIndex(oldindex, leftindex, rightindex, pivot)
//~    ensures WF(oldindex)
//~  {
//~    forall i, j | 0 <= i < j < |oldindex.pivots|
//~      ensures Keys.lt(oldindex.pivots[i], oldindex.pivots[j])
//~    {
//~      if j < |leftindex.pivots| {
//~        Keys.IsStrictlySortedImpliesLt(leftindex.pivots, i, j);
//~      } else if j == |leftindex.pivots| {
//~        Keys.IsStrictlySortedImpliesLte(leftindex.pivots, i, j-1);
//~        assert AllKeysAboveBound(leftindex, j);
//~      } else if i <  |leftindex.pivots| {
//~        Keys.IsStrictlySortedImpliesLte(leftindex.pivots, i, |leftindex.pivots|-1);
//~        assert AllKeysAboveBound(leftindex, |leftindex.pivots|);
//~        var lwit :| lwit in AllKeys(Last(leftindex.children));
//~        var rwit :| rwit in AllKeys(rightindex.children[0]);
//~        assert AllKeysBelowBound(rightindex, 0);
//~        Keys.IsStrictlySortedImpliesLte(rightindex.pivots, 0, j - |leftindex.children|);
//~      } else if i == |leftindex.pivots| {
//~        assert AllKeysBelowBound(rightindex, 0);
//~        Keys.IsStrictlySortedImpliesLte(rightindex.pivots, 0, j - |leftindex.children|);
//~      } else {
//~        Keys.IsStrictlySortedImpliesLt(rightindex.pivots, i - |leftindex.children|, j - |leftindex.children|);
//~      }
//~    }
//~    Keys.reveal_IsStrictlySorted();
//~
//~    forall i | 0 <= i < |oldindex.children|-1
//~      ensures AllKeysBelowBound(oldindex, i)
//~    {
//~      if i < |leftindex.children|-1 {
//~        assert AllKeysBelowBound(leftindex, i);
//~      } else if i == |leftindex.children|-1 {
//~      } else {
//~        assert AllKeysBelowBound(rightindex, i - |leftindex.children|);
//~      }
//~    }
//~    forall i | 0 < i < |oldindex.children|
//~      ensures AllKeysAboveBound(oldindex, i)
//~    {
//~      if i < |leftindex.children| {
//~        assert AllKeysAboveBound(leftindex, i);
//~      } else if i == |leftindex.children| {
//~      } else {
//~        assert AllKeysAboveBound(rightindex, i - |leftindex.children|);
//~      }
//~    }
//~    assert WF(oldindex);
//~  }
  
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

    //Keys.PosEqLargestLte(oldindex.pivots, pivot, |leftindex.pivots|);

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

    //Keys.PosEqLargestLte(oldindex.pivots, pivot, |leftindex.pivots|);

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
    
//~  lemma MergeNodePreservesWF(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
//~    requires SplitNode(oldnode, leftnode, rightnode, pivot)
//~    requires WF(leftnode)
//~    requires WF(rightnode)
//~    ensures WF(oldnode)
//~  {
//~    if SplitLeaf(oldnode, leftnode, rightnode, pivot) {
//~      MergeLeafPreservesWF(oldnode, leftnode, rightnode, pivot);
//~    } else {
//~      MergeIndexPreservesWF(oldnode, leftnode, rightnode, pivot);
//~    }
//~  }
    
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
    && |newindex.children| == |oldindex.children| + 1 // FIXME: WTF?  Dafny can't get these from WF?
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

//~  lemma MergeChildOfIndexPreservesWF(oldindex: Node, newindex: Node, childidx: int)
//~    requires WF(newindex)
//~    requires SplitChildOfIndex(oldindex, newindex, childidx)
//~    ensures WF(oldindex)
//~  {
//~    assert Keys.IsStrictlySorted(oldindex.pivots) by { Keys.reveal_IsStrictlySorted(); }
//~    forall i | 0 <= i < |oldindex.children|
//~      ensures WF(oldindex.children[i])
//~    {
//~      if i < childidx {
//~      } else if i == childidx {
//~        MergeNodePreservesWF(oldindex.children[childidx],
//~          newindex.children[childidx], newindex.children[childidx+1], newindex.pivots[childidx]);
//~      } else {
//~      }
//~    }
//~    forall i | 0 <= i < |oldindex.children|-1
//~      ensures AllKeysBelowBound(oldindex, i)
//~    {
//~      if i < childidx {
//~        assert AllKeysBelowBound(newindex, i);
//~      } else if i == childidx {
//~        SplitNodeAllKeys(oldindex.children[childidx],
//~          newindex.children[childidx], newindex.children[childidx+1], newindex.pivots[childidx]);
//~        assert AllKeysBelowBound(newindex, childidx);
//~        assert AllKeysBelowBound(newindex, childidx+1);
//~        Keys.IsStrictlySortedImpliesLt(newindex.pivots, childidx, childidx + 1);
//~      } else {
//~        assert AllKeysBelowBound(newindex, i+1);
//~      }
//~    }
//~    forall i | 0 < i < |oldindex.children|
//~      ensures AllKeysAboveBound(oldindex, i)
//~    {
//~      if i < childidx {
//~        assert AllKeysAboveBound(newindex, i);
//~      } else if i == childidx {
//~        SplitNodeAllKeys(oldindex.children[childidx],
//~          newindex.children[childidx], newindex.children[childidx+1], newindex.pivots[childidx]);
//~        Keys.IsStrictlySortedImpliesLt(newindex.pivots, childidx-1, childidx);
//~        forall key | key in AllKeys(oldindex.children[childidx])
//~          ensures Keys.lte(oldindex.pivots[childidx-1], key)
//~        {
//~          if key in AllKeys(newindex.children[childidx]) {
//~            assert AllKeysAboveBound(newindex, childidx);
//~          } else if key == newindex.pivots[childidx] {
//~            Keys.IsStrictlySortedImpliesLt(newindex.pivots, childidx-1, childidx);
//~          } else {
//~            assert key in AllKeys(newindex.children[childidx+1]);
//~            assert AllKeysAboveBound(newindex, childidx+1);
//~          }
//~        }
//~      } else {
//~        assert AllKeysAboveBound(newindex, i+1);
//~      }
//~    }
//~  }
  
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
  
  lemma SplitChildOfIndexPreservesInterpretationA(oldindex: Node, newindex: Node, childidx: int)
    requires WF(oldindex);
    requires WF(newindex);
    requires SplitChildOfIndex(oldindex, newindex, childidx)
    ensures forall key :: key in Interpretation(oldindex) ==> MapsTo(Interpretation(newindex), key, Interpretation(oldindex)[key])
  {
    reveal_Interpretation();
    var newint := Interpretation(newindex);
    var oldint := Interpretation(oldindex);

    // WTF?  These speed up verification a bit for god knows why.
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

    // WTF?  Dafny can't see these (from emacs flycheck mode)
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
    //ensures forall key :: key in Interpretation(newindex) ==> key in Interpretation(oldindex)
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

  // Used in splitting a tree into two trees.
//~  lemma ReplacePivotIsCorrect(node: Node, pivotidx: int, pivot: Key)
//~    requires WF(node)
//~    requires node.Index?
//~    requires 0 <= pivotidx < |node.pivots|
//~    requires forall key :: key in AllKeys(node.children[pivotidx]) ==> Keys.lt(key, pivot)
//~    requires forall key :: key in AllKeys(node.children[pivotidx+1]) ==> Keys.lte(pivot, key)
//~    ensures WF(ReplacePivot(node, pivotidx, pivot))
//~    ensures Interpretation(ReplacePivot(node, pivotidx, pivot)) == Interpretation(node)
//~    ensures AllKeys(ReplacePivot(node, pivotidx, pivot)) <= AllKeys(node) + {pivot}
//~  {
//~    reveal_Interpretation();
//~    reveal_AllKeys();
//~    var newnode := ReplacePivot(node, pivotidx, pivot);
//~    
//~    if pivotidx < |node.pivots|-1 {
//~      var wit :| wit in AllKeys(node.children[pivotidx+1]);
//~      assert AllKeysBelowBound(node, pivotidx+1);
//~      assert Keys.lte(pivot, wit);
//~      assert Keys.lt(pivot, node.pivots[pivotidx+1]);
//~    }
//~    if 0 < pivotidx {
//~      var wit :| wit in AllKeys(node.children[pivotidx]);
//~      assert AllKeysAboveBound(node, pivotidx);
//~      assert Keys.lt(wit, pivot);
//~      assert Keys.lt(node.pivots[pivotidx-1], pivot);
//~    }
//~    Keys.strictlySortedReplace(node.pivots, pivot, pivotidx);
//~    
//~    forall i | 0 <= i < |newnode.children|-1
//~      ensures AllKeysBelowBound(newnode, i)
//~    {
//~      assert AllKeysBelowBound(node, i);
//~    }
//~    forall i | 0 < i < |newnode.children|
//~      ensures AllKeysAboveBound(newnode, i)
//~    {
//~      assert AllKeysAboveBound(node, i);
//~    }
//~
//~    forall key | key in Interpretation(node)
//~      ensures MapsTo(Interpretation(newnode), key, Interpretation(node)[key])
//~    {
//~      var childidx := Keys.LargestLte(node.pivots, key) + 1;
//~      InterpretationInheritance(node, key);
//~      Keys.LargestLteIsUnique2(newnode.pivots, key, childidx-1);
//~      InterpretationDelegation(newnode, key);
//~    }
//~    forall key | key in Interpretation(newnode)
//~      ensures key in Interpretation(node)
//~    {
//~      var childidx := Keys.LargestLte(newnode.pivots, key) + 1;
//~      InterpretationInheritance(newnode, key);
//~      AllKeysIsConsistentWithInterpretation(newnode, key);
//~      if childidx < |newnode.pivots| {
//~        assert AllKeysBelowBound(newnode, childidx);
//~      }
//~      assert AllKeysBelowBound(node, pivotidx);
//~      if 0 <= childidx - 1 {
//~        assert AllKeysAboveBound(node, childidx);
//~      }
//~      Keys.LargestLteIsUnique2(node.pivots, key, childidx-1);
//~      assert key in AllKeys(node);
//~    }
//~  }

//~  lemma IncreasePivotIsCorrect(node: Node, pivotidx: int, pivot: Key)
//~    requires WF(node)
//~    requires node.Index?
//~    requires 0 <= pivotidx < |node.pivots|
//~    requires Keys.lte(node.pivots[pivotidx], pivot)
//~    requires forall key :: key in AllKeys(node.children[pivotidx+1]) ==> Keys.lte(pivot, key)
//~    ensures WF(ReplacePivot(node, pivotidx, pivot))
//~    ensures Interpretation(ReplacePivot(node, pivotidx, pivot)) == Interpretation(node)
//~    ensures AllKeys(ReplacePivot(node, pivotidx, pivot)) <= AllKeys(node) + {pivot}
//~  {
//~    forall key | key in AllKeys(node.children[pivotidx])
//~    ensures Keys.lt(key, pivot)
//~    {
//~      assert AllKeysBelowBound(node, pivotidx);
//~    }
//~    ReplacePivotIsCorrect(node, pivotidx, pivot);
//~  }
  
//~  lemma DecreasePivotIsCorrect(node: Node, pivotidx: int, pivot: Key)
//~    requires WF(node)
//~    requires node.Index?
//~    requires 0 <= pivotidx < |node.pivots|
//~    requires forall key :: key in AllKeys(node.children[pivotidx]) ==> Keys.lt(key, pivot)
//~    requires Keys.lte(pivot, node.pivots[pivotidx])
//~    ensures WF(ReplacePivot(node, pivotidx, pivot))
//~    ensures Interpretation(ReplacePivot(node, pivotidx, pivot)) == Interpretation(node)
//~    ensures AllKeys(ReplacePivot(node, pivotidx, pivot)) <= AllKeys(node) + {pivot}
//~  {
//~    //requires forall key :: key in AllKeys(node.children[pivotidx+1]) ==> Keys.lte(pivot, key)
//~    forall key | key in AllKeys(node.children[pivotidx+1])
//~    ensures Keys.lte(pivot, key)
//~    {
//~      assert AllKeysAboveBound(node, pivotidx+1);
//~    }
//~    ReplacePivotIsCorrect(node, pivotidx, pivot);
//~  }

  // lemma IncreasePivotIsCorrect(node: Node, pivotidx: int, pivot: Key)
  //   requires WF(node)
  //   requires node.Index?
  //   requires 0 <= pivotidx < |node.pivots|
  //   requires Keys.lte(node.pivots[pivotidx], pivot)
  //   requires forall key :: key in AllKeys(node.children[pivotidx+1]) ==> Keys.lte(pivot, key)
  //   ensures WF(ReplacePivot(node, pivotidx, pivot))
  //   ensures Interpretation(ReplacePivot(node, pivotidx, pivot)) == Interpretation(node)
  //   ensures AllKeys(ReplacePivot(node, pivotidx, pivot)) <= AllKeys(node) + {pivot}
  // {
  //   forall key | key in AllKeys(node.children[pivotidx])
  //   ensures Keys.lt(key, pivot)
  //   {
  //     assert AllKeysBelowBound(node, pivotidx);
  //   }
  //   ReplacePivotIsCorrect(node, pivotidx, pivot);
  // }
  // 
  // lemma DecreasePivotIsCorrect(node: Node, pivotidx: int, pivot: Key)
  //   requires WF(node)
  //   requires node.Index?
  //   requires 0 <= pivotidx < |node.pivots|
  //   requires forall key :: key in AllKeys(node.children[pivotidx]) ==> Keys.lt(key, pivot)
  //   requires Keys.lte(pivot, node.pivots[pivotidx])
  //   ensures WF(ReplacePivot(node, pivotidx, pivot))
  //   ensures Interpretation(ReplacePivot(node, pivotidx, pivot)) == Interpretation(node)
  //   ensures AllKeys(ReplacePivot(node, pivotidx, pivot)) <= AllKeys(node) + {pivot}
  // {
  //   //requires forall key :: key in AllKeys(node.children[pivotidx+1]) ==> Keys.lte(pivot, key)
  //   forall key | key in AllKeys(node.children[pivotidx+1])
  //   ensures Keys.lte(pivot, key)
  //   {
  //     assert AllKeysAboveBound(node, pivotidx+1);
  //   }
  //   ReplacePivotIsCorrect(node, pivotidx, pivot);
  // }

//~  lemma AppendChildPreservesWF(oldparent: Node, newparent: Node)
//~    requires WF(oldparent)
//~    requires AppendChild(oldparent, newparent)
//~    requires WF(Last(newparent.children))
//~    requires AllKeys(Last(newparent.children)) != {}
//~    ensures WF(newparent)
//~  {
//~    Keys.StrictlySortedAugment(oldparent.pivots, Last(newparent.pivots));
//~    forall i | 0 <= i < |newparent.children|-1
//~      ensures AllKeysBelowBound(newparent, i)
//~    {
//~      if i < |newparent.children|-2 {
//~        assert AllKeysBelowBound(oldparent, i);
//~      } else {
//~      }
//~    }
//~    forall i | 0 < i < |newparent.children|
//~      ensures AllKeysAboveBound(newparent, i)
//~    {
//~      if i < |newparent.children|-1 {
//~        assert AllKeysAboveBound(oldparent, i);
//~      } else {
//~      }
//~    }
//~    assert WF(newparent);
//~  }

//~  lemma AppendChildAllKeys(oldparent: Node, newparent: Node)
//~    requires WF(oldparent)
//~    requires WF(newparent)
//~    requires AppendChild(oldparent, newparent)
//~    ensures AllKeys(newparent) ==
//~      AllKeys(oldparent) + {Last(newparent.pivots)} + AllKeys(Last(newparent.children))
//~  {
//~    var newkeys := AllKeys(newparent);
//~    var oldkeys := AllKeys(oldparent);
//~    var equivkeys := oldkeys + {Last(newparent.pivots)} + AllKeys(Last(newparent.children));
//~    forall key | key in newkeys
//~      ensures key in equivkeys
//~    {
//~      reveal_AllKeys();
//~      if i :| 0 <= i < |newparent.pivots| && key == newparent.pivots[i] {
//~      } else {
//~        var i :| 0 <= i < |newparent.children| && key in AllKeys(newparent.children[i]);
//~      }
//~    }
//~    forall key | key in equivkeys
//~      ensures key in newkeys
//~    {
//~      reveal_AllKeys();
//~      if key in AllKeys(oldparent) {
//~        if i :| 0 <= i < |oldparent.pivots| && key == oldparent.pivots[i] {
//~        } else {
//~          var i :| 0 <= i < |oldparent.children| && key in AllKeys(oldparent.children[i]);
//~          assert key in AllKeys(newparent.children[i]);
//~        }
//~      } else if key == Last(newparent.pivots) {
//~      } else {
//~      }
//~    }
//~  }
  
//~  lemma AppendChildInterpretation(oldparent: Node, newparent: Node)
//~    requires WF(oldparent)
//~    requires WF(newparent)
//~    requires AppendChild(oldparent, newparent)
//~    ensures Interpretation(newparent) ==
//~    Maps.MapUnion(Interpretation(oldparent), Interpretation(Last(newparent.children)))
//~  {
//~    AppendChildAllKeys(oldparent, newparent);
//~    var newinterp := Interpretation(newparent);
//~    var oldinterp := Interpretation(oldparent);
//~    var childinterp := Interpretation(Last(newparent.children));
//~    var equivinterp := Maps.MapUnion(oldinterp, childinterp);
//~    
//~    forall key | key in newinterp
//~      ensures MapsTo(equivinterp, key, newinterp[key])
//~    {
//~      var i := Keys.LargestLte(newparent.pivots, key) + 1;
//~      if i < |oldparent.children| {
//~        InterpretationInheritance(newparent, key);
//~        assert 0 <= i-1 ==> oldparent.pivots[i-1] == newparent.pivots[i-1];
//~        assert i-1 < |oldparent.pivots|-1 ==> oldparent.pivots[i] == newparent.pivots[i];
//~        Keys.LargestLteIsUnique2(oldparent.pivots, key, i-1);
//~        InterpretationDelegation(oldparent, key);
//~        AllKeysIsConsistentWithInterpretation(newparent.children[i], key);
//~        assert AllKeysBelowBound(newparent, i);
//~        Keys.IsStrictlySortedImpliesLte(newparent.pivots, i, |newparent.pivots|-1);
//~        assert AllKeysAboveBound(newparent, |newparent.children|-1);
//~        assert key !in AllKeys(Last(newparent.children));
//~        if key in childinterp {
//~          AllKeysIsConsistentWithInterpretation(Last(newparent.children), key);
//~          assert false;
//~        }
//~      } else {
//~        InterpretationInheritance(newparent, key);
//~        assert MapsTo(childinterp, key, newinterp[key]);
//~        assert Keys.LargestLte(oldparent.pivots, key) == |oldparent.pivots|-1;
//~        assert AllKeysBelowBound(newparent, |oldparent.pivots|);
//~        assert key !in AllKeys(Last(oldparent.children));
//~        if key in oldinterp {
//~          InterpretationInheritance(oldparent, key);
//~          assert key in Interpretation(Last(oldparent.children));
//~          AllKeysIsConsistentWithInterpretation(Last(oldparent.children), key);
//~          assert false;
//~        }
//~      }
//~    }
//~
//~    forall key | key in equivinterp
//~      ensures key in newinterp
//~    {
//~      if key in oldinterp {
//~        InterpretationInheritance(oldparent, key);
//~        var i := Keys.LargestLte(oldparent.pivots, key) + 1;
//~        if i == |oldparent.children| - 1 {
//~          AllKeysIsConsistentWithInterpretation(Last(oldparent.children), key);
//~        }
//~        Keys.LargestLteIsUnique2(newparent.pivots, key, i-1);
//~        InterpretationDelegation(newparent, key);
//~      } else {
//~        assert key in childinterp;
//~        AllKeysIsConsistentWithInterpretation(Last(newparent.children), key);
//~        assert AllKeysAboveBound(newparent, |newparent.children|-1);
//~        Keys.LargestLteIsUnique2(newparent.pivots, key, |newparent.pivots|-1);
//~        InterpretationDelegation(newparent, key);
//~      }
//~    }
//~  }
  
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
    // ensures Interpretation(node) ==
    //   MapDisjointUnion(Interpretation(SubIndex(node, 0, |node.children|-1)),
    //                    Interpretation(Last(lseqs(node.children))))
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
        //Keys.IsStrictlySortedImpliesLte(node.pivots, childidx, |node.pivots|-1);
        AllKeysIsConsistentWithInterpretation(rightchild, key);
        assert AllKeysAboveBound(node, |node.children|-1);
      }
    }
    if Interpretation(left).Keys * Interpretation(rightchild).Keys != {} {
      assert false;
    }
    assert Interpretation(left).Keys !! Interpretation(rightchild).Keys;
    //assert Interpretation(node) == MapDisjointUnion(Interpretation(left), Interpretation(rightchild));
  }

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
    calc {
      lseqs(right.children);
      lseqs(SubIndex(node, |left.children|, |node.children|).children);
    }
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
        //NumElements(parent);
        //NumElementsOfChildren(nodes);
        //NumElements(nodes[0]);
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
        //NumElementsOfChildren(left.children) + NumElements(right.children[0]);
        //|Interpretation(left)| + |Interpretation(right)|;
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
    //requires forall i :: 0 <= i < |nodes| ==> 0 < NumElements(nodes[i])
    requires 0 <= prefix <= |nodes|
    ensures NumElementsOfChildren(nodes[..prefix]) <= NumElementsOfChildren(nodes)
    //ensures prefix < |nodes| ==> NumElementsOfChildren(nodes[..prefix]) < NumElementsOfChildren(nodes)
  {
    if prefix == |nodes| {
      assert nodes[..prefix] == nodes;
    } else {
      NumElementsOfChildrenDecreases(DropLast(nodes), prefix);
      assert DropLast(nodes)[..prefix] == nodes[..prefix];
    }
  }

  // lemma NumElementsMatchesInterpretation(node: Node)
  //   requires WF(node)
  //   ensures NumElements(node) == |Interpretation(node)|
  // {
  //   var interp := Interpretation(node);
  //   reveal_Interpretation();
  //   if node.Leaf? {
  //     assert NoDupes(node.keys) by {
  //       reveal_NoDupes();
  //       Keys.reveal_IsStrictlySorted();
  //     }
  //     NoDupesSetCardinality(node.keys);
  //     assert interp.Keys == Set(node.keys);
  //   } else if |node.children| == 1 {
  //     var child := node.children[0];
  //     var ichild := Interpretation(child);
  //     forall key | key in ichild
  //       ensures MapsTo(interp, key, ichild[key])
  //     {
  //       AllKeysIsConsistentWithInterpretation(child, key);
  //       reveal_AllKeys();
  //     }
  //     assert interp == Interpretation(child);
  //     NumElementsMatchesInterpretation(child);
  //     assert NumElementsOfChildren(node.children) == NumElements(child);
  //   } else {
  //     var prefix := SubIndex(node, 0, |node.children|-1);
  //     SubIndexPreservesWF(node, 0, |node.children|-1);
  //     var iprefix := Interpretation(prefix);
  //     var child := Last(lseqs(node.children));
  //     var ichild := Interpretation(child);
  //     
  //     assume iprefix.Keys !! ichild.Keys;
  //     assume false;
  //     //assert interp == MapDisjointUnion(iprefix, ichild);
  //   }
  // }
  // 
  // lemma NumElementsOfChildrenNotZero(node: Node)
  //   requires WF(node)
  //   requires node.Index?
  //   ensures forall child :: 0 <= child < |node.children| ==> 0 < NumElements(node.children[child])
  // {
  //   forall child | 0 <= child < |node.children|
  //     ensures 0 < NumElements(node.children[child])
  //   {
  //     reveal_AllKeys();
  //     if node.children[child].Leaf? {
  //     } else {
  //       NumElementsOfChildrenNotZero(node.children[child]);
  //     }
  //   }
  // }
  // 
  // lemma NumElementsOfChildrenDecreases(nodes: seq<Node>, prefix: int)
  //   requires forall i :: 0 <= i < |nodes| ==> WF(nodes[i])
  //   //requires forall i :: 0 <= i < |nodes| ==> 0 < NumElements(nodes[i])
  //   requires 0 <= prefix <= |nodes|
  //   ensures NumElementsOfChildren(nodes[..prefix]) <= NumElementsOfChildren(nodes)
  //   //ensures prefix < |nodes| ==> NumElementsOfChildren(nodes[..prefix]) < NumElementsOfChildren(nodes)
  // {
  //   if prefix == |nodes| {
  //     assert nodes[..prefix] == nodes;
  //   } else {
  //     NumElementsOfChildrenDecreases(DropLast(nodes), prefix);
  //     assert DropLast(nodes)[..prefix] == nodes[..prefix];
  //   }
  // }

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
  
//~  lemma ToSeqIsSortedSeqForInterpretation(node: Node)
//~    requires WF(node)
//~    ensures Keys.SortedSeqForMap(Zip(ToSeq(node).0, ToSeq(node).1), Interpretation(node))
//~  {
//~    reveal_Interpretation();
//~    ToSeqIsStrictlySorted(node);
//~    ToSeqInInterpretation(node);
//~    ToSeqCoversInterpretation(node);
//~    Keys.reveal_SortedSeqForMap();
//~
//~    var (keys, values) := ToSeq(node);
//~    var kvlist := Zip(keys, values);
//~    assert keys == Unzip(kvlist).0;
//~  }

  // predicate ValidBoundariesForSeqInner(nkeys: int, boundaries: seq<nat>)
  // {
  //   && 1 < |boundaries|
  //   && boundaries[0] == 0
  //   && Last(boundaries) == nkeys
  //   && Integer_Order.IsStrictlySorted(boundaries)
  // }

  // lemma ValidBoundariesForSeqBounds(nkeys: int, boundaries: seq<nat>)
  //   ensures ValidBoundariesForSeqInner(nkeys, boundaries) ==>
  //   && (forall i :: 0 <= i < |boundaries|-1 ==> boundaries[i] < nkeys)
  //   && (forall i :: 1 <= i < |boundaries| ==> 0 < boundaries[i])
  // {
  //   if ValidBoundariesForSeqInner(nkeys, boundaries) {
  //     forall i | 0 <= i < |boundaries|-1
  //       ensures boundaries[i] < nkeys
  //     {
  //       Integer_Order.IsStrictlySortedImpliesLt(boundaries, i, |boundaries|-1);
  //     }
  //     forall i | 1 <= i < |boundaries|
  //       ensures 0 < boundaries[i]
  //     {
  //       Integer_Order.IsStrictlySortedImpliesLt(boundaries, 0, i);
  //     }
  //   }
  // }

  // predicate ValidBoundariesForSeq(nkeys: int, boundaries: seq<nat>)
  //   ensures ValidBoundariesForSeq(nkeys, boundaries) ==>
  //   && (forall i :: 0 <= i < |boundaries|-1 ==> boundaries[i] < nkeys)
  //   && (forall i :: 1 <= i < |boundaries| ==> 0 < boundaries[i])
  // {
  //   ValidBoundariesForSeqBounds(nkeys, boundaries);
  //   ValidBoundariesForSeqInner(nkeys, boundaries)
  // }
  
  // lemma ValidBoundaryLength(nkeys: int, boundaries: seq<nat>)
  //   requires ValidBoundariesForSeq(nkeys, boundaries)
  //   ensures |boundaries| <= nkeys + 1
  // {
  //   var i := 0;
  //   while i < |boundaries|-1
  //     invariant i <= |boundaries|-1
  //     invariant i <= boundaries[i]
  //   {
  //     Integer_Order.IsStrictlySortedImpliesLt(boundaries, i, i+1);
  //     i := i + 1;
  //   }
  // }
  
  // function {:opaque} ExtractBoundedSubsequence<T>(things: seq<T>, boundaries: seq<nat>, i: int) : seq<T>
  //   requires ValidBoundariesForSeq(|things|, boundaries)
  //   requires 0 <= i < |boundaries|-1
  // {
  //   assert boundaries[i] <= boundaries[i+1] by
  //   {
  //     Integer_Order.IsStrictlySortedImpliesLte(boundaries, i, i+1);
  //   }
  //   things[boundaries[i]..boundaries[i+1]]
  // }

  // lemma ExtractBoundedSubsequenceLength<T>(things: seq<T>, boundaries: seq<nat>, i: int)
  //   requires ValidBoundariesForSeq(|things|, boundaries)
  //   requires 0 <= i < |boundaries|-1
  //   ensures boundaries[i] <= boundaries[i+1];
  //   ensures |ExtractBoundedSubsequence(things, boundaries, i)| == boundaries[i+1] - boundaries[i]
  // {
  //   reveal_ExtractBoundedSubsequence();
  //   Integer_Order.IsStrictlySortedImpliesLte(boundaries, i, i+1);
  // }
  
  // // lemma ToSeqChildrenOfChildrenFromSeq(keys: seq<Key>, values: seq<Value>, boundaries: seq<nat>, children: seq<Node>)
  // //   requires |keys| == |values|
  // //   requires Keys.IsStrictlySorted(keys)
  // //   requires ValidBoundariesForSeq(|keys|, boundaries)
  // //   requires |boundaries| == |children| + 1
  // //   requires forall i :: 0 <= i < |children| ==> WF(children[i])
  // //   requires forall i :: 0 <= i < |children| ==> ToSeq(children[i]) == (ExtractBoundedSubsequence(keys, boundaries, i), ExtractBoundedSubsequence(values, boundaries, i))
  // //   ensures Flatten(ToSeqChildren(children).0) == keys
  // //   ensures Flatten(ToSeqChildren(children).1) == values
  // // {
  // //   if |children| == 1 {
  // //     ToSeqChildrenDecomposition(children);
  // //   } else {
  // //     var i := 0;
  // //     while i < |children|
  // //       invariant i <= |children|
  // //       invariant Flatten(ToSeqChildren(children[..i]).0) == keys[..boundaries[i]]
  // //       invariant Flatten(ToSeqChildren(children[..i]).1) == values[..boundaries[i]]
  // //     {
  // //       ToSeqChildrenDecomposition(children[..i+1]);
  // //       assert children[..i] == children[..i+1][..i];
  // //       Integer_Order.IsStrictlySortedImpliesLte(boundaries, i, i+1);
  // //       assert keys[..boundaries[i+1]] == keys[..boundaries[i]] + ExtractBoundedSubsequence(keys, boundaries, i);
  // //       assert values[boundaries[i]..boundaries[i+1]] == ExtractBoundedSubsequence(values, boundaries, i);
  // //       assert values[..boundaries[i+1]] == values[..boundaries[i]] + ExtractBoundedSubsequence(values, boundaries, i);
  // //       i := i + 1;
  // //     }
  // //     assert children[..|children|] == children;
  // //     assert keys[..boundaries[|children|]] == keys;
  // //     assert values[..boundaries[|children|]] == values;
  // //   }
  // // }

  // // TODO: generalize KVLists and define equivalence in terms of their
  // // interpretation as maps.  (To handle key-message lists, we can
  // // break the merging process into a sorted-merge step and a
  // // message-amalgamation step.)  (robj)
  // // predicate TreeMatchesKVList(node: Node, kvlist: KVList)
  // //   requires WF(node)
  // //   requires WFKVList(kvlist)
  // // {
  // //   Keys.SortedSeqForMap(Zip(kvlist.keys, kvlist.values), Interpretation(node))
  // // }

  // datatype Configuration = Configuration(ghost maxChildren: nat, ghost maxKeys: nat)

  // predicate ValidConfiguration(config: Configuration)
  // {
  //   && 0 < config.maxKeys
  //   && 1 < config.maxChildren
  // }
    
  // predicate FitsConfig(node: Node, config: Configuration)
  // {
  //   && WF(node)
  //   && (if node.Index? then
  //        && |node.children| <= config.maxChildren
  //        && (forall i :: 0 <= i < |node.children| ==> FitsConfig(node.children[i], config))
  //      else
  //        && |node.keys| <= config.maxKeys
  //     )
  // }

  // datatype KVList = KVList(keys: seq<Key>, values: seq<Value>)
  
  // predicate WFKVList(kvlist: KVList)
  // {
  //   && |kvlist.keys| == |kvlist.values|
  //   && Keys.IsStrictlySorted(kvlist.keys)
  // }

  // function KVListInterpretation(kvlist: KVList) : map<Key, Value>
  //   requires WFKVList(kvlist)
  // {
  //   var keys := Set(kvlist.keys);
  //   map k | k in keys :: kvlist.values[Keys.LargestLte(kvlist.keys, k)]
  // }
  
  // function DropLastPiece<T>(things: seq<T>, boundaries: seq<nat>) : (subthings: seq<T>)
  //   requires 2 < |boundaries|
  //   requires ValidBoundariesForSeq(|things|, boundaries)
  //   ensures ValidBoundariesForSeq(|subthings|, DropLast(boundaries))
  // {
  //   Integer_Order.StrictlySortedSubsequence(boundaries, 0, |boundaries|-1);
  //   things[..boundaries[|boundaries|-2]]
  // }

  // function DropLastKVListPiece(kvlist: KVList, boundaries: seq<nat>) : (sublist: KVList)
  //   requires 2 < |boundaries|
  //   requires WFKVList(kvlist)
  //   requires ValidBoundariesForSeq(|kvlist.keys|, boundaries)
  //   ensures ValidBoundariesForSeq(|sublist.keys|, DropLast(boundaries))
  //   ensures WFKVList(sublist)
  // {
  //   Keys.StrictlySortedSubsequence(kvlist.keys, 0, boundaries[|boundaries|-2]);
  //   KVList(DropLastPiece(kvlist.keys, boundaries), DropLastPiece(kvlist.values, boundaries))
  // }

  // function DropLastPivotsPiece(pivots: seq<Key>, boundaries: seq<nat>) : (subpivots: seq<Key>)
  //   requires 2 < |boundaries|
  //   requires ValidBoundariesForSeq(|pivots| + 1, boundaries)
  //   ensures ValidBoundariesForSeq(|subpivots| + 1, DropLast(boundaries))
  // {
  //   Integer_Order.StrictlySortedSubsequence(boundaries, 0, |boundaries|-1);
  //   pivots[..boundaries[|boundaries|-2] - 1]
  // }
  
  // predicate {:opaque} BoundariesFit(boundaries: seq<nat>, groupSize: nat)
  // {
  //   forall i :: 0 <= i < |boundaries| - 1 ==> boundaries[i+1] - boundaries[i] <= groupSize
  // }
  
  // function {:opaque} BuildBoundariesInner(numthings: nat, groupSize: nat) : (boundaries: seq<nat>)
  //   requires 0 < numthings
  //   requires 0 < groupSize
  // {
  //   var tmp := Apply(i => i * groupSize, Range((numthings + groupSize - 1) / groupSize));
  //   if Last(tmp) == numthings then tmp
  //   else tmp + [numthings]
  // }

  // lemma BuildBoundariesProperties(numthings: nat, groupSize: nat)
  //   requires 0 < numthings
  //   requires 0 < groupSize
  //   ensures ValidBoundariesForSeq(numthings, BuildBoundariesInner(numthings, groupSize))
  //   ensures 1 < numthings && 1 < groupSize ==> |BuildBoundariesInner(numthings, groupSize)| - 1 < numthings
  //   ensures BoundariesFit(BuildBoundariesInner(numthings, groupSize), groupSize)
  // {
  //   reveal_BuildBoundariesInner();
  //   reveal_BoundariesFit();
  //   var tmp := Apply(i => i * groupSize, Range((numthings + groupSize - 1) / groupSize));
  //   forall i, j | 0 <= i < j < |tmp|
  //     ensures tmp[i] < tmp[j]
  //   {
  //     assert i * groupSize < j * groupSize;
  //   }
  //   Integer_Order.reveal_IsStrictlySorted();
  //   if Last(tmp) == numthings {
  //   } else {
  //     Integer_Order.StrictlySortedAugment(tmp, numthings);
  //     if 1 < numthings && 1 < groupSize {
  //       Math.DivCeilLT(numthings, groupSize);
  //     }
  //   }
  // }

  // function BuildBoundaries(numthings: nat, groupSize: nat) : (boundaries: seq<nat>)
  //   requires 0 < numthings
  //   requires 0 < groupSize
  //   ensures ValidBoundariesForSeq(numthings, boundaries)
  //   ensures 1 < numthings && 1 < groupSize ==> |BuildBoundaries(numthings, groupSize)| - 1 < numthings
  //   ensures BoundariesFit(BuildBoundaries(numthings, groupSize), groupSize)
  // {
  //   BuildBoundariesProperties(numthings, groupSize);
  //   BuildBoundariesInner(numthings, groupSize)
  // }

  // function {:opaque} ExtractPivotsForBoundaries(pivots: seq<Key>, boundaries: seq<nat>) : (subpivots: seq<Key>)
  //   requires ValidBoundariesForSeq(|pivots|+1, boundaries)
  //   ensures |subpivots| == |boundaries|-2
  // {
  //   Apply(i
  //         requires 0 <= i < |boundaries|-2
  //         requires ValidBoundariesForSeq(|pivots|+1, boundaries) =>
  //         Integer_Order.IsStrictlySortedImpliesLte(boundaries, i+1, |boundaries|-2);
  //         pivots[boundaries[i+1]-1],
  //         Range(|boundaries|-2))
  // }

  // lemma ExtractPivotsForBoundariesPreservesSort(pivots: seq<Key>, boundaries: seq<nat>)
  //   requires ValidBoundariesForSeq(|pivots|+1, boundaries)
  //   requires Keys.IsStrictlySorted(pivots)
  //   ensures Keys.IsStrictlySorted(ExtractPivotsForBoundaries(pivots, boundaries))
  // {
  //   reveal_ExtractPivotsForBoundaries();
  //   var subpivots := ExtractPivotsForBoundaries(pivots, boundaries);
  //   forall i, j | 0 <= i < j < |subpivots|
  //     ensures Keys.lt(subpivots[i], subpivots[j])
  //   {
  //     var i' := boundaries[i+1]-1;
  //     var j' := boundaries[j+1]-1;
  //     Integer_Order.IsStrictlySortedImpliesLt(boundaries, i+1, j+1);
  //     Keys.IsStrictlySortedImpliesLt(pivots, i', j');
  //   }
  //   Keys.reveal_IsStrictlySorted();
  // }

  // function ExtractPivotsFromKVList(kvlist: KVList) : (pivots: seq<Key>)
  //   requires 0 < |kvlist.keys|
  //   requires WFKVList(kvlist)
  //   ensures Keys.IsStrictlySorted(pivots)
  // {
  //   Keys.StrictlySortedSubsequence(kvlist.keys, 1, |kvlist.keys|);
  //   assert kvlist.keys[1..] == kvlist.keys[1..|kvlist.keys|];
  //   kvlist.keys[1..]
  // }

  // function BuildLeafForSequence(kvlist: KVList, boundaries: seq<nat>, i: nat) : (node: Node)
  //   requires WFKVList(kvlist)
  //   requires ValidBoundariesForSeq(|kvlist.keys|, boundaries)
  //   requires i < |boundaries|-1
  //   ensures WF(node)
  //   ensures AllKeys(node) != {}
  // {
  //   var mykeys := ExtractBoundedSubsequence(kvlist.keys, boundaries, i);
  //   var myvals := ExtractBoundedSubsequence(kvlist.values, boundaries, i);
  //   Integer_Order.IsStrictlySortedImpliesLt(boundaries, i, i+1);
  //   assert 0 < |mykeys| == |myvals| by { reveal_ExtractBoundedSubsequence(); }
  //   assert Keys.IsStrictlySorted(mykeys) by {
  //     reveal_ExtractBoundedSubsequence();
  //     Keys.StrictlySortedSubsequence(kvlist.keys, boundaries[i], boundaries[i+1]);
  //   }
  //   var node := Leaf(mykeys, myvals);
  //   Integer_Order.IsStrictlySortedImpliesLt(boundaries, i, i+1);
  //   Keys.StrictlySortedSubsequence(kvlist.keys, boundaries[i], boundaries[i+1]);
  //   //assert node.keys[0] in AllKeys(node) by { reveal_AllKeys(); }
  //   assert 0 < |node.keys|;
  //   node
  // }

  // function BuildLeavesForSequenceInner(kvlist: KVList, boundaries: seq<nat>, count: nat) : (nodes: seq<Node>)
  //   requires WFKVList(kvlist)
  //   requires ValidBoundariesForSeq(|kvlist.keys|, boundaries)
  //   requires count <= |boundaries|-1
  //   ensures |nodes| == count
  //   ensures forall i :: 0 <= i < |nodes| ==> nodes[i] == BuildLeafForSequence(kvlist, boundaries, i)
  //   decreases count
  // {
  //   if count == 0 then
  //     []
  //   else
  //     BuildLeavesForSequenceInner(kvlist, boundaries, count-1) + [BuildLeafForSequence(kvlist, boundaries, count-1)]
  // }
  
  // function BuildLeavesForSequence(kvlist: KVList, boundaries: seq<nat>) : (nodes: seq<Node>)
  //   requires WFKVList(kvlist)
  //   requires ValidBoundariesForSeq(|kvlist.keys|, boundaries)
  //   ensures |nodes| == |boundaries| - 1
  //   ensures forall i :: 0 <= i < |nodes| ==> nodes[i] == BuildLeafForSequence(kvlist, boundaries, i)
  // {
  //   BuildLeavesForSequenceInner(kvlist, boundaries, |boundaries|-1)
  // }

  // function BuildParent(children: seq<Node>, pivots: seq<Key>, boundaries: seq<nat>, i: nat) : (parent: Node)
  //   requires WF(Index(pivots, children))
  //   requires ValidBoundariesForSeq(|children|, boundaries)
  //   requires 0 <= i < |boundaries|-1
  //   ensures parent.Index?
  //   ensures WF(parent)
  //   ensures AllKeys(parent) != {}
  // {
  //   ValidBoundariesForSeqBounds(|children|, boundaries);
  //   Integer_Order.IsStrictlySortedImpliesLt(boundaries, i, i + 1);
  //   var fparent := Index(pivots, children);
  //   var parent := SubIndex(fparent, boundaries[i], boundaries[i+1]);
  //   SubIndexPreservesWF(fparent, boundaries[i], boundaries[i+1]);
  //   var wit :| wit in AllKeys(children[boundaries[i]]);
  //   assert parent.children[0] == children[boundaries[i]];
  //   assert wit in AllKeys(parent) by { reveal_AllKeys(); }
  //   parent
  // }

  // lemma BuildParentAllKeys(children: seq<Node>, pivots: seq<Key>, boundaries: seq<nat>, i: nat)
  //   requires WF(Index(pivots, children))
  //   requires ValidBoundariesForSeq(|children|, boundaries)
  //   requires 0 <= i < |boundaries|-1
  //   ensures AllKeys(BuildParent(children, pivots, boundaries, i)) <= AllKeys(Index(pivots, children))
  // {
  //   var parent := BuildParent(children, pivots, boundaries, i);
  //   forall key | key in AllKeys(parent)
  //     ensures key in AllKeys(Index(pivots, children))
  //   {
  //     reveal_AllKeys();
  //     if j :| 0 <= j < |parent.pivots| && key == parent.pivots[j] {
  //     } else {
  //       Integer_Order.IsStrictlySortedImpliesLt(boundaries, i, i+1);
  //     }
  //   }
  // }
  
  
  // function BuildParentsInner(children: seq<Node>, pivots: seq<Key>, boundaries: seq<nat>, count: nat) :
  //   (parents: seq<Node>)
  //   requires WF(Index(pivots, children))
  //   requires ValidBoundariesForSeq(|children|, boundaries)
  //   requires 0 <= count <= |boundaries|-1
  //   ensures |parents| == count
  //   ensures forall i :: 0 <= i < |parents| ==> parents[i].Index?
  //   ensures forall i :: 0 <= i < |parents| ==> WF(parents[i])
  //   ensures forall i :: 0 <= i < |parents| ==> AllKeys(parents[i]) != {}
  // {
  //   if count == 0 then
  //     []
  //   else
  //     BuildParentsInner(children, pivots, boundaries, count-1) +
  //     [BuildParent(children, pivots, boundaries, count-1)]
  // }

  // lemma BuildParentsInnerProperties(children: seq<Node>, pivots: seq<Key>, boundaries: seq<nat>, count: nat, parents: seq<Node>)
  //   requires WF(Index(pivots, children))
  //   requires ValidBoundariesForSeq(|children|, boundaries)
  //   requires 0 <= count <= |boundaries|-1
  //   requires parents == BuildParentsInner(children, pivots, boundaries, count)
  //   ensures forall i :: 0 <= i < |parents| ==> boundaries[i] < boundaries[i+1]
  //   ensures forall i :: 0 <= i < |parents| ==> parents[i].pivots == pivots[boundaries[i]..boundaries[i+1]-1];
  //   ensures forall i :: 0 <= i < |parents| ==> parents[i].children == children[boundaries[i]..boundaries[i+1]];
  // {
  //   forall i | 0 <= i < |parents|
  //     ensures boundaries[i] < boundaries[i+1]
  //   {
  //     Integer_Order.IsStrictlySortedImpliesLt(boundaries, i, i+1);
  //   }

  //   if count == 0 {
  //   } else {
  //     BuildParentsInnerProperties(children, pivots, boundaries, count-1, DropLast(parents));
  //   }
  // }

  // function BuildParents(children: seq<Node>, pivots: seq<Key>, boundaries: seq<nat>) :
  //   (parents: seq<Node>)
  //   requires WF(Index(pivots, children))
  //   requires ValidBoundariesForSeq(|children|, boundaries)
  //   ensures forall i :: 0 <= i < |parents| ==> parents[i].Index?
  //   ensures forall i :: 0 <= i < |parents| ==> WF(parents[i])
  //   ensures forall i :: 0 <= i < |parents| ==> AllKeys(parents[i]) != {}
  // {
  //   BuildParentsInner(children, pivots, boundaries, |boundaries| - 1)
  // }

  // function Grandparent(children: seq<Node>, pivots: seq<Key>, boundaries: seq<nat>) : (grandparent: Node)
  //   requires WF(Index(pivots, children))
  //   requires ValidBoundariesForSeq(|children|, boundaries)
  // {
  //   Index(ExtractPivotsForBoundaries(pivots, boundaries), BuildParents(children, pivots, boundaries))
  // }
  
  // lemma GrandparentWF(children: seq<Node>, pivots: seq<Key>, boundaries: seq<nat>)
  //   requires WF(Index(pivots, children))
  //   requires ValidBoundariesForSeq(|children|, boundaries)
  //   ensures WF(Grandparent(children, pivots, boundaries))
  //   //ensures Interpretation(Grandparent(children, pivots, boundaries)) == Interpretation(Index(pivots, children))
  // {
  //   var oldparent := Index(pivots, children);
  //   var grandparent := Grandparent(children, pivots, boundaries);
  //   BuildParentsInnerProperties(children, pivots, boundaries, |boundaries|-1, grandparent.children);
    
  //   ExtractPivotsForBoundariesPreservesSort(pivots, boundaries);
  //   forall i | 0 <= i < |grandparent.children|-1
  //     ensures AllKeysBelowBound(grandparent, i)
  //   {
  //     forall key | key in AllKeys(grandparent.children[i])
  //       ensures Keys.lt(key, grandparent.pivots[i])
  //     {
  //       assert grandparent.pivots[i] == pivots[boundaries[i+1]-1] by { reveal_ExtractPivotsForBoundaries(); }
  //       var parent := grandparent.children[i];
  //       reveal_AllKeys();
  //       if j :| 0 <= j < |parent.pivots| && key == parent.pivots[j] {
  //         Keys.IsStrictlySortedImpliesLt(pivots, boundaries[i] + j, boundaries[i+1]-1);
  //       } else {
  //         var j :| 0 <= j < |parent.children| && key in AllKeys(parent.children[j]);
  //         assert AllKeysBelowBound(oldparent, boundaries[i] + j);
  //         Keys.IsStrictlySortedImpliesLte(pivots, boundaries[i] + j, boundaries[i+1]-1);
  //       }
  //     }
  //   }
  //   forall i | 0 < i < |grandparent.children|
  //     ensures AllKeysAboveBound(grandparent, i)
  //   {
  //     forall key | key in AllKeys(grandparent.children[i])
  //       ensures Keys.lte(grandparent.pivots[i-1], key)
  //     {
  //       assert grandparent.pivots[i-1] == pivots[boundaries[i]-1] by { reveal_ExtractPivotsForBoundaries(); }
  //       var parent := grandparent.children[i];
  //       reveal_AllKeys();
  //       if j :| 0 <= j < |parent.pivots| && key == parent.pivots[j] {
  //         assert boundaries[i] + j < boundaries[i+1];
  //         Keys.IsStrictlySortedImpliesLt(pivots, boundaries[i]-1, boundaries[i] + j);
  //       } else {
  //         var j :| 0 <= j < |parent.children| && key in AllKeys(parent.children[j]);
  //         assert boundaries[i] + j < boundaries[i+1];
  //         assert AllKeysAboveBound(oldparent, boundaries[i] + j);
  //         Keys.IsStrictlySortedImpliesLte(pivots, boundaries[i]-1, boundaries[i] + j-1);
  //       }
  //     }
  //   }
  //   assert WF(grandparent);
  // }

  // lemma GrandparentAllKeys(children: seq<Node>, pivots: seq<Key>, boundaries: seq<nat>)
  //   requires WF(Index(pivots, children))
  //   requires ValidBoundariesForSeq(|children|, boundaries)
  //   ensures AllKeys(Grandparent(children, pivots, boundaries)) == AllKeys(Index(pivots, children))
  // {
  //   var oldparent := Index(pivots, children);
  //   var grandparent := Grandparent(children, pivots, boundaries);
  //   BuildParentsInnerProperties(children, pivots, boundaries, |boundaries|-1, grandparent.children);

  //   var grandak := AllKeys(grandparent);
  //   var oldak := AllKeys(oldparent);
    
  //   forall key | key in grandak
  //     ensures key in oldak
  //   {
  //     reveal_AllKeys();
  //     if j :| 0 <= j < |grandparent.pivots| && key == grandparent.pivots[j] {
  //       assert key == pivots[boundaries[j+1] - 1] by { reveal_ExtractPivotsForBoundaries(); }
  //     } else {
  //       var j :| 0 <= j < |grandparent.children| && key in AllKeys(grandparent.children[j]);
  //       BuildParentAllKeys(children, pivots, boundaries, j);
  //     }
  //   }

  //   forall key | key in oldak
  //     ensures key in grandak
  //   {
  //     reveal_AllKeys();
  //     if j :| 0 <= j < |pivots| && key == pivots[j] {
  //       var i := Integer_Order.LargestLte(boundaries, j);
  //       if j == boundaries[i+1]-1 {
  //         assert key == grandparent.pivots[i] by { reveal_ExtractPivotsForBoundaries(); }
  //       } else {
  //         assert grandparent.children[i].pivots == pivots[boundaries[i]..boundaries[i+1]-1];
  //         assert key == grandparent.children[i].pivots[j - boundaries[i]];
  //         assert key in AllKeys(grandparent.children[i]);
  //       }
  //     } else {
  //       var j :| 0 <= j < |children| && key in AllKeys(children[j]);
  //       var i := Integer_Order.LargestLte(boundaries, j);
  //       assert grandparent.children[i].children == children[boundaries[i]..boundaries[i+1]];
  //       assert key in AllKeys(grandparent.children[i]);
  //     }
  //   }
  // }
  
  // lemma GrandparentInterpretation(children: seq<Node>, pivots: seq<Key>, boundaries: seq<nat>)
  //   requires WF(Index(pivots, children))
  //   requires ValidBoundariesForSeq(|children|, boundaries)
  //   ensures WF(Grandparent(children, pivots, boundaries))
  //   ensures Interpretation(Grandparent(children, pivots, boundaries)) == Interpretation(Index(pivots, children))
  // {
  //   var oldparent := Index(pivots, children);
  //   var grandparent := Grandparent(children, pivots, boundaries);
  //   BuildParentsInnerProperties(children, pivots, boundaries, |boundaries|-1, grandparent.children);
  //   GrandparentWF(children, pivots, boundaries);
    
  //   var grandinterp := Interpretation(grandparent);
  //   var oldinterp := Interpretation(oldparent);

  //   forall key | key in grandinterp
  //     ensures MapsTo(oldinterp, key, grandinterp[key])
  //   {
  //     var i := Keys.LargestLte(grandparent.pivots, key) + 1;
  //     InterpretationInheritance(grandparent, key);
  //     var j := Keys.LargestLte(grandparent.children[i].pivots, key) + 1;
  //     InterpretationInheritance(grandparent.children[i], key);
  //     assert boundaries[i] + j < boundaries[i+1];
  //     assert key in Interpretation(children[boundaries[i] + j]);
  //     AllKeysIsConsistentWithInterpretation(children[boundaries[i] + j], key);
  //     if 0 < boundaries[i] + j {
  //       assert AllKeysAboveBound(oldparent, boundaries[i] + j);
  //     }
  //     if boundaries[i] + j < |children|-1 {
  //       assert AllKeysBelowBound(oldparent, boundaries[i] + j);
  //     }
  //     Keys.LargestLteIsUnique2(pivots, key, boundaries[i] + j - 1);
  //     InterpretationDelegation(oldparent, key);
  //   }
    
  //   forall key | key in oldinterp
  //     ensures key in grandinterp
  //   {
  //     var j := Keys.LargestLte(pivots, key) + 1;
  //     InterpretationInheritance(oldparent, key);
  //     var i := Integer_Order.LargestLte(boundaries, j);
  //     var j' := j - boundaries[i];
  //     AllKeysIsConsistentWithInterpretation(children[j], key);
  //     assert grandparent.children[i].children == children[boundaries[i]..boundaries[i+1]];
  //     assert grandparent.children[i].pivots == pivots[boundaries[i]..boundaries[i+1]-1];
  //     if 0 < j {
  //       assert AllKeysAboveBound(oldparent, j);
  //       assert Keys.lte(pivots[j-1], key);
  //     }
  //     if j' < |grandparent.children[i].pivots| {
  //       assert AllKeysBelowBound(oldparent, j);
  //       assert grandparent.children[i].pivots[j'] == pivots[j];
  //       assert Keys.lt(key, grandparent.children[i].pivots[j']);
  //     }
  //     Keys.LargestLteIsUnique2(grandparent.children[i].pivots, key, j' as int - 1);
  //     InterpretationDelegation(grandparent.children[i], key);

  //     AllKeysIsConsistentWithInterpretation(grandparent.children[i], key);
  //     if 0 < i {
  //       assert AllKeysAboveBound(grandparent, i);
  //     }
  //     if i < |grandparent.children|-1 {
  //       assert AllKeysBelowBound(grandparent, i);
  //     }
  //     Keys.LargestLteIsUnique2(grandparent.pivots, key, i - 1);
  //     InterpretationDelegation(grandparent, key);
  //   }
  // }

  // lemma ParentsFitConfig(children: seq<Node>, pivots: seq<Key>, boundaries: seq<nat>, config: Configuration)
  //   requires WF(Index(pivots, children))
  //   requires ValidBoundariesForSeq(|children|, boundaries)
  //   requires ValidConfiguration(config)
  //   requires forall i :: 0 <= i < |children| ==> FitsConfig(children[i], config)
  //   requires BoundariesFit(boundaries, config.maxChildren)
  //   ensures forall i :: 0 <= i < |BuildParents(children, pivots, boundaries)| ==>
  //     FitsConfig(BuildParents(children, pivots, boundaries)[i], config)
  // {
  //   var parents := BuildParents(children, pivots, boundaries);
  //   BuildParentsInnerProperties(children, pivots, boundaries, |boundaries|-1, parents);
  //   reveal_BoundariesFit();
  //   forall i | 0 <= i < |parents|
  //     ensures FitsConfig(parents[i], config)
  //   {
  //     assert |parents[i].children| == boundaries[i+1] - boundaries[i];
  //   }
  // }

  // // This function clumps node.children together into config-sized parents,
  // // recursing until there's only one node left.
  // function BuildLayers(children: seq<Node>, pivots: seq<Key>, config: Configuration) : (newnode: Node)
  //   requires WF(Index(pivots, children))
  //   requires ValidConfiguration(config)
  //   requires forall i :: 0 <= i < |children| ==> FitsConfig(children[i], config)
  //   ensures WF(newnode)
  //   ensures AllKeys(newnode) == AllKeys(Index(pivots, children))
  //   ensures Interpretation(newnode) == Interpretation(Index(pivots, children))
  //   ensures FitsConfig(newnode, config)
  //   decreases |children|
  // {
  //   reveal_Interpretation();
  //   if |children| == 1  then
  //     GrowPreservesAllKeys(children[0]);
  //     assert children == [children[0]];
  //     GrowPreservesInterpretation(children[0]);
  //     children[0]
  //   else
  //     var boundaries := BuildBoundaries(|children|, config.maxChildren);
  //     var parents := BuildParents(children, pivots, boundaries);
  //     var ppivots := ExtractPivotsForBoundaries(pivots, boundaries);
  //     GrandparentWF(children, pivots, boundaries);
  //     GrandparentAllKeys(children, pivots, boundaries);
  //     GrandparentInterpretation(children, pivots, boundaries);
  //     ParentsFitConfig(children, pivots, boundaries, config);
  //     BuildLayers(parents, ppivots, config)
  // }

  // lemma LeavesProperties(kvlist: KVList, config: Configuration, boundaries: seq<nat>, node: Node)
  //   requires 0 < |kvlist.keys|
  //   requires WFKVList(kvlist)
  //   requires ValidConfiguration(config)
  //   requires boundaries == BuildBoundaries(|kvlist.keys|, config.maxKeys)
  //   requires node.Index?
  //   requires node.children == BuildLeavesForSequence(kvlist, boundaries)
  //   requires node.pivots == ExtractPivotsForBoundaries(ExtractPivotsFromKVList(kvlist), boundaries)
  //   ensures WF(node)
  //   ensures Interpretation(node) == KVListInterpretation(kvlist)
  //   ensures forall i :: 0 <= i < |node.children| ==> FitsConfig(node.children[i], config)
  // {
  //   ExtractPivotsForBoundariesPreservesSort(ExtractPivotsFromKVList(kvlist), boundaries);
  //   reveal_ExtractPivotsForBoundaries();
  //   forall i | 0 <= i < |node.children| - 1
  //     ensures AllKeysBelowBound(node, i)
  //   {
  //     forall j | 0 <= j < |node.children[i].keys|
  //       ensures Keys.lt(node.children[i].keys[j], node.pivots[i])
  //     {
  //       reveal_ExtractBoundedSubsequence();
  //       ExtractBoundedSubsequenceLength(kvlist.keys, boundaries, i);
  //       Keys.IsStrictlySortedImpliesLt(kvlist.keys, boundaries[i] + j, boundaries[i+1]);
  //     }
  //     reveal_AllKeys();
  //   }
  //   forall i | 0 < i < |node.children|
  //     ensures AllKeysAboveBound(node, i)
  //   {
  //     forall j | 0 <= j < |node.children[i].keys|
  //       ensures Keys.lte(node.pivots[i-1], node.children[i].keys[j])
  //     {
  //       reveal_ExtractBoundedSubsequence();
  //       ExtractBoundedSubsequenceLength(kvlist.keys, boundaries, i);
  //       Keys.IsStrictlySortedImpliesLte(kvlist.keys, boundaries[i], boundaries[i] + j);
  //     }
  //     reveal_AllKeys();
  //   }

  //   forall i | 0 <= i < |node.children|
  //     ensures FitsConfig(node.children[i], config)
  //   {
  //     ExtractBoundedSubsequenceLength(kvlist.keys, boundaries, i);
  //     reveal_BoundariesFit();
  //   }
  //   var inode := Interpretation(node);
  //   var ikvlist := KVListInterpretation(kvlist);
  //   forall k | k in inode
  //     ensures MapsTo(ikvlist, k, inode[k])
  //   {
  //     reveal_ExtractBoundedSubsequence();
  //     var childidx := Keys.LargestLte(node.pivots, k) + 1;
  //     var child := node.children[childidx];
  //     InterpretationInheritance(node, k);
  //     assert k in child.keys by { reveal_Interpretation(); }
  //     var j := Keys.LargestLte(child.keys, k);
  //     Keys.PosEqLargestLte(kvlist.keys, k, boundaries[childidx] + j);
  //     assert child.values[j] == inode[k] by { reveal_Interpretation(); }
  //   }

  //   forall k | k in ikvlist
  //     ensures k in inode
  //   {
  //     reveal_ExtractBoundedSubsequence();
  //     var pos := Keys.LargestLte(kvlist.keys, k);
  //     assert 0 <= pos;
  //     var childidx := Integer_Order.LargestLte(boundaries, pos);
  //     assert 0 <= childidx;
  //     var j := pos - boundaries[childidx];
  //     if 0 <= childidx - 1 {
  //     }
  //     if childidx - 1 < |node.pivots|-1 {
  //     }
  //     Keys.LargestLteIsUnique2(node.pivots, k, childidx-1);
  //     assert childidx-1 == Keys.LargestLte(node.pivots, k);
  //     var child := node.children[childidx];
  //     assert child.keys[j] == k;
  //     assert k in Interpretation(child) by { reveal_Interpretation(); }
  //     InterpretationDelegation(node, k);
  //   }
  // }
  
  // function BuildTreeForSequence(kvlist: KVList, config: Configuration) : (node: Node)
  //   requires 0 < |kvlist.keys|
  //   requires WFKVList(kvlist)
  //   requires ValidConfiguration(config)
  //   ensures FitsConfig(node, config)
  //   ensures Interpretation(node) == KVListInterpretation(kvlist)
  // {
  //   var boundaries := BuildBoundaries(|kvlist.keys|, config.maxKeys);
  //   var leaves := BuildLeavesForSequence(kvlist, boundaries);
  //   var pivots := ExtractPivotsForBoundaries(ExtractPivotsFromKVList(kvlist), boundaries);
  //   var node := Index(pivots, leaves);
  //   LeavesProperties(kvlist, config, boundaries, node);
  //   BuildLayers(leaves, pivots, config)
  // }
}

