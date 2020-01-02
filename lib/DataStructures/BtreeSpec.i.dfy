include "../Base/sequences.i.dfy"
include "../Base/Maps.s.dfy"
include "../Base/total_order.i.dfy"
include "../Base/mathematics.i.dfy"

abstract module BtreeSpec {
  import opened Seq = Sequences
  import opened Maps
  import Keys : Total_Order
  import Integer_Order
  import Math = Mathematics
  
  type Key = Keys.Element
  type Value
    
  datatype Node =
    | Leaf(keys: seq<Key>, values: seq<Value>)
    | Index(pivots: seq<Key>, children: seq<Node>)

  function AllKeys(node: Node) : set<Key>
  {
    match node {
      case Leaf(keys, values) => set k | k in keys
      case Index(pivots, children) =>
        (set k | k in pivots)
        +
        (set i, k | 0 <= i < |children| && k in AllKeys(children[i]) :: k)
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

  function Interpretation(node: Node) : map<Key, Value>
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
  }

  lemma InterpretationDelegation(node: Node, key: Key)
    requires WF(node)
    requires node.Index?
    requires key in Interpretation(node.children[Keys.LargestLte(node.pivots, key)+1])
    ensures MapsTo(Interpretation(node), key, Interpretation(node.children[Keys.LargestLte(node.pivots, key)+1])[key])
  {
    var interp := Interpretation(node);
    assert key in interp;
  }
  
  lemma AllKeysIsConsistentWithInterpretation(node: Node, key: Key)
    requires WF(node)
    requires key in Interpretation(node)
    ensures key in AllKeys(node)
    ensures node.Index? ==> WF(node) && key in AllKeys(node.children[Keys.LargestLte(node.pivots, key) + 1])
  {
    if node.Index? {
      assert key in Interpretation(node.children[Keys.LargestLte(node.pivots, key) + 1]);
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
    requires WF(node)
    requires node.Index?
    requires 0 <= from < to <= |node.children|
  {
    Index(node.pivots[from..to-1], node.children[from..to])
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
  }
  
  predicate SplitIndex(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
  {
    && oldindex.Index?
    && leftindex.Index?
    && rightindex.Index?
    && WF(oldindex)
    && 0 < |leftindex.children| < |oldindex.children|
    && leftindex == SubIndex(oldindex, 0, |leftindex.children|)
    && rightindex == SubIndex(oldindex, |leftindex.children|, |oldindex.children|)
    && pivot == oldindex.pivots[|leftindex.pivots|]
  }

  lemma SplitIndexPreservesWF(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
    requires SplitIndex(oldindex, leftindex, rightindex, pivot)
    ensures WF(leftindex)
    ensures WF(rightindex)
  {
    SubIndexPreservesWF(oldindex, 0, |leftindex.children|);
    SubIndexPreservesWF(oldindex, |leftindex.children|, |oldindex.children|);
  }
  
  lemma SplitIndexInterpretation1(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
    requires SplitIndex(oldindex, leftindex, rightindex, pivot)
    requires WF(leftindex)
    requires WF(rightindex)
    ensures forall key :: key in Interpretation(oldindex) ==>
    MapsTo(Keys.MapPivotedUnion(Interpretation(leftindex), pivot, Interpretation(rightindex)), key, Interpretation(oldindex)[key])
  {
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
    }
  }
  
  lemma SplitIndexInterpretation2(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
    requires SplitIndex(oldindex, leftindex, rightindex, pivot)
    requires WF(leftindex)
    requires WF(rightindex)
    ensures Interpretation(oldindex).Keys >=
            Keys.MapPivotedUnion(Interpretation(leftindex), pivot, Interpretation(rightindex)).Keys
  {
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
    }
  }

  lemma SplitIndexInterpretation(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
    requires SplitIndex(oldindex, leftindex, rightindex, pivot)
    requires WF(leftindex)
    requires WF(rightindex)
    ensures Interpretation(oldindex) ==
    Keys.MapPivotedUnion(Interpretation(leftindex), pivot, Interpretation(rightindex))
  {
    SplitIndexInterpretation1(oldindex, leftindex, rightindex, pivot);
    SplitIndexInterpretation2(oldindex, leftindex, rightindex, pivot);
  }

  // TODO: maybe eliminate wit by just requiring pivot to be larger
  // than the lower-bounding pivot in SplitChildOfIndex.
  predicate SplitNode(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
  {
    || SplitLeaf(oldnode, leftnode, rightnode, pivot)
    || SplitIndex(oldnode, leftnode, rightnode, pivot)
  }

  lemma SplitNodePreservesWF(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
    requires WF(oldnode)
    requires SplitNode(oldnode, leftnode, rightnode, pivot)
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
    requires SplitNode(oldnode, leftnode, rightnode, pivot)
    requires WF(oldnode)
    requires WF(leftnode)
    requires WF(rightnode)
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
    requires SplitLeaf(oldnode, leftnode, rightnode, pivot)
    ensures AllKeys(oldnode) == AllKeys(leftnode) + AllKeys(rightnode)
    ensures AllKeys(leftnode) != {}
    ensures AllKeys(rightnode) != {}
    ensures forall key :: key in AllKeys(leftnode) ==> Keys.lt(key, pivot)
    ensures forall key :: key in AllKeys(rightnode) ==> Keys.lte(pivot, key)
  {
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
    requires SplitIndex(oldnode, leftnode, rightnode, pivot)
    ensures AllKeys(oldnode) == AllKeys(leftnode) + AllKeys(rightnode) + {pivot}
    ensures AllKeys(leftnode) != {}
    ensures AllKeys(rightnode) != {}
    ensures forall key :: key in AllKeys(leftnode) ==> Keys.lt(key, pivot)
    ensures forall key :: key in AllKeys(rightnode) ==> Keys.lte(pivot, key)
  {
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
    assert Last(rightnode.children) == Last(oldnode.children);
  }
  
  lemma SplitNodeAllKeys(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
    requires WF(oldnode)
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
    && WF(oldindex)
    && 0 <= childidx < |oldindex.children|
    && |newindex.children| == |oldindex.children| + 1 // FIXME: WTF?  Dafny can't get these from WF?
    && |newindex.pivots| == |oldindex.pivots| + 1
    && |oldindex.pivots| == |oldindex.children| - 1
    && SplitNode(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], newindex.pivots[childidx])
    && newindex.pivots == Seq.insert(oldindex.pivots, newindex.pivots[childidx], childidx)
    && newindex.children == Seq.replace1with2(oldindex.children, newindex.children[childidx], newindex.children[childidx+1], childidx)
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
    SplitNodeAllKeys(oldchild, leftchild, rightchild, pivot);
    SplitNodePreservesWF(oldchild, leftchild, rightchild, pivot);
    assert 0 < childidx ==> AllKeysAboveBound(oldindex, childidx);
    assert childidx < |oldindex.pivots| ==> AllKeysBelowBound(oldindex, childidx);
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
    requires SplitChildOfIndex(oldindex, newindex, childidx)
    ensures AllKeys(newindex) == AllKeys(oldindex) + {newindex.pivots[childidx]}
  {
    assert WF(oldindex);
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
    requires SplitChildOfIndex(oldindex, newindex, childidx)
    requires WF(newindex);
    ensures forall key :: key in Interpretation(oldindex) ==> MapsTo(Interpretation(newindex), key, Interpretation(oldindex)[key])
  {
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
    requires SplitChildOfIndex(oldindex, newindex, childidx)
    requires WF(newindex);
    ensures forall key :: key in Interpretation(newindex) ==> key in Interpretation(oldindex)
      //ensures Interpretation(newindex) == Interpretation(oldindex)
  {
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
      var llte := Keys.LargestLte(newindex.pivots, key);
      if llte + 1 < childidx {
        Keys.LargestLteIsUnique2(oldindex.pivots, key, llte);
      } else if llte + 1 == childidx {
        Keys.LargestLteIsUnique2(oldindex.pivots, key, llte);
      } else if llte + 1 == childidx + 1 {
        var oldllte := llte - 1;
        Keys.LargestLteIsUnique2(oldindex.pivots, key, oldllte);
        assert oldllte == Keys.LargestLte(oldindex.pivots, key);
        assert key in Interpretation(oldindex.children[Keys.LargestLte(oldindex.pivots, key) + 1]);
      } else {
        Keys.LargestLteIsUnique2(oldindex.pivots, key, llte-1);
      }
    }
  }

  lemma SplitChildOfIndexPreservesInterpretation(oldindex: Node, newindex: Node, childidx: int)
    requires SplitChildOfIndex(oldindex, newindex, childidx)
    requires WF(newindex);
    //ensures forall key :: key in Interpretation(newindex) ==> key in Interpretation(oldindex)
    ensures Interpretation(newindex) == Interpretation(oldindex)
  {
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
    requires newnode == node.(children := node.children[pos := newchild])
    requires AllKeys(newchild) <= AllKeys(node.children[pos]) + {key}
    ensures WF(newnode)
    ensures Interpretation(newnode) == Interpretation(node)[key := value]
    ensures AllKeys(newnode) <= AllKeys(node) + {key}
  {
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
    Index([], [node])
  }

  lemma GrowPreservesWF(node: Node)
    requires WF(node)
    requires AllKeys(node) != {}
    ensures WF(Grow(node))
  {
  }

  lemma GrowPreservesInterpretation(node: Node)
    requires WF(node)
    requires AllKeys(node) != {}
    ensures WF(Grow(node))
    ensures Interpretation(Grow(node)) == Interpretation(node)
  {
    var interp := Interpretation(node);
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

  lemma ReplacePivotIsCorrect(node: Node, pivotidx: int, pivot: Key)
    requires WF(node)
    requires node.Index?
    requires 0 <= pivotidx < |node.pivots|
    requires forall key :: key in AllKeys(node.children[pivotidx]) ==> Keys.lt(key, pivot)
    requires forall key :: key in AllKeys(node.children[pivotidx+1]) ==> Keys.lte(pivot, key)
    ensures WF(ReplacePivot(node, pivotidx, pivot))
    ensures Interpretation(ReplacePivot(node, pivotidx, pivot)) == Interpretation(node)
    ensures AllKeys(ReplacePivot(node, pivotidx, pivot)) <= AllKeys(node) + {pivot}
  {
    var newnode := ReplacePivot(node, pivotidx, pivot);
    
    if pivotidx < |node.pivots|-1 {
      var wit :| wit in AllKeys(node.children[pivotidx+1]);
      assert AllKeysBelowBound(node, pivotidx+1);
      assert Keys.lte(pivot, wit);
      assert Keys.lt(pivot, node.pivots[pivotidx+1]);
    }
    if 0 < pivotidx {
      var wit :| wit in AllKeys(node.children[pivotidx]);
      assert AllKeysAboveBound(node, pivotidx);
      assert Keys.lt(wit, pivot);
      assert Keys.lt(node.pivots[pivotidx-1], pivot);
    }
    Keys.strictlySortedReplace(node.pivots, pivot, pivotidx);
    
    forall i | 0 <= i < |newnode.children|-1
      ensures AllKeysBelowBound(newnode, i)
    {
      assert AllKeysBelowBound(node, i);
    }
    forall i | 0 < i < |newnode.children|
      ensures AllKeysAboveBound(newnode, i)
    {
      assert AllKeysAboveBound(node, i);
    }

    forall key | key in Interpretation(node)
      ensures MapsTo(Interpretation(newnode), key, Interpretation(node)[key])
    {
      var childidx := Keys.LargestLte(node.pivots, key) + 1;
      InterpretationInheritance(node, key);
      Keys.LargestLteIsUnique2(newnode.pivots, key, childidx-1);
      InterpretationDelegation(newnode, key);
    }
    forall key | key in Interpretation(newnode)
      ensures key in Interpretation(node)
    {
      var childidx := Keys.LargestLte(newnode.pivots, key) + 1;
      InterpretationInheritance(newnode, key);
      if childidx < |newnode.pivots| {
        assert AllKeysBelowBound(newnode, childidx);
      }
      assert AllKeysBelowBound(node, pivotidx);
      if 0 <= childidx - 1 {
        assert AllKeysAboveBound(node, childidx);
      }
      Keys.LargestLteIsUnique2(node.pivots, key, childidx-1);
    }
  }

  lemma IncreasePivotIsCorrect(node: Node, pivotidx: int, pivot: Key)
    requires WF(node)
    requires node.Index?
    requires 0 <= pivotidx < |node.pivots|
    requires Keys.lte(node.pivots[pivotidx], pivot)
    requires forall key :: key in AllKeys(node.children[pivotidx+1]) ==> Keys.lte(pivot, key)
    ensures WF(ReplacePivot(node, pivotidx, pivot))
    ensures Interpretation(ReplacePivot(node, pivotidx, pivot)) == Interpretation(node)
    ensures AllKeys(ReplacePivot(node, pivotidx, pivot)) <= AllKeys(node) + {pivot}
  {
    forall key | key in AllKeys(node.children[pivotidx])
    ensures Keys.lt(key, pivot)
    {
      assert AllKeysBelowBound(node, pivotidx);
    }
    ReplacePivotIsCorrect(node, pivotidx, pivot);
  }
  
  lemma DecreasePivotIsCorrect(node: Node, pivotidx: int, pivot: Key)
    requires WF(node)
    requires node.Index?
    requires 0 <= pivotidx < |node.pivots|
    requires forall key :: key in AllKeys(node.children[pivotidx]) ==> Keys.lt(key, pivot)
    requires Keys.lte(pivot, node.pivots[pivotidx])
    ensures WF(ReplacePivot(node, pivotidx, pivot))
    ensures Interpretation(ReplacePivot(node, pivotidx, pivot)) == Interpretation(node)
    ensures AllKeys(ReplacePivot(node, pivotidx, pivot)) <= AllKeys(node) + {pivot}
  {
    //requires forall key :: key in AllKeys(node.children[pivotidx+1]) ==> Keys.lte(pivot, key)
    forall key | key in AllKeys(node.children[pivotidx+1])
    ensures Keys.lte(pivot, key)
    {
      assert AllKeysAboveBound(node, pivotidx+1);
    }
    ReplacePivotIsCorrect(node, pivotidx, pivot);
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
    else NumElementsOfChildren(node.children)
  }

  lemma NumElementsOfChildrenNotZero(node: Node)
    requires WF(node)
    requires node.Index?
    ensures forall child :: 0 <= child < |node.children| ==> 0 < NumElements(node.children[child])
  {
    forall child | 0 <= child < |node.children|
      ensures 0 < NumElements(node.children[child])
    {
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
      var (keylists, valuelists) := ToSeqChildren(node.children);
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
      ToSeqChildrenLength(node.children);
    }      
  }

  lemma ToSeqInAllKeys(node: Node)
    requires WF(node)
    ensures forall key :: key in ToSeq(node).0 ==> key in AllKeys(node)
  {
    var (keys, values) := ToSeq(node);
    reveal_ToSeq();
    
    if node.Index? {
      var (childkeys, chilvalues) := ToSeqChildren(node.children);
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
      var (keylists, valuelists) := ToSeqChildren(node.children);
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
      var (keylists, valuelists) := ToSeqChildren(node.children);
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
    var (keys, values) := ToSeq(node);
    var interp := Interpretation(node);
    
    reveal_ToSeq();
    
    if node.Index? {
      var (keylists, valuelists) := ToSeqChildren(node.children);
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

  lemma ToSeqIsSortedSeqForInterpretation(node: Node)
    requires WF(node)
    ensures Keys.SortedSeqForMap(Zip(ToSeq(node).0, ToSeq(node).1), Interpretation(node))
  {
    ToSeqIsStrictlySorted(node);
    ToSeqInInterpretation(node);
    ToSeqCoversInterpretation(node);
    Keys.reveal_SortedSeqForMap();

    var (keys, values) := ToSeq(node);
    var kvlist := Zip(keys, values);
    assert keys == Unzip(kvlist).0;
  }

  predicate ValidBoundariesForSeqInner(nkeys: int, boundaries: seq<nat>)
  {
    && 1 < |boundaries|
    && boundaries[0] == 0
    && Last(boundaries) == nkeys
    && Integer_Order.IsStrictlySorted(boundaries)
  }

  lemma ValidBoundariesForSeqBounds(nkeys: int, boundaries: seq<nat>)
    ensures ValidBoundariesForSeqInner(nkeys, boundaries) ==>
    && (forall i :: 0 <= i < |boundaries|-1 ==> boundaries[i] < nkeys)
    && (forall i :: 1 <= i < |boundaries| ==> 0 < boundaries[i])
  {
    if ValidBoundariesForSeqInner(nkeys, boundaries) {
      forall i | 0 <= i < |boundaries|-1
        ensures boundaries[i] < nkeys
      {
        Integer_Order.IsStrictlySortedImpliesLt(boundaries, i, |boundaries|-1);
      }
      forall i | 1 <= i < |boundaries|
        ensures 0 < boundaries[i]
      {
        Integer_Order.IsStrictlySortedImpliesLt(boundaries, 0, i);
      }
    }
  }

  predicate ValidBoundariesForSeq(nkeys: int, boundaries: seq<nat>)
    ensures ValidBoundariesForSeq(nkeys, boundaries) ==>
    && (forall i :: 0 <= i < |boundaries|-1 ==> boundaries[i] < nkeys)
    && (forall i :: 1 <= i < |boundaries| ==> 0 < boundaries[i])
  {
    ValidBoundariesForSeqBounds(nkeys, boundaries);
    ValidBoundariesForSeqInner(nkeys, boundaries)
  }
  
  lemma ValidBoundaryLength(nkeys: int, boundaries: seq<nat>)
    requires ValidBoundariesForSeq(nkeys, boundaries)
    ensures |boundaries| <= nkeys + 1
  {
    var i := 0;
    while i < |boundaries|-1
      invariant i <= |boundaries|-1
      invariant i <= boundaries[i]
    {
      Integer_Order.IsStrictlySortedImpliesLt(boundaries, i, i+1);
      i := i + 1;
    }
  }
  
  function ExtractBoundedSubsequence<T>(things: seq<T>, boundaries: seq<nat>, i: int) : seq<T>
    requires ValidBoundariesForSeq(|things|, boundaries)
    requires 0 <= i < |boundaries|-1
  {
    assert boundaries[i] <= boundaries[i+1] by
    {
      Integer_Order.IsStrictlySortedImpliesLte(boundaries, i, i+1);
    }
    things[boundaries[i]..boundaries[i+1]]
  }
  
  predicate PivotsMatchBoundaries(keys: seq<Key>, boundaries: seq<nat>, pivots: seq<Key>)
    requires ValidBoundariesForSeq(|keys|, boundaries)
  {
    && |pivots| == |boundaries| - 2
    && (forall i :: 0 <= i < |pivots| ==> pivots[i] == keys[boundaries[i+1]])
  }
  
  lemma BoundaryPivotsStrictlySorted(keys: seq<Key>, boundaries: seq<nat>, pivots: seq<Key>)
    requires Keys.IsStrictlySorted(keys)
    requires ValidBoundariesForSeq(|keys|, boundaries)
    requires PivotsMatchBoundaries(keys, boundaries, pivots)
    ensures Keys.IsStrictlySorted(pivots)
  {
    forall i, j | 0 <= i < j < |pivots|
      ensures Keys.lt(pivots[i], pivots[j])
    {
      Integer_Order.IsStrictlySortedImpliesLt(boundaries, i+1, j+1);
      Keys.IsStrictlySortedImpliesLt(keys, boundaries[i+1], boundaries[j+1]);
    }
    Keys.reveal_IsStrictlySorted();
  }

  predicate LeafMatchesBoundary(keys: seq<Key>, values: seq<Value>, boundaries: seq<nat>, leaf: Node, i: nat)
    requires |keys| == |values|
    requires ValidBoundariesForSeq(|keys|, boundaries)
    requires i + 2 <= |boundaries|
    requires leaf.Leaf?
  {
    && leaf.keys == ExtractBoundedSubsequence(keys, boundaries, i)
    && leaf.values == ExtractBoundedSubsequence(values, boundaries, i)
  }
  
  predicate LeavesMatchBoundaries(keys: seq<Key>, values: seq<Value>, boundaries: seq<nat>, leaves: seq<Node>)
    requires |keys| == |values|
    requires ValidBoundariesForSeq(|keys|, boundaries)
  {
    && |boundaries| == |leaves| + 1
    && (forall i :: 0 <= i < |leaves| ==> leaves[i].Leaf?)
    && (forall i :: 0 <= i < |leaves| ==> leaves[i].keys == ExtractBoundedSubsequence(keys, boundaries, i))
    && (forall i :: 0 <= i < |leaves| ==> leaves[i].values == ExtractBoundedSubsequence(values, boundaries, i))
  }
    
  lemma ToSeqChildrenOfChildrenFromSeq(keys: seq<Key>, values: seq<Value>, boundaries: seq<nat>, children: seq<Node>)
    requires |keys| == |values|
    requires Keys.IsStrictlySorted(keys)
    requires ValidBoundariesForSeq(|keys|, boundaries)
    requires |boundaries| == |children| + 1
    requires forall i :: 0 <= i < |children| ==> WF(children[i])
    requires forall i :: 0 <= i < |children| ==> ToSeq(children[i]) == (ExtractBoundedSubsequence(keys, boundaries, i), ExtractBoundedSubsequence(values, boundaries, i))
    ensures Flatten(ToSeqChildren(children).0) == keys
    ensures Flatten(ToSeqChildren(children).1) == values
  {
    if |children| == 1 {
      ToSeqChildrenDecomposition(children);
    } else {
      var i := 0;
      while i < |children|
        invariant i <= |children|
        invariant Flatten(ToSeqChildren(children[..i]).0) == keys[..boundaries[i]]
        invariant Flatten(ToSeqChildren(children[..i]).1) == values[..boundaries[i]]
      {
        ToSeqChildrenDecomposition(children[..i+1]);
        assert children[..i] == children[..i+1][..i];
        Integer_Order.IsStrictlySortedImpliesLte(boundaries, i, i+1);
        assert keys[..boundaries[i+1]] == keys[..boundaries[i]] + ExtractBoundedSubsequence(keys, boundaries, i);
        assert values[boundaries[i]..boundaries[i+1]] == ExtractBoundedSubsequence(values, boundaries, i);
        assert values[..boundaries[i+1]] == values[..boundaries[i]] + ExtractBoundedSubsequence(values, boundaries, i);
        i := i + 1;
      }
      assert children[..|children|] == children;
      assert keys[..boundaries[|children|]] == keys;
      assert values[..boundaries[|children|]] == values;
    }
  }

  datatype Configuration = Configuration(maxChildren: nat, maxKeys: nat)

  predicate ValidConfiguration(config: Configuration)
  {
    && 0 < config.maxKeys
    && 1 < config.maxChildren
  }
    
  predicate FitsConfig(node: Node, config: Configuration)
  {
    && WF(node)
    && (if node.Index? then
         && |node.children| <= config.maxChildren
         && (forall i :: 0 <= i < |node.children| ==> FitsConfig(node.children[i], config))
       else
         && |node.keys| <= config.maxKeys
      )
  }

  datatype KVList = KVList(keys: seq<Key>, values: seq<Value>)
  
  predicate WFKVList(kvlist: KVList)
  {
    && |kvlist.keys| == |kvlist.values|
    && Keys.IsStrictlySorted(kvlist.keys)
  }

  predicate TreeMatchesKVList(node: Node, kvlist: KVList)
    requires WF(node)
    requires WFKVList(kvlist)
  {
    Keys.SortedSeqForMap(Zip(kvlist.keys, kvlist.values), Interpretation(node))
  }

  function DropLastPiece<T>(things: seq<T>, boundaries: seq<nat>) : (subthings: seq<T>)
    requires 2 < |boundaries|
    requires ValidBoundariesForSeq(|things|, boundaries)
    ensures ValidBoundariesForSeq(|subthings|, DropLast(boundaries))
  {
    Integer_Order.StrictlySortedSubsequence(boundaries, 0, |boundaries|-1);
    things[..boundaries[|boundaries|-2]]
  }

  function DropLastKVListPiece(kvlist: KVList, boundaries: seq<nat>) : (sublist: KVList)
    requires 2 < |boundaries|
    requires WFKVList(kvlist)
    requires ValidBoundariesForSeq(|kvlist.keys|, boundaries)
    ensures ValidBoundariesForSeq(|sublist.keys|, DropLast(boundaries))
    ensures WFKVList(sublist)
  {
    Keys.StrictlySortedSubsequence(kvlist.keys, 0, boundaries[|boundaries|-2]);
    KVList(DropLastPiece(kvlist.keys, boundaries), DropLastPiece(kvlist.values, boundaries))
  }

  function DropLastPivotsPiece(pivots: seq<Key>, boundaries: seq<nat>) : (subpivots: seq<Key>)
    requires 2 < |boundaries|
    requires ValidBoundariesForSeq(|pivots| + 1, boundaries)
    ensures ValidBoundariesForSeq(|subpivots| + 1, DropLast(boundaries))
  {
    Integer_Order.StrictlySortedSubsequence(boundaries, 0, |boundaries|-1);
    pivots[..boundaries[|boundaries|-2] - 1]
  }
  
  function BuildLeafForSequence(kvlist: KVList, boundaries: seq<nat>, i: nat) : (node: Node)
    requires WFKVList(kvlist)
    requires ValidBoundariesForSeq(|kvlist.keys|, boundaries)
    requires i < |boundaries|-1
    ensures WF(node)
  {
    var mykeys := ExtractBoundedSubsequence(kvlist.keys, boundaries, i);
    var myvals := ExtractBoundedSubsequence(kvlist.values, boundaries, i);
    Integer_Order.IsSortedImpliesLte(boundaries, i, i+1);
    Keys.StrictlySortedSubsequence(kvlist.keys, boundaries[i], boundaries[i+1]);
    Leaf(mykeys, myvals)
  }
  
  function BuildLeavesForSequence(kvlist: KVList, boundaries: seq<nat>) : (nodes: seq<Node>)
    requires WFKVList(kvlist)
    requires ValidBoundariesForSeq(|kvlist.keys|, boundaries)
    ensures forall i :: 0 <= i < |nodes| ==> WF(nodes[i])
    decreases |boundaries|
  {
    if |boundaries| == 2 then
      [BuildLeafForSequence(kvlist, boundaries, 0)]
    else
      var subboundaries := DropLast(boundaries);
      var subkvlist := DropLastKVListPiece(kvlist, boundaries);
      BuildLeavesForSequence(subkvlist, subboundaries) + [BuildLeafForSequence(kvlist, boundaries, |boundaries|-2)]
  }

  function {:opaque} ExtractPivotsForBoundaries(pivots: seq<Key>, boundaries: seq<nat>) : (subpivots: seq<Key>)
    requires ValidBoundariesForSeq(|pivots|+1, boundaries)
    ensures |subpivots| == |boundaries|-2
  {
    Apply(i
          requires 0 <= i < |boundaries|-2
          requires ValidBoundariesForSeq(|pivots|+1, boundaries) =>
          Integer_Order.IsStrictlySortedImpliesLte(boundaries, i+1, |boundaries|-2);
          pivots[boundaries[i+1]-1],
          Range(|boundaries|-2))
  }

  lemma ExtractPivotsForBoundariesPreservesSort(pivots: seq<Key>, boundaries: seq<nat>)
    requires ValidBoundariesForSeq(|pivots|+1, boundaries)
    requires Keys.IsStrictlySorted(pivots)
    ensures Keys.IsStrictlySorted(ExtractPivotsForBoundaries(pivots, boundaries))
  {
    reveal_ExtractPivotsForBoundaries();
    var subpivots := ExtractPivotsForBoundaries(pivots, boundaries);
    forall i, j | 0 <= i < j < |subpivots|
      ensures Keys.lt(subpivots[i], subpivots[j])
    {
      var i' := boundaries[i+1]-1;
      var j' := boundaries[j+1]-1;
      Integer_Order.IsStrictlySortedImpliesLt(boundaries, i+1, j+1);
      Keys.IsStrictlySortedImpliesLt(pivots, i', j');
    }
    Keys.reveal_IsStrictlySorted();
  }
  
  function ExtractPivotsFromKVList(kvlist: KVList) : (pivots: seq<Key>)
    requires 0 < |kvlist.keys|
  {
    kvlist.keys[1..]
  }

  function BuildParentForSequenceInner(nodes: seq<Node>, pivots: seq<Key>, boundaries: seq<nat>, i: nat) : (node: Node)
    requires ValidBoundariesForSeq(|nodes|, boundaries)
    requires |pivots| == |nodes|-1
    requires Keys.IsStrictlySorted(pivots)
    requires i < |boundaries|-1
  {
    Integer_Order.IsStrictlySortedImpliesLt(boundaries, i, i+1);
    var mypivots := pivots[boundaries[i]..boundaries[i+1]-1];
    var mychildren := ExtractBoundedSubsequence(nodes, boundaries, i);
    var pnode := Index(pivots, nodes);
    var node := Index(mypivots, mychildren);
    node
  }

  lemma BuildParentForSequenceProperties(nodes: seq<Node>, pivots: seq<Key>, boundaries: seq<nat>, i: nat)
    requires WF(Index(pivots, nodes))
    requires ValidBoundariesForSeq(|nodes|, boundaries)
    requires |pivots| == |nodes|-1
    requires Keys.IsStrictlySorted(pivots)
    requires i < |boundaries|-1
    ensures WF(BuildParentForSequenceInner(nodes, pivots, boundaries, i))
    ensures AllKeys(BuildParentForSequenceInner(nodes, pivots, boundaries, i)) != {}
  {
    Integer_Order.IsStrictlySortedImpliesLt(boundaries, i, i+1);
    Keys.StrictlySortedSubsequence(pivots, boundaries[i], boundaries[i+1]-1);
    var mypivots := pivots[boundaries[i]..boundaries[i+1]-1];
    var mychildren := ExtractBoundedSubsequence(nodes, boundaries, i);
    var pnode := Index(pivots, nodes);
    var node := Index(mypivots, mychildren);
    forall j | 0 <= j < |node.children| - 1
      ensures AllKeysBelowBound(node, j)
    {
      assert AllKeysBelowBound(pnode, boundaries[i] + j);
    }
    forall j | 0 < j < |node.children|
      ensures AllKeysAboveBound(node, j)
    {
      assert AllKeysAboveBound(pnode, boundaries[i] + j);
    }
    assert node.children[0] == nodes[boundaries[i]];
  }
    
  function BuildParentForSequence(nodes: seq<Node>, pivots: seq<Key>, boundaries: seq<nat>, i: nat) : (node: Node)
    requires WF(Index(pivots, nodes))
    requires ValidBoundariesForSeq(|nodes|, boundaries)
    requires |pivots| == |nodes|-1
    requires Keys.IsStrictlySorted(pivots)
    requires i < |boundaries|-1
    ensures WF(node)
    ensures AllKeys(node) != {}
  {
    BuildParentForSequenceProperties(nodes, pivots, boundaries, i);
    BuildParentForSequenceInner(nodes, pivots, boundaries, i)
  }
  
  function BuildParentsFromChildren(nodes: seq<Node>, pivots: seq<Key>, boundaries: seq<nat>) : (parents: seq<Node>)
    requires WF(Index(pivots, nodes))
    requires ValidBoundariesForSeq(|nodes|, boundaries)
    requires |pivots| == |nodes| - 1
    ensures |parents| == |boundaries|-1
    ensures forall i :: 0 <= i < |parents| ==> WF(parents[i])
    ensures forall i :: 0 <= i < |parents| ==> AllKeys(parents[i]) != {}
  {
    if |boundaries| == 2 then
      [BuildParentForSequence(nodes, pivots, boundaries, 0)]
    else
      var subboundaries := DropLast(boundaries);
      var subnodes := DropLastPiece(nodes, boundaries);
      var subpivots := DropLastPivotsPiece(pivots, boundaries);
      SubIndexPreservesWF(Index(pivots, nodes), 0, boundaries[|boundaries|-2]);
      BuildParentsFromChildren(subnodes, subpivots, subboundaries) + [BuildParentForSequence(nodes, pivots, boundaries, |boundaries|-2)]
  }

  function {:opaque} BuildBoundariesInner(numthings: nat, groupSize: nat) : (boundaries: seq<nat>)
    requires 0 < numthings
    requires 0 < groupSize
  {
    var tmp := Apply(i => i * groupSize, Range((numthings + groupSize - 1) / groupSize));
    if Last(tmp) == numthings then tmp
    else tmp + [numthings]
  }


  lemma BuildBoundariesProperties(numthings: nat, groupSize: nat)
    requires 0 < numthings
    requires 0 < groupSize
    ensures ValidBoundariesForSeq(numthings, BuildBoundariesInner(numthings, groupSize))
    ensures 1 < numthings && 1 < groupSize ==> |BuildBoundariesInner(numthings, groupSize)| - 1 < numthings
  {
    reveal_BuildBoundariesInner();
    var tmp := Apply(i => i * groupSize, Range((numthings + groupSize - 1) / groupSize));
    forall i, j | 0 <= i < j < |tmp|
      ensures tmp[i] < tmp[j]
    {
      assert i * groupSize < j * groupSize;
    }
    Integer_Order.reveal_IsStrictlySorted();
    if Last(tmp) == numthings {
    } else {
      Integer_Order.StrictlySortedAugment(tmp, numthings);
      if 1 < numthings && 1 < groupSize {
        Math.DivCeilLT(numthings, groupSize);
      }
    }
  }

  function BuildBoundaries(numthings: nat, groupSize: nat) : (boundaries: seq<nat>)
    requires 0 < numthings
    requires 0 < groupSize
    ensures ValidBoundariesForSeq(numthings, boundaries)
    ensures 1 < numthings && 1 < groupSize ==> |BuildBoundaries(numthings, groupSize)| - 1 < numthings
  {
    BuildBoundariesProperties(numthings, groupSize);
    BuildBoundariesInner(numthings, groupSize)
  }


  function SplitFirstChildAlongBoundaries(node: Node, boundaries: seq<nat>) : (newnode: Node)
    requires WF(node)
    requires node.Index?
    requires node.children[0].Index?
    requires ValidBoundariesForSeq(|node.children[0].children|, boundaries)
  {
    if |boundaries| == 2 then
      node
    else
      var subboundaries := DropLast(boundaries);
      var leftchild := SubIndex(node.children[0], 0, Last(subboundaries));
      var rightchild := SubIndex(node.children[0], Last(subboundaries), Last(boundaries));
      var pivot := node.children[0].pivots[Last(subboundaries)-1];
      Index([pivot] + node.pivots, [leftchild, rightchild] + node.children[1..])
  }

  lemma SplitFirstChildAlongBoundariesEquivalence(node: Node, boundaries: seq<nat>, newnode: Node)
    requires WF(node)
    requires node.Index?
    requires node.children[0].Index?
    requires ValidBoundariesForSeq(|node.children[0].children|, boundaries)
    requires newnode == SplitFirstChildAlongBoundaries(node, boundaries)
    ensures WF(newnode)
    ensures AllKeys(newnode) == AllKeys(node)
    ensures Interpretation(newnode) == Interpretation(node)
  {
    if |boundaries| == 2 {
    } else {
      // assert SplitIndex(node.children[0], newnode.children[0], newnode.children[1],
      //                   newnode.children[0].pivots[0], newnode.pivots[0]);
      // SplitChildOfIndexPreservesWF(node, newnode, 0, newnode.children[0].pivots[0]);
      // assert WF(newnode);
      assume false;
    }
  }
  
  lemma ParentsMatchPivots(nodes: seq<Node>, pivots: seq<Key>, config: Configuration, boundaries: seq<nat>, parents: seq<Node>, newpivots: seq<Key>)
    requires WF(Index(pivots, nodes))
    requires ValidConfiguration(config)
    requires boundaries == BuildBoundaries(|nodes|, config.maxChildren)
    requires parents == BuildParentsFromChildren(nodes, pivots, boundaries)
    requires newpivots == ExtractPivotsForBoundaries(pivots, boundaries)
    ensures WF(Index(newpivots, parents))
  {
    assume false;
    // ExtractPivotsForBoundariesPreservesSort(pivots, boundaries);
    // var pnode := Index(newpivots, parents);
    // forall i | 0 <= i < |pnode.children|-1
    //   ensures AllKeysBelowBound(pnode, i)
    // {
    //   forall key | key in AllKeys(pnode.children[i])
    //     ensures Keys.lt(key, pnode.pivots[i])
    //   {
    //     assert pnode.pivots[i] == pivots[boundaries[i+1]-1];
    //     if j :| key == pnode.children[i].pivots[j] {
    //       assert pnode.children[i].pivots[j] == pivots[boundaries[i]-1+j];
    //       Keys.IsStrictlySortedImpliesLt(pivots, boundaries[i]-1+j, boundaries[i+1]-1);
    //     } else {
    //       var j :| key in AllKeys(pnode.children[i].children[j]);
    //       assert AllKeysBelowBound(pnode.children[i], j);
    //       assert Keys.lt(key, pnode.children[i].pivots[j]);
    //       assert pnode.children[i].pivots[j] == pivots[boundaries[i]-1+j];
    //       Keys.IsStrictlySortedImpliesLt(pivots, boundaries[i]-1+j, boundaries[i+1]-1);
    //       assert Keys.lt(pnode.children[i].pivots[j], pnode.pivots[i]);
    //     }
    //   }
    // }
    // forall i | 0 < i < |pnode.children|
    //   ensures AllKeysAboveBound(pnode, i)
    // {
    //   assume false;
    // }
  }
  
  function BuildTreeFromChildren(nodes: seq<Node>, pivots: seq<Key>, config: Configuration) : (node: Node)
    requires WF(Index(pivots, nodes))
    requires ValidConfiguration(config)
    ensures WF(node)
    decreases |nodes|
  {
    if |nodes| == 1 then
      nodes[0]
    else
      var boundaries := BuildBoundaries(|nodes|, config.maxChildren);
      var parents := BuildParentsFromChildren(nodes, pivots, boundaries);
      var newpivots := ExtractPivotsForBoundaries(pivots, boundaries);
      ParentsMatchPivots(nodes, pivots, config, boundaries, parents, newpivots);
      BuildTreeFromChildren(parents, newpivots, config)
  }
  
  function BuildTreeForSequence(kvlist: KVList, config: Configuration) : (node: Node)
    requires 0 < |kvlist.keys|
    requires WFKVList(kvlist)
    requires ValidConfiguration(config)
    ensures FitsConfig(node, config)
  {
    var boundaries := BuildBoundaries(|kvlist.keys|, config.maxKeys);
    var leaves := BuildLeavesForSequence(kvlist, boundaries);
    var pivots := ExtractPivotsForBoundaries(ExtractPivotsFromKVList(kvlist), boundaries);
    assume false;
    BuildTreeFromChildren(leaves, pivots, config)
  }
    
  lemma FromSeqWF(keys: seq<Key>, boundaries: seq<nat>, pivots: seq<Key>, children: seq<Node>)
    requires Keys.IsStrictlySorted(keys)
    requires ValidBoundariesForSeq(|keys|, boundaries)
    requires |boundaries| == |children| + 1
    requires PivotsMatchBoundaries(keys, boundaries, pivots)
    requires forall i :: 0 <= i < |children| ==> WF(children[i])
    requires forall i :: 0 <= i  < |children| ==> {} < AllKeys(children[i]) <= Set(ExtractBoundedSubsequence(keys, boundaries, i))
    ensures WF(Index(pivots, children))
  {
    var node := Index(pivots, children);
    forall i | 0 <= i < |children|-1
      ensures AllKeysBelowBound(node, i)
    {
      forall k | k in AllKeys(node.children[i])
        ensures Keys.lt(k, node.pivots[i])
      {
        Integer_Order.IsStrictlySortedImpliesLt(boundaries, i, i+1);
        var j :| boundaries[i] <= j < boundaries[i+1] && keys[j] == k;
        Keys.IsStrictlySortedImpliesLt(keys, j, boundaries[i+1]);
      }
    }
    forall i | 0 < i < |children|
      ensures AllKeysAboveBound(node, i)
    {
      forall k | k in AllKeys(node.children[i])
        ensures Keys.lte(node.pivots[i-1], k)
      {
        Integer_Order.IsStrictlySortedImpliesLt(boundaries, i, i+1);
        var j :| boundaries[i] <= j < boundaries[i+1] && keys[j] == k;
        Keys.IsStrictlySortedImpliesLte(keys, boundaries[i], j);
      }
    }
    BoundaryPivotsStrictlySorted(keys, boundaries, pivots);
  }
}

