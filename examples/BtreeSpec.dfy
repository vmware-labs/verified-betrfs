include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Maps.s.dfy"
include "../lib/Base/total_order.i.dfy"

abstract module BtreeSpec {
  import opened Seq = Sequences
  import opened Maps
  import Keys : Total_Order

  type Key = Keys.Element
  type Value
    
  datatype QueryResult =
    | Found(value: Value)
    | NotFound
    
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

  predicate SplitLeaf(oldleaf: Node, leftleaf: Node, rightleaf: Node, wit: Key, pivot: Key)
  {
    && oldleaf.Leaf?
    && leftleaf.Leaf?
    && rightleaf.Leaf?
    && 0 < |leftleaf.keys| == |leftleaf.values|
    && 0 < |rightleaf.keys| == |rightleaf.values|
    && oldleaf.keys == leftleaf.keys + rightleaf.keys
    && oldleaf.values == leftleaf.values + rightleaf.values
    && pivot == rightleaf.keys[0]
    && wit == leftleaf.keys[0]
  }

  lemma SplitLeafPreservesWF(oldleaf: Node, leftleaf: Node, rightleaf: Node, wit: Key, pivot: Key)
    requires WF(oldleaf)
    requires SplitLeaf(oldleaf, leftleaf, rightleaf, wit, pivot)
    ensures WF(leftleaf)
    ensures WF(rightleaf)
  {
    Keys.StrictlySortedSubsequence(oldleaf.keys, 0, |leftleaf.keys|);
    Keys.StrictlySortedSubsequence(oldleaf.keys, |leftleaf.keys|, |oldleaf.keys|);
    assert Keys.IsStrictlySorted(oldleaf.keys[|leftleaf.keys|..|oldleaf.keys|]);
    assert rightleaf.keys == oldleaf.keys[|leftleaf.keys|..|oldleaf.keys|];
  }

  lemma SplitLeafInterpretation(oldleaf: Node, leftleaf: Node, rightleaf: Node, wit: Key, pivot: Key)
    requires SplitLeaf(oldleaf, leftleaf, rightleaf, wit, pivot)
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
  
  predicate SplitIndex(oldindex: Node, leftindex: Node, rightindex: Node, wit: Key, pivot: Key)
  {
    && oldindex.Index?
    && leftindex.Index?
    && rightindex.Index?
    && WF(oldindex)
    && 0 < |leftindex.children| < |oldindex.children|-1
    && leftindex == SubIndex(oldindex, 0, |leftindex.children|)
    && rightindex == SubIndex(oldindex, |leftindex.children|, |oldindex.children|)
    && Keys.lt(wit, pivot)
    && wit in AllKeys(oldindex)
    && pivot == oldindex.pivots[|leftindex.pivots|]
  }

  lemma SplitIndexPreservesWF(oldindex: Node, leftindex: Node, rightindex: Node, wit: Key, pivot: Key)
    requires SplitIndex(oldindex, leftindex, rightindex, wit, pivot)
    ensures WF(leftindex)
    ensures WF(rightindex)
  {
    SubIndexPreservesWF(oldindex, 0, |leftindex.children|);
    SubIndexPreservesWF(oldindex, |leftindex.children|, |oldindex.children|);
  }
  
  lemma SplitIndexInterpretation1(oldindex: Node, leftindex: Node, rightindex: Node, wit: Key, pivot: Key)
    requires SplitIndex(oldindex, leftindex, rightindex, wit, pivot)
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
  
  lemma SplitIndexInterpretation2(oldindex: Node, leftindex: Node, rightindex: Node, wit: Key, pivot: Key)
    requires SplitIndex(oldindex, leftindex, rightindex, wit, pivot)
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

  lemma SplitIndexInterpretation(oldindex: Node, leftindex: Node, rightindex: Node, wit: Key, pivot: Key)
    requires SplitIndex(oldindex, leftindex, rightindex, wit, pivot)
    requires WF(leftindex)
    requires WF(rightindex)
    ensures Interpretation(oldindex) ==
    Keys.MapPivotedUnion(Interpretation(leftindex), pivot, Interpretation(rightindex))
  {
    SplitIndexInterpretation1(oldindex, leftindex, rightindex, wit, pivot);
    SplitIndexInterpretation2(oldindex, leftindex, rightindex, wit, pivot);
  }

  
  predicate SplitNode(oldnode: Node, leftnode: Node, rightnode: Node, wit: Key, pivot: Key)
  {
    || SplitLeaf(oldnode, leftnode, rightnode, wit, pivot)
    || SplitIndex(oldnode, leftnode, rightnode, wit, pivot)
  }

  lemma SplitNodePreservesWF(oldnode: Node, leftnode: Node, rightnode: Node, wit: Key, pivot: Key)
    requires WF(oldnode)
    requires SplitNode(oldnode, leftnode, rightnode, wit, pivot)
    ensures WF(leftnode)
    ensures WF(rightnode)
  {
    if SplitLeaf(oldnode, leftnode, rightnode, wit, pivot) {
      SplitLeafPreservesWF(oldnode, leftnode, rightnode, wit, pivot);
    } else {
      SplitIndexPreservesWF(oldnode, leftnode, rightnode, wit, pivot);
    }
  }
    
  lemma SplitNodeInterpretation(oldnode: Node, leftnode: Node, rightnode: Node, wit: Key, pivot: Key)
    requires SplitNode(oldnode, leftnode, rightnode, wit, pivot)
    requires WF(oldnode)
    requires WF(leftnode)
    requires WF(rightnode)
    ensures Interpretation(oldnode) == Keys.MapPivotedUnion(Interpretation(leftnode), pivot, Interpretation(rightnode))
  {
    if SplitLeaf(oldnode, leftnode, rightnode, wit, pivot) {
      SplitLeafInterpretation(oldnode, leftnode, rightnode, wit, pivot);
    } else {
      SplitIndexInterpretation(oldnode, leftnode, rightnode, wit, pivot);
    }
  }

  lemma SplitLeafAllKeys(oldnode: Node, leftnode: Node, rightnode: Node, wit: Key, pivot: Key)
    requires WF(oldnode)
    requires SplitLeaf(oldnode, leftnode, rightnode, wit, pivot)
    ensures AllKeys(oldnode) == AllKeys(leftnode) + AllKeys(rightnode) + {pivot}
    ensures wit in AllKeys(oldnode)
    ensures Keys.lt(wit, pivot)
    ensures AllKeys(leftnode) != {}
    ensures AllKeys(rightnode) != {}
    ensures forall key :: key in AllKeys(leftnode) ==> Keys.lt(key, pivot)
    ensures forall key :: key in AllKeys(rightnode) ==> Keys.lte(pivot, key)
  {
    forall key | key in AllKeys(leftnode)
      ensures Keys.lt(key, pivot)
    {
      var i :| 0 <= i < |leftnode.keys| && key == leftnode.keys[i];
      Keys.IsStrictlySortedImpliesLt(oldnode.keys, i, |leftnode.keys|);
    }
    forall key | key in AllKeys(rightnode)
      ensures Keys.lte(pivot, key)
    {
      var i :| 0 <= i < |rightnode.keys| && key == rightnode.keys[i];
      Keys.IsSortedImpliesLte(oldnode.keys, |leftnode.keys|, |leftnode.keys| + i);
    }
  }

  lemma SplitIndexAllKeys(oldnode: Node, leftnode: Node, rightnode: Node, wit: Key, pivot: Key)
    requires WF(oldnode)
    requires SplitIndex(oldnode, leftnode, rightnode, wit, pivot)
    ensures AllKeys(oldnode) == AllKeys(leftnode) + AllKeys(rightnode) + {pivot}
    ensures wit in AllKeys(oldnode)
    ensures Keys.lt(wit, pivot)
    ensures AllKeys(leftnode) != {}
    ensures AllKeys(rightnode) != {}
    ensures forall key :: key in AllKeys(leftnode) ==> Keys.lt(key, pivot)
    ensures forall key :: key in AllKeys(rightnode) ==> Keys.lte(pivot, key)
  {
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
  
  lemma SplitNodeAllKeys(oldnode: Node, leftnode: Node, rightnode: Node, wit: Key, pivot: Key)
    requires WF(oldnode)
    requires SplitNode(oldnode, leftnode, rightnode, wit, pivot)
    ensures AllKeys(oldnode) == AllKeys(leftnode) + AllKeys(rightnode) + {pivot}
    ensures wit in AllKeys(oldnode)
    ensures Keys.lt(wit, pivot)
    ensures AllKeys(leftnode) != {}
    ensures AllKeys(rightnode) != {}
    ensures forall key :: key in AllKeys(leftnode) ==> Keys.lt(key, pivot)
    ensures forall key :: key in AllKeys(rightnode) ==> Keys.lte(pivot, key)
  {
    if SplitLeaf(oldnode, leftnode, rightnode, wit, pivot) {
      SplitLeafAllKeys(oldnode, leftnode, rightnode, wit, pivot);
    } else {
      SplitIndexAllKeys(oldnode, leftnode, rightnode, wit, pivot);
    }
  }
  
  predicate SplitChildOfIndex(oldindex: Node, newindex: Node, childidx: int, wit: Key)
  {
    && oldindex.Index?
    && newindex.Index?
    && WF(oldindex)
    && 0 <= childidx < |oldindex.children|
    && |newindex.children| == |oldindex.children| + 1 // FIXME: WTF?  Dafny can't get these from WF?
    && |newindex.pivots| == |oldindex.pivots| + 1
    && |oldindex.pivots| == |oldindex.children| - 1
    && SplitNode(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], wit, newindex.pivots[childidx])
    && newindex.pivots == Seq.insert(oldindex.pivots, newindex.pivots[childidx], childidx)
    && newindex.children == Seq.replace1with2(oldindex.children, newindex.children[childidx], newindex.children[childidx+1], childidx)
  }

  lemma SplitChildOfIndexPreservesWF(oldindex: Node, newindex: Node, childidx: int, wit: Key)
    requires WF(oldindex)
    requires SplitChildOfIndex(oldindex, newindex, childidx, wit)
    ensures WF(newindex)
  {
    var pivot := newindex.pivots[childidx];
    var oldchild := oldindex.children[childidx];
    var leftchild := newindex.children[childidx];
    var rightchild := newindex.children[childidx+1];
    SplitNodeAllKeys(oldchild, leftchild, rightchild, wit, pivot);
    SplitNodePreservesWF(oldchild, leftchild, rightchild, wit, pivot);
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
  
  lemma SplitChildOfIndexPreservesAllKeys(oldindex: Node, newindex: Node, childidx: int, wit: Key)
    requires SplitChildOfIndex(oldindex, newindex, childidx, wit)
    ensures AllKeys(newindex) == AllKeys(oldindex)
  {
    assert WF(oldindex);
    SplitChildOfIndexPreservesWF(oldindex, newindex, childidx, wit);
    SplitNodeAllKeys(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], wit, newindex.pivots[childidx]);
    
    forall key | key in AllKeys(newindex)
      ensures key in AllKeys(oldindex)
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
        } else if i == childidx + 1 {
        } else {
          assert key == oldindex.pivots[i-1];
        }
      }
    }
  }
  
  lemma SplitChildOfIndexPreservesInterpretation(oldindex: Node, newindex: Node, childidx: int, wit: Key)
    requires SplitChildOfIndex(oldindex, newindex, childidx, wit)
    requires WF(newindex);
    ensures Interpretation(newindex) == Interpretation(oldindex)
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
    SplitNodeInterpretation(oldchild, leftchild, rightchild, wit, pivot);
    SplitChildOfIndexPreservesAllKeys(oldindex, newindex, childidx, wit);
    
    forall key | key in oldint
      ensures key in newint && newint[key] == oldint[key]
    {
      var llte := Keys.LargestLte(oldindex.pivots, key);
      if llte + 1 < childidx {
        Keys.LargestLteIsUnique2(newindex.pivots, key, llte);
        // assert key in newint && newint[key] == oldint[key];
      } else if llte + 1 == childidx {
        if Keys.lt(key, pivot) {
          Keys.LargestLteIsUnique2(newindex.pivots, key, llte);
        } else {
          assert llte+2 < |newindex.pivots| ==> newindex.pivots[llte+2] == oldindex.pivots[llte+1];
          Keys.LargestLteIsUnique2(newindex.pivots, key, llte+1);
        }
      } else {
        var newllte := llte + 1;
        assert newindex.pivots[newllte] == oldindex.pivots[llte];
        assert newllte+1 < |newindex.pivots| ==> newindex.pivots[newllte+1] == oldindex.pivots[llte+1];
        assert newllte+1 < |newindex.pivots| ==> Keys.lt(key, newindex.pivots[newllte+1]);
        Keys.LargestLteIsUnique2(newindex.pivots, key, newllte);
        assert newindex.children[newllte+1] == oldindex.children[llte+1];
      }
    }

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

  lemma NumElementsOfChildrenDecreases(nodes: seq<Node>, prefix: int)
    requires forall i :: 0 <= i < |nodes| ==> WF(nodes[i])
    requires 0 <= prefix <= |nodes|
    ensures NumElementsOfChildren(nodes[..prefix]) <= NumElementsOfChildren(nodes)
  {
    if prefix == |nodes| {
      assert nodes[..prefix] == nodes;
    } else {
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
    
  function ToSeq(node: Node) : (kvlists : (seq<Key>, seq<Value>))
    requires WF(node)
    ensures |kvlists.0| == |kvlists.1|
  {
    if node.Leaf? then (node.keys, node.values)
    else
      var (keylists, valuelists) := ToSeqChildren(node.children);
      (Flatten(keylists), Flatten(valuelists))
  }

  lemma ToSeqMapCorrespondence(node: Node)
    requires WF(node)
    ensures Keys.IsStrictlySorted(ToSeq(node).0);
    ensures forall i :: 0 <= i < |ToSeq(node).0| ==> MapsTo(Interpretation(node), ToSeq(node).0[i], ToSeq(node).1[i])
    ensures forall key :: key in Interpretation(node) ==> key in ToSeq(node).0
  {
    var (keys, values) := ToSeq(node);
    
    if node.Leaf? {
      forall i | 0 <= i < |keys|
        ensures i == Keys.LargestLte(node.keys, node.keys[i])
      {
        Keys.PosEqLargestLte(node.keys, node.keys[i], i);
      }
      
    } else {
      var (keylists, valuelists) := ToSeqChildren(node.children);
      var shape := FlattenShape(keylists);
      assert shape == FlattenShape(valuelists);
      
      forall i | 0 <= i < |keylists|
        ensures Keys.IsStrictlySorted(keylists[i])
        ensures forall j :: 0 <= j < |keylists[i]| ==> MapsTo(Interpretation(node.children[i]), keylists[i][j], valuelists[i][j])
        ensures forall key :: key in Interpretation(node.children[i]) ==> key in keylists[i]
      {
        ToSeqMapCorrespondence(node.children[i]);
      }

      forall i, j, k1, k2 | 0 <= i < j < |keylists| && k1 in keylists[i] && k2 in keylists[j]
        ensures Keys.lt(k1, k2)
      {
        assert k1 in Interpretation(node.children[i]);
        assert k2 in Interpretation(node.children[j]);
        AllKeysIsConsistentWithInterpretation(node.children[i], k1);
        AllKeysIsConsistentWithInterpretation(node.children[j], k2);
        assert AllKeysBelowBound(node, i);
        assert AllKeysAboveBound(node, j);
        if i < j-1 {
          Keys.IsStrictlySortedImpliesLt(node.pivots, i, j-1);
        }
      }
      Keys.FlattenStrictlySorted(keylists);
      assert Keys.IsStrictlySorted(keys);

      forall i | 0 <= i < |keys|
        ensures MapsTo(Interpretation(node), keys[i], values[i])
      {
        var (child, offset) := UnflattenIndex(shape, i);
        UnflattenIndexIsCorrect(keylists, i);
        UnflattenIndexIsCorrect(valuelists, i);
        assert keys[i] in Interpretation(node.children[child]);
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

      forall key | key in Interpretation(node)
        ensures key in keys
      {
        InterpretationInheritance(node, key);
        var child := Keys.LargestLte(node.pivots, key) + 1;
        var offset :| 0 <= offset < |keylists[child]| && keylists[child][offset] == key;
        assert keylists[child][offset] == key;
        FlattenIndexIsCorrect(keylists, child, offset);
      }
    }
  }
}

