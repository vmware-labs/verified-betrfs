include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "../lib/total_order.dfy"

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

  function PotentialPivots(node: Node) : set<Key>
  {
    match node {
      case Leaf(keys, values) => set i | 0 < i < |keys| :: keys[i]
      case Index(pivots, children) => set i | 0 <= i < |pivots| :: pivots[i]
    }    
  }    
    
  function AllKeys(node: Node) : set<Key>
  {
    match node {
      case Leaf(keys, values) => set k | k in keys
      case Index(pivots, children) => set i, k | 0 <= i < |children| && k in AllKeys(children[i]) :: k
    }    
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
      && (forall i, key :: 0 <= i < |node.children|-1 && key in PotentialPivots(node.children[i]) ==> Keys.lt(key, node.pivots[i]))
      && (forall i, key :: 0 < i < |node.children|   && key in PotentialPivots(node.children[i]) ==> Keys.lt(node.pivots[i-1], key))
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

  lemma AllKeysIsConsistentWithInterpretation(node: Node, key: Key)
    requires WF(node)
    requires key in Interpretation(node)
    ensures node.Index? ==> WF(node) && key in AllKeys(node.children[Keys.LargestLte(node.pivots, key) + 1])
  {
    if node.Index? {
      assert key in Interpretation(node.children[Keys.LargestLte(node.pivots, key) + 1]);
    }
  }
  
  lemma AllKeysIsConsistentWithInterpretationUniversal(node: Node)
    requires WF(node)
    requires node.Index?
    ensures WF(node)
    ensures forall key :: key in Interpretation(node) ==> key in AllKeys(node.children[Keys.LargestLte(node.pivots, key) + 1])
  {
    forall key | key in Interpretation(node)
      ensures key in AllKeys(node.children[Keys.LargestLte(node.pivots, key) + 1])
    {
      AllKeysIsConsistentWithInterpretation(node, key);
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
    && pivot == rightleaf.keys[0]
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
  }
  
  predicate SplitIndex(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
  {
    && oldindex.Index?
    && leftindex.Index?
    && rightindex.Index?
    && WF(oldindex)
    && 0 < |leftindex.children| < |oldindex.children|-1
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
  
  lemma SplitIndexInterpretation(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
    requires SplitIndex(oldindex, leftindex, rightindex, pivot)
    requires WF(leftindex)
    requires WF(rightindex)
    ensures Interpretation(oldindex) == Keys.MapPivotedUnion(Interpretation(leftindex), pivot, Interpretation(rightindex))
  {
    var oldint := Interpretation(oldindex);
    var leftint := Interpretation(leftindex);
    var rightint := Interpretation(rightindex);
    var newint := Keys.MapPivotedUnion(leftint, pivot, rightint);

    Keys.PosEqLargestLte(oldindex.pivots, pivot, |leftindex.pivots|);
    
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
      }
    }

    forall key | key in newint
      ensures key in oldint
    {
      if Keys.lt(key, pivot) {
        AllKeysIsConsistentWithInterpretation(leftindex, key);
        var llte := Keys.LargestLte(leftindex.pivots, key);
        Keys.LargestLteSubsequence(oldindex.pivots, key, 0, |leftindex.pivots|);
        assert oldindex.children[llte+1] == leftindex.children[llte+1];
      } else {
        AllKeysIsConsistentWithInterpretation(rightindex, key);
        var llte := Keys.LargestLte(rightindex.pivots, key);
        Keys.LargestLteSubsequence(oldindex.pivots, key, |leftindex.pivots|+1, |oldindex.pivots|);
        assert oldindex.children[|leftindex.children| + llte + 1] == rightindex.children[llte+1];
      }
    }
  }
  
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

  lemma SplitNodeAllKeys(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
    requires SplitNode(oldnode, leftnode, rightnode, pivot)
    ensures AllKeys(oldnode) == AllKeys(leftnode) + AllKeys(rightnode)
  {
    if SplitLeaf(oldnode, leftnode, rightnode, pivot) {
    } else {
      forall key | key in AllKeys(leftnode) + AllKeys(rightnode)
        ensures key in AllKeys(oldnode)
      {
        if key in AllKeys(leftnode) {
          var i :| 0 <= i < |leftnode.children| && key in AllKeys(leftnode.children[i]);
          assert oldnode.children[i] == leftnode.children[i];
        } else {
          var i :| 0 <= i < |rightnode.children| && key in AllKeys(rightnode.children[i]);
          assert oldnode.children[i + |leftnode.children|] == rightnode.children[i];
        }
      }
    }
  }

  lemma SplitNodePotentialPivots(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
    requires WF(oldnode)
    requires SplitNode(oldnode, leftnode, rightnode, pivot)
    ensures PotentialPivots(leftnode) <= PotentialPivots(oldnode)
    ensures PotentialPivots(rightnode) <= PotentialPivots(oldnode)
    ensures forall key :: key in PotentialPivots(leftnode) ==> Keys.lt(key, pivot)
    ensures forall key :: key in PotentialPivots(rightnode) ==> Keys.lt(pivot, key)
  {
    forall key | key in PotentialPivots(leftnode)
      ensures key in PotentialPivots(oldnode)
      ensures Keys.lt(key, pivot)
    {
      if oldnode.Leaf? {
        var i :| 0 < i < |leftnode.keys| && key == leftnode.keys[i];
        assert oldnode.keys[i] == key;
        Keys.IsStrictlySortedImpliesLt(oldnode.keys, i, |leftnode.keys|);
      } else {
        var i :| 0 <= i < |leftnode.pivots| && key == leftnode.pivots[i];
        Keys.IsStrictlySortedImpliesLt(oldnode.pivots, i, |leftnode.pivots|);        
      }
    }
    forall key | key in PotentialPivots(rightnode)
      ensures key in PotentialPivots(oldnode)
      ensures Keys.lt(pivot, key)
    {
      if oldnode.Leaf? {
        var i :| 0 < i < |rightnode.keys| && key == rightnode.keys[i];
        assert oldnode.keys[|leftnode.keys| + i] == key;
        Keys.IsStrictlySortedImpliesLt(oldnode.keys, |leftnode.keys|, |leftnode.keys| + i);
      } else {
        var i :| 0 <= i < |rightnode.pivots| && key == rightnode.pivots[i];
        Keys.IsStrictlySortedImpliesLt(oldnode.pivots, |leftnode.pivots|, |leftnode.pivots| + i + 1);
      }
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
    
    if oldindex.children[childidx].Leaf? {
      assert pivot == oldindex.children[childidx].keys[|newindex.children[childidx].keys|];
      assert pivot in PotentialPivots(oldindex.children[childidx]);
    } else {
      assert pivot in PotentialPivots(oldindex.children[childidx]);
    }
    Keys.strictlySortedInsert2(oldindex.pivots, pivot, childidx);

    forall i | 0 <= i < |newindex.children|
      ensures WF(newindex.children[i])
    {
      if i < childidx {
      } else if i == childidx {
        SplitNodePreservesWF(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], pivot);
      } else if i == childidx + 1 {
        SplitNodePreservesWF(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], pivot);
      } else {
        assert newindex.children[i] == oldindex.children[i-1];
      }
    }

    forall i, key | 0 <= i < |newindex.children| - 1 && key in PotentialPivots(newindex.children[i])
      ensures Keys.lt(key, newindex.pivots[i])
    {
      if i < childidx {
      } else if i == childidx {
        SplitNodePotentialPivots(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], pivot);
      } else if i == childidx + 1 {
        SplitNodePotentialPivots(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], pivot);
      } else {
        assert newindex.children[i] == oldindex.children[i-1];
      }      
    }
    
    forall i, key | 0 < i < |newindex.children| && key in PotentialPivots(newindex.children[i])
      ensures Keys.lt(newindex.pivots[i-1], key)
    {
      if i < childidx {
      } else if i == childidx {
        SplitNodePotentialPivots(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], pivot);
      } else if i == childidx + 1 {
        SplitNodePotentialPivots(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], pivot);
      } else {
        assert newindex.children[i] == oldindex.children[i-1];
      }      
    }
    
  }
  
  lemma SplitChildOfIndexPreservesAllKeys(oldindex: Node, newindex: Node, childidx: int)
    requires SplitChildOfIndex(oldindex, newindex, childidx)
    ensures AllKeys(newindex) == AllKeys(oldindex)
  {
    assert WF(oldindex);
    SplitChildOfIndexPreservesWF(oldindex, newindex, childidx);
    
    forall key | key in AllKeys(oldindex)
      ensures key in AllKeys(newindex)
    {
      var i :| 0 <= i < |oldindex.children| && key in AllKeys(oldindex.children[i]);
      if i < childidx {
      } else if i == childidx {
        SplitNodeAllKeys(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], newindex.pivots[childidx]);
      } else {
        assert newindex.children[i+1] == oldindex.children[i];
      }
    }
    
    forall key | key in AllKeys(newindex)
      ensures key in AllKeys(oldindex)
    {
      var i :| 0 <= i < |newindex.children| && key in AllKeys(newindex.children[i]);
      if i < childidx {
      } else if i == childidx {
        SplitNodeAllKeys(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], newindex.pivots[childidx]);
      } else if i == childidx + 1 {
        SplitNodeAllKeys(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], newindex.pivots[childidx]);
      } else {
        assert newindex.children[i] == oldindex.children[i-1];
      }
    }
  }
  
  lemma SplitChildOfIndexPreservesInterpretation(oldindex: Node, newindex: Node, childidx: int)
    requires SplitChildOfIndex(oldindex, newindex, childidx)
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
    SplitNodeInterpretation(oldchild, leftchild, rightchild, pivot);        
    SplitChildOfIndexPreservesAllKeys(oldindex, newindex, childidx);
    
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
    }
  }
}
