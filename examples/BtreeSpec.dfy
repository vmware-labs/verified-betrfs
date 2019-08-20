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

  function LocalKeys(node: Node) : set<Key>
  {
    match node {
      case Leaf(keys, values) => set k | k in keys
      case Index(pivots, children) => set k | k in pivots
    }    
  }    
    
  function AllKeys(node: Node) : set<Key>
  {
    match node {
      case Leaf(keys, values) => set k | k in keys
      case Index(pivots, children) => set i, k | 0 <= i < |children| && k in AllKeys(children[i]) :: k
    }    
  }
  
  predicate WFLeaf(leaf: Node)
    requires leaf.Leaf?
  {
    && |leaf.keys| == |leaf.values|
    && Keys.IsStrictlySorted(leaf.keys)
  }

  predicate WFIndex(index: Node)
    requires index.Index?
    decreases index, 0
  {
    && |index.pivots| == |index.children| - 1
    && Keys.IsStrictlySorted(index.pivots)
    && (forall i :: 0 <= i < |index.children| ==> WF(index.children[i]))
    && (forall i :: 0 <= i < |index.children| ==> LocalKeys(index.children[i]) != {})
    && (forall i, key :: 0 <= i < |index.children|-1 && key in LocalKeys(index.children[i]) ==> Keys.lt(key, index.pivots[i]))
    && (forall i, key :: 0 < i < |index.children|   && key in LocalKeys(index.children[i]) ==> Keys.lte(index.pivots[i-1], key))
  }

  predicate WF(node: Node)
    decreases node, 1
  {
    match node {
      case Leaf(_, _) =>  WFLeaf(node)
      case Index(_, _) => WFIndex(node)
    }
  }

  function InterpretLeaf(leaf: Node) : map<Key, Value>
    requires leaf.Leaf?
    requires WFLeaf(leaf)
  {
    Keys.PosEqLargestLteForAllElts(leaf.keys);
    map k | (k in leaf.keys) :: leaf.values[Keys.LargestLte(leaf.keys, k)]
  }

  function InterpretIndex(index: Node) : map<Key, Value>
    requires index.Index?
    requires WFIndex(index)
    decreases index, 0
  {
    map key |
      && key in AllKeys(index)
      && key in InterpretNode(index.children[Keys.LargestLte(index.pivots, key) + 1])
      :: InterpretNode(index.children[Keys.LargestLte(index.pivots, key) + 1])[key]
  }

  function InterpretNode(node: Node) : map<Key, Value>
    requires WF(node)
    decreases node, 1
  {
    match node {
      case Leaf(_, _) => InterpretLeaf(node)
      case Index(_, _) => InterpretIndex(node)
    }
  }

  lemma AllKeysIsConsistentWithInterpretation(node: Node, key: Key)
    requires WF(node)
    requires key in InterpretNode(node)
    ensures node.Index? ==> key in AllKeys(node.children[Keys.LargestLte(node.pivots, key) + 1])
  {
    if node.Index? {
      assert key in InterpretNode(node.children[Keys.LargestLte(node.pivots, key) + 1]);
    }
  }
  
  lemma AllKeysIsConsistentWithInterpretationUniversal(node: Node)
    requires WF(node)
    requires node.Index?
    ensures forall key :: key in InterpretNode(node) ==> key in AllKeys(node.children[Keys.LargestLte(node.pivots, key) + 1])
  {
    forall key | key in InterpretNode(node)
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
    && WFLeaf(oldleaf)
    && WFLeaf(leftleaf)
    && WFLeaf(rightleaf)
    && 0 < |leftleaf.keys|
    && 0 < |rightleaf.keys|
    && oldleaf.keys == leftleaf.keys + rightleaf.keys
    && oldleaf.values == leftleaf.values + rightleaf.values
    && Keys.lt(Last(leftleaf.keys), pivot)
    && Keys.lte(pivot, rightleaf.keys[0])
  }

  lemma SplitLeafInterpretation(oldleaf: Node, leftleaf: Node, rightleaf: Node, pivot: Key)
    requires SplitLeaf(oldleaf, leftleaf, rightleaf, pivot)
    ensures InterpretLeaf(oldleaf) == MapDisjointUnion(InterpretLeaf(leftleaf), InterpretLeaf(rightleaf))
  {
    var oldint := InterpretLeaf(oldleaf);
    var leftint := InterpretLeaf(leftleaf);
    var rightint := InterpretLeaf(rightleaf);
    var newint := MapDisjointUnion(leftint, rightint);

    forall key | key in oldint
      ensures newint[key] == oldint[key]
    {
      var llte := Keys.LargestLte(oldleaf.keys, key);
      if llte < |leftleaf.keys| {
        Keys.PosEqLargestLte(leftleaf.keys, key, llte);
      } else {
        var rightllte := llte - |leftleaf.keys|;
        Keys.PosEqLargestLte(rightleaf.keys, key, rightllte);
      }
    }
  }
  
  predicate SplitIndex(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
  {
    && oldindex.Index?
    && leftindex.Index?
    && rightindex.Index?
    && WFIndex(oldindex)
    && WFIndex(leftindex)
    && WFIndex(rightindex)
    && oldindex.pivots == leftindex.pivots + [pivot] + rightindex.pivots
    && oldindex.children == leftindex.children + rightindex.children
  }

  lemma SplitIndexInterpretation(oldindex: Node, leftindex: Node, rightindex: Node, pivot: Key)
    requires SplitIndex(oldindex, leftindex, rightindex, pivot)
    ensures InterpretIndex(oldindex) == Keys.MapPivotedUnion(InterpretIndex(leftindex), pivot, InterpretIndex(rightindex))
  {
    var oldint := InterpretIndex(oldindex);
    var leftint := InterpretIndex(leftindex);
    var rightint := InterpretIndex(rightindex);
    var newint := Keys.MapPivotedUnion(leftint, pivot, rightint);

    Keys.reveal_IsStrictlySorted();
    Keys.PosEqLargestLte(oldindex.pivots, pivot, |leftindex.pivots|);
    
    forall key | key in oldint
      ensures MapsTo(newint, key, oldint[key])
    {
      AllKeysIsConsistentWithInterpretation(oldindex, key);
    }

    forall key | key in newint
      ensures MapsTo(oldint, key, newint[key])
    {
      if Keys.lt(key, pivot) {
        AllKeysIsConsistentWithInterpretation(leftindex, key);
        var llte := Keys.LargestLte(leftindex.pivots, key);
        assert oldindex.children[llte+1] == leftindex.children[llte+1];
      } else {
        AllKeysIsConsistentWithInterpretation(rightindex, key);
        var llte := Keys.LargestLte(rightindex.pivots, key);
        assert oldindex.children[|leftindex.children| + llte + 1] == rightindex.children[llte+1];
      }
    }
    
  }
  
  predicate SplitNode(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
  {
    || SplitLeaf(oldnode, leftnode, rightnode, pivot)
    || SplitIndex(oldnode, leftnode, rightnode, pivot)
  }

  lemma SplitNodeInterpretation(oldnode: Node, leftnode: Node, rightnode: Node, pivot: Key)
    requires SplitNode(oldnode, leftnode, rightnode, pivot)
    ensures InterpretNode(oldnode) == Keys.MapPivotedUnion(InterpretNode(leftnode), pivot, InterpretNode(rightnode))
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
  
  predicate SplitChildOfIndex(oldindex: Node, newindex: Node, childidx: int)
  {
    && oldindex.Index?
    && newindex.Index?
    && WF(oldindex)
    && WF(newindex)
    && 0 <= childidx < |oldindex.children|
    && |newindex.children| == |oldindex.children| + 1 // FIXME: WTF?  Dafny can't get these from WF?
    && |newindex.pivots| == |oldindex.pivots| + 1
    && |oldindex.pivots| == |oldindex.children| - 1
    && newindex.pivots == Seq.insert(oldindex.pivots, newindex.pivots[childidx], childidx)
    && SplitNode(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], newindex.pivots[childidx])
    && newindex.children == oldindex.children[..childidx] + [newindex.children[childidx], newindex.children[childidx+1]] + oldindex.children[childidx+1..]
  }

  lemma SplitChildOfIndexPreservesAllKeys(oldindex: Node, newindex: Node, childidx: int)
    requires SplitChildOfIndex(oldindex, newindex, childidx)
    ensures AllKeys(newindex) == AllKeys(oldindex)
  {
    assert WFIndex(oldindex);
    assert WFIndex(newindex);
    
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
      }
    }
  }
  
  lemma SplitChildOfIndexPreservesInterpretation(oldindex: Node, newindex: Node, childidx: int)
    requires SplitChildOfIndex(oldindex, newindex, childidx)
    ensures InterpretNode(newindex) == InterpretNode(oldindex)
  {
    var newint := InterpretNode(newindex);
    var oldint := InterpretNode(oldindex);

    // WTF?  Dafny can't see these (from emacs flycheck mode)
    assert WFIndex(oldindex);
    assert WFIndex(newindex);
    assert oldint == InterpretIndex(oldindex);
    assert newint == InterpretIndex(newindex);
    
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
        assert llte == Keys.LargestLte(newindex.pivots, key);
      } else if llte + 1 == childidx {
      } else {
        var newllte := llte + 1;
        assert newllte == Keys.LargestLte(newindex.pivots, key);
        assert newindex.children[newllte+1] == oldindex.children[llte+1];
      }
    }

    forall key | key in newint
      ensures key in oldint
    {
      var llte := Keys.LargestLte(newindex.pivots, key);
      if llte + 1 < childidx {
        assert llte == Keys.LargestLte(oldindex.pivots, key);
      } else if llte + 1 == childidx {
        var oldllte := llte;
        assert oldllte == Keys.LargestLte(oldindex.pivots, key);
        assert key in InterpretNode(oldindex.children[Keys.LargestLte(oldindex.pivots, key) + 1]);
      } else if llte + 1 == childidx + 1 {
        var oldllte := llte - 1;
        assert oldllte == Keys.LargestLte(oldindex.pivots, key);
        assert key in InterpretNode(oldindex.children[Keys.LargestLte(oldindex.pivots, key) + 1]);
      } else {
        assert llte - 1 == Keys.LargestLte(oldindex.pivots, key);
      }
    }
  }
    
  function InsertLeaf(leaf: Node, key: Key, value: Value) : (result: Node)
    requires leaf.Leaf?
    requires WFLeaf(leaf)
    ensures result.Leaf?
    ensures WFLeaf(result)
  {
    var llte := Keys.LargestLte(leaf.keys, key);
    if 0 <= llte && leaf.keys[llte] == key then
      Leaf(leaf.keys, leaf.values[llte := value])
    else
      Keys.strictlySortedInsert(leaf.keys, key, llte);
      Leaf(Seq.insert(leaf.keys, key, llte+1), Seq.insert(leaf.values, value, llte+1))
  }

  lemma InsertLeafIsCorrect(leaf: Node, key: Key, value: Value, result: Node)
    requires leaf.Leaf?
    requires WFLeaf(leaf)
    requires result == InsertLeaf(leaf, key, value)
    ensures InterpretNode(result) == InterpretNode(leaf)[key := value]
  {
    var llte := Keys.LargestLte(leaf.keys, key);
    if 0 <= llte && leaf.keys[llte] == key {
      assert InterpretNode(result) == InterpretNode(leaf)[key := value];
    } else {
      Keys.reveal_IsStrictlySorted();
      forall k | k in InterpretNode(result).Keys
        ensures k in InterpretNode(leaf).Keys + {key}
      {
        var kpos := IndexOf(result.keys, k);
        if llte + 1 < kpos {
          assert k == leaf.keys[kpos-1];
        }
      }
    }
  }
}
