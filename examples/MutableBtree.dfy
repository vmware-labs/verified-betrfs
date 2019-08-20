include "../lib/NativeTypes.dfy"
include "../lib/total_order.dfy"
include "../lib/sequences.dfy"
include "../lib/Arrays.dfy"
include "../lib/Maps.dfy"

abstract module MutableBtree {
  import opened NativeTypes
  import opened Seq = Sequences
  import opened Maps
  import Arrays
  import Keys : Total_Order

  type Key = Keys.Element
  type Value
    
  datatype QueryResult =
    | Found(value: Value)
    | NotFound
    
  function method MaxKeysPerLeaf() : uint64
    ensures 1 < MaxKeysPerLeaf() as int < Uint64UpperBound() / 2

  function method MaxChildren() : uint64
    ensures 3 < MaxChildren() as int < Uint64UpperBound() / 2

  function method DefaultValue() : Value
  function method DefaultKey() : Key

  datatype ImmutableNode =
    | ImmutableLeaf(keys: seq<Key>, values: seq<Value>)
    | ImmutableIndex(pivots: seq<Key>, children: seq<ImmutableNode>)
  
  function AllKeysNode(node: ImmutableNode) : set<Key>
  {
    match node {
      case ImmutableLeaf(keys, values) => set k | k in keys
      case ImmutableIndex(pivots, children) => set i, k | 0 <= i < |children| && k in AllKeysNode(children[i]) :: k
    }    
  }
  
  predicate WFLeaf(leaf: ImmutableNode)
    requires leaf.ImmutableLeaf?
  {
    && |leaf.keys| == |leaf.values|
    && Keys.IsStrictlySorted(leaf.keys)
  }

  predicate WFIndex(index: ImmutableNode)
    requires index.ImmutableIndex?
    decreases index, 0
  {
    && |index.pivots| == |index.children| - 1
    && Keys.IsStrictlySorted(index.pivots)
    && (forall i :: 0 <= i < |index.children| ==> WFNode(index.children[i]))
    && (forall i :: 0 <= i < |index.children| ==> AllKeysNode(index.children[i]) != {})
    && (forall i, key :: 0 <= i < |index.children|-1 && key in AllKeysNode(index.children[i]) ==> Keys.lt(key, index.pivots[i]))
    && (forall i, key :: 0 < i < |index.children|   && key in AllKeysNode(index.children[i]) ==> Keys.lte(index.pivots[i-1], key))
  }

  predicate WFNode(node: ImmutableNode)
    decreases node, 1
  {
    match node {
      case ImmutableLeaf(_, _) =>  WFLeaf(node)
      case ImmutableIndex(_, _) => WFIndex(node)
    }
  }

  function InterpretLeaf(leaf: ImmutableNode) : map<Key, Value>
    requires leaf.ImmutableLeaf?
    requires WFLeaf(leaf)
  {
    Keys.PosEqLargestLteForAllElts(leaf.keys);
    map k | (k in leaf.keys) :: leaf.values[Keys.LargestLte(leaf.keys, k)]
  }

  function InterpretIndex(index: ImmutableNode) : map<Key, Value>
    requires index.ImmutableIndex?
    requires WFIndex(index)
    decreases index, 0
  {
    map key |
      && key in AllKeysNode(index)
      && key in InterpretNode(index.children[Keys.LargestLte(index.pivots, key) + 1])
      :: InterpretNode(index.children[Keys.LargestLte(index.pivots, key) + 1])[key]
  }

  function InterpretNode(node: ImmutableNode) : map<Key, Value>
    requires WFNode(node)
    decreases node, 1
  {
    match node {
      case ImmutableLeaf(_, _) => InterpretLeaf(node)
      case ImmutableIndex(_, _) => InterpretIndex(node)
    }
  }

  predicate SplitLeaf(oldleaf: ImmutableNode, leftleaf: ImmutableNode, rightleaf: ImmutableNode, pivot: Key)
  {
    && oldleaf.ImmutableLeaf?
    && leftleaf.ImmutableLeaf?
    && rightleaf.ImmutableLeaf?
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

  lemma SplitLeafInterpretation(oldleaf: ImmutableNode, leftleaf: ImmutableNode, rightleaf: ImmutableNode, pivot: Key)
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
  
  predicate SplitIndex(oldindex: ImmutableNode, leftindex: ImmutableNode, rightindex: ImmutableNode, pivot: Key)
  {
    && oldindex.ImmutableIndex?
    && leftindex.ImmutableIndex?
    && rightindex.ImmutableIndex?
    && WFIndex(oldindex)
    && WFIndex(leftindex)
    && WFIndex(rightindex)
    && oldindex.pivots == leftindex.pivots + [pivot] + rightindex.pivots
    && oldindex.children == leftindex.children + rightindex.children
  }

  lemma SplitIndexInterpretation(oldindex: ImmutableNode, leftindex: ImmutableNode, rightindex: ImmutableNode, pivot: Key)
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
      if Keys.lt(key, pivot) {
      } else {
      }
    }

    forall key | key in newint
      ensures MapsTo(oldint, key, newint[key])
    {
      if Keys.lt(key, pivot) {
        var llte := Keys.LargestLte(leftindex.pivots, key);
        assert oldindex.children[llte+1] == leftindex.children[llte+1];
      } else {
        var llte := Keys.LargestLte(rightindex.pivots, key);
        assert oldindex.children[|leftindex.children| + llte + 1] == rightindex.children[llte+1];
      }
    }
    
  }
  
  predicate SplitNode(oldnode: ImmutableNode, leftnode: ImmutableNode, rightnode: ImmutableNode, pivot: Key)
  {
    || SplitLeaf(oldnode, leftnode, rightnode, pivot)
    || SplitIndex(oldnode, leftnode, rightnode, pivot)
  }

  lemma SplitNodeInterpretation(oldnode: ImmutableNode, leftnode: ImmutableNode, rightnode: ImmutableNode, pivot: Key)
    requires SplitNode(oldnode, leftnode, rightnode, pivot)
    ensures InterpretNode(oldnode) == Keys.MapPivotedUnion(InterpretNode(leftnode), pivot, InterpretNode(rightnode))
  {
    if SplitLeaf(oldnode, leftnode, rightnode, pivot) {
      SplitLeafInterpretation(oldnode, leftnode, rightnode, pivot);
    } else {
      SplitIndexInterpretation(oldnode, leftnode, rightnode, pivot);
    }
  }
  
  predicate SplitChildOfIndex(oldindex: ImmutableNode, newindex: ImmutableNode, childidx: int)
  {
    && oldindex.ImmutableIndex?
    && newindex.ImmutableIndex?
    && WFNode(oldindex)
    && WFNode(newindex)
    && 0 <= childidx < |oldindex.children|
    && |newindex.children| == |oldindex.children| + 1 // FIXME: WTF?  Dafny can't get these from WFNode?
    && |newindex.pivots| == |oldindex.pivots| + 1
    && |oldindex.pivots| == |oldindex.children| - 1
    && newindex.pivots == Seq.insert(oldindex.pivots, newindex.pivots[childidx], childidx)
    && SplitNode(oldindex.children[childidx], newindex.children[childidx], newindex.children[childidx+1], newindex.pivots[childidx])
    && newindex.children == oldindex.children[..childidx] + [newindex.children[childidx], newindex.children[childidx+1]] + oldindex.children[childidx+1..]
  }

  lemma SplitChildOfIndexPreservesInterpretation(oldindex: ImmutableNode, newindex: ImmutableNode, childidx: int)
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
    
  function InsertLeaf(leaf: ImmutableNode, key: Key, value: Value) : (result: ImmutableNode)
    requires leaf.ImmutableLeaf?
    requires WFLeaf(leaf)
    ensures result.ImmutableLeaf?
    ensures WFLeaf(result)
  {
    var llte := Keys.LargestLte(leaf.keys, key);
    if 0 <= llte && leaf.keys[llte] == key then
      ImmutableLeaf(leaf.keys, leaf.values[llte := value])
    else
      Keys.strictlySortedInsert(leaf.keys, key, llte);
      ImmutableLeaf(Seq.insert(leaf.keys, key, llte+1), Seq.insert(leaf.values, value, llte+1))
  }

  lemma InsertLeafIsCorrect(leaf: ImmutableNode, key: Key, value: Value, result: ImmutableNode)
    requires leaf.ImmutableLeaf?
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
   
  trait Node {
    ghost var subtreeObjects: set<object>
      
    predicate WF()
      ensures WF() ==> this in subtreeObjects
      reads this, subtreeObjects
      decreases subtreeObjects, 0
      
    function ToImmutableNode() : (imnode: ImmutableNode)
      requires WF()
      ensures WFNode(imnode)
      reads this, subtreeObjects
      decreases subtreeObjects, 2
      
    function AllKeys() : set<Key>
      requires WF()
      reads this, subtreeObjects
      decreases subtreeObjects, 3
    {
      AllKeysNode(ToImmutableNode())
    }

    function Interpretation() : map<Key, Value>
      requires WF()
      reads this, subtreeObjects
      decreases subtreeObjects, 4
    {
      InterpretNode(ToImmutableNode())
    }
    
    // method Query(needle: Key) returns (result: QueryResult)
    //   requires WF()
    //   ensures needle in Interpretation() ==> result == Found(Interpretation()[needle])
    //   ensures needle !in Interpretation() ==> result == NotFound
    //   decreases subtreeObjects

    // predicate method Full()
    //   requires WF()
    //   reads this, subtreeObjects
      
    // predicate SplitEnsures(oldint: map<Key, Value>, pivot: Key, rightnode: Node)
    //   reads this, subtreeObjects
    //   reads rightnode, rightnode.subtreeObjects
    // {
    //   && WF()
    //   && !Full()
    //   && rightnode.WF()
    //   && !rightnode.Full()
    //   && SplitNode(old(ToImmutableNode()), 
    //   && Keys.MapPivotedUnion(Interpretation(), pivot, rightnode.Interpretation()) == oldint
    //   && AllKeys() != {}
    //   && rightnode.AllKeys() != {}
    //   && (forall key :: key in AllKeys() ==> Keys.lt(key, pivot))
    //   && (forall key :: key in rightnode.AllKeys() ==> Keys.lte(pivot, key))
    // }
      
    // method Split() returns (pivot: Key, rightnode: Node)
    //   requires WF()
    //   requires Full()
    //   ensures WF()
    //   ensures rightnode.WF()
    //   ensures SplitNode(old(ToImmutableNode()), ToImmutableNode(), rightnode.ToImmutableNode(), pivot)
    //   ensures !Full()
    //   ensures !rightnode.Full()
    //   ensures subtreeObjects <= old(subtreeObjects)
    //   ensures subtreeObjects !! rightnode.subtreeObjects
    //   ensures fresh(rightnode.subtreeObjects - old(subtreeObjects))
    //   modifies this

    // method Insert(key: Key, value: Value)
    //   requires WF()
    //   requires !Full()
    //   ensures WF()
    //   ensures Interpretation() == old(Interpretation())[key := value]
    //   ensures AllKeys() == old(AllKeys()) + {key}
    //   ensures fresh(subtreeObjects-old(subtreeObjects))
    //   modifies this, subtreeObjects
    //   decreases AllKeys()
      
  }

  datatype NodeBox = NodeBox(node: Node?)

  class Leaf extends Node {
    var nkeys : uint64
    var keys: array<Key>
    var values: array<Value>

    predicate WF()
      ensures WF() ==> this in subtreeObjects
      reads this, subtreeObjects
      decreases subtreeObjects, 0
    {
      && subtreeObjects == {this, keys, values}
      && keys != values
      && keys.Length == MaxKeysPerLeaf() as int
      && values.Length == MaxKeysPerLeaf() as int
      && 0 <= nkeys as int <= keys.Length
      && Keys.IsStrictlySorted(keys[..nkeys])
    }

    function ToImmutableNode() : (result: ImmutableNode)
      requires WF()
      ensures WFNode(result)
      //ensures result.ImmutableLeaf?
      reads this, subtreeObjects
      decreases subtreeObjects, 2
    {
      ImmutableLeaf(keys[..nkeys], values[..nkeys])
    }
    
    // method Query(needle: Key) returns (result: QueryResult)
    //   requires WF()
    //   ensures needle in Interpretation() ==> result == Found(Interpretation()[needle])
    //   ensures needle !in Interpretation() ==> result == NotFound
    //   decreases subtreeObjects
    // {
    //   //Keys.reveal_IsStrictlySorted();
    //   var posplus1: uint64 := Keys.ArrayLargestLtePlus1(keys, 0, nkeys, needle);
    //   if 1 <= posplus1 && keys[posplus1-1] == needle {
    //     result := Found(values[posplus1-1]);
    //   } else {
    //     result := NotFound;
    //   }
    // }

    // predicate method Full()
    //   requires WF()
    //   reads this, subtreeObjects
    // {
    //   nkeys >= MaxKeysPerLeaf()
    // }
    
    // method Split() returns (pivot: Key, rightnode: Node)
    //   requires WF()
    //   requires Full()
    //   ensures WF()
    //   ensures rightnode.WF()
    //   ensures SplitNode(old(ToImmutableNode()), ToImmutableNode(), rightnode.ToImmutableNode(), pivot)
    //   ensures !Full()
    //   ensures !rightnode.Full()
    //   ensures subtreeObjects <= old(subtreeObjects)
    //   ensures subtreeObjects !! rightnode.subtreeObjects
    //   ensures fresh(rightnode.subtreeObjects - old(subtreeObjects))
    //   modifies this
    // {
    //   var right := new Leaf();
    //   var boundary := nkeys/2;
    //   Arrays.Memcpy(right.keys, 0, keys[boundary..nkeys]); // FIXME: remove conversion to seq
    //   Arrays.Memcpy(right.values, 0, values[boundary..nkeys]); // FIXME: remove conversion to seq
    //   right.nkeys := nkeys - boundary;
    //   nkeys := boundary;
    //   pivot := right.keys[0];
    //   rightnode := right;

    //   assert keys[..nkeys] == old(keys[..nkeys])[..nkeys];
    //   Keys.StrictlySortedSubsequence(old(keys[..nkeys]), 0, nkeys as int);
    //   assert right.keys[..right.nkeys] == old(keys[..nkeys])[boundary..old(nkeys)];
    //   Keys.StrictlySortedSubsequence(old(keys[..nkeys]), boundary as int, old(nkeys) as int);
    //   Keys.reveal_IsStrictlySorted();
    //   assert SplitLeaf(old(ToImmutableNode()), ToImmutableNode(), rightnode.ToImmutableNode(), pivot);
    // }
      
    // method Insert(key: Key, value: Value)
    //   requires WF()
    //   requires !Full()
    //   ensures WF()
    //   ensures Interpretation() == old(Interpretation())[key := value]
    //   ensures AllKeys() == old(AllKeys()) + {key}
    //   ensures fresh(subtreeObjects-old(subtreeObjects))
    //   modifies this, subtreeObjects
    //   decreases AllKeys()
    // {
    //   var posplus1 := Keys.ArrayLargestLtePlus1(keys, 0, nkeys, key);

    //   if 1 <= posplus1 && keys[posplus1-1] == key {
    //     values[posplus1-1] := value;
    //   } else {
    //     ghost var oldkeys := keys[..nkeys];
    //     Arrays.Insert(keys, nkeys, key, posplus1);
    //     Arrays.Insert(values, nkeys, value, posplus1);
    //     nkeys := nkeys + 1;

    //     InsertMultiset(oldkeys, key, posplus1 as int); // OBSERVE
    //     Keys.strictlySortedInsert(oldkeys, key, posplus1 as int - 1); // OBSERVE
    //     Keys.PosEqLargestLte(keys[..nkeys], key, posplus1 as int);
    //     forall key' |  key' != key && key' in old(Interpretation())
    //       ensures key' in Interpretation() && Interpretation()[key'] == old(Interpretation())[key']
    //     {
    //       var i: int := Keys.LargestLte(old(keys[..nkeys]), key');
    //       //assert 0 <= i;
    //       if i < posplus1 as int {
    //         //assert keys[i] == key';
    //         Keys.PosEqLargestLte(keys[..nkeys], key', i);
    //       } else {
    //         //assert keys[i+1] == key';
    //         Keys.PosEqLargestLte(keys[..nkeys], key', i+1);
    //       }
    //     }
    //     forall key' | key' != key && key' in Interpretation()
    //       ensures key' in old(Interpretation()) && old(Interpretation())[key'] == Interpretation()[key']
    //     {
    //       var i: int := Keys.LargestLte(keys[..nkeys], key');
    //       if i < posplus1 as int {
    //         Keys.PosEqLargestLte(old(keys[..nkeys]), key', i);
    //       } else {
    //         Keys.PosEqLargestLte(old(keys[..nkeys]), key', i-1);
    //       }
    //     }
    //   }
    // }

    // constructor()
    //   ensures WF()
    //   ensures Interpretation() == map[]
    //   ensures !Full()
    //   ensures fresh(keys)
    //   ensures fresh(values)
    // {
    //   nkeys := 0;
    //   keys := new Key[MaxKeysPerLeaf()](_ => DefaultKey());
    //   values := new Value[MaxKeysPerLeaf()](_ => DefaultValue());
    //   subtreeObjects := {this, keys, values};
    // }
  }

  class Index extends Node {
    var nchildren: uint64
    var pivots: array<Key>
    var children: array<NodeBox>

    predicate WF()
      ensures WF() ==> this in subtreeObjects
      reads this, subtreeObjects
      decreases subtreeObjects, 0
    {
      && {this, pivots, children} <= subtreeObjects
      && pivots.Length == (MaxChildren() as int) - 1
      && children.Length == MaxChildren() as int
      && 1 < nchildren <= MaxChildren()
      && (forall i :: 0 <= i < nchildren ==> children[i].node != null)
      && (forall i :: 0 <= i < nchildren ==> children[i].node in subtreeObjects)
      && (forall i {:trigger children[i].node.subtreeObjects} :: 0 <= i < nchildren as int ==> children[i].node.subtreeObjects < subtreeObjects)
      && (forall i {:trigger children[i].node.subtreeObjects} :: 0 <= i < nchildren as int ==> {this, pivots, children} !! children[i].node.subtreeObjects)
      && (forall i, j {:trigger children[i].node.subtreeObjects, children[j].node.subtreeObjects} :: 0 <= i < j < nchildren as int ==> children[i].node.subtreeObjects !! children[j].node.subtreeObjects)
      
      && Keys.IsStrictlySorted(pivots[..nchildren-1])
      && (forall i :: 0 <= i < nchildren ==> children[i].node.WF())
      && (forall i :: 0 <= i < nchildren ==> children[i].node.AllKeys() != {})
      && (forall i, key :: 0 <= i < nchildren-1 && key in children[i].node.AllKeys() ==> Keys.lt(key, pivots[i]))
      && (forall i, key :: 0 < i < nchildren   && key in children[i].node.AllKeys() ==> Keys.lte(pivots[i-1], key))
    }

    // static function SeqSubtreeObjects(nodes: seq<NodeBox>) : (result: set<object>)
    //   requires forall i :: 0 <= i < |nodes| ==> nodes[i].node != null
    //   reads set i | 0 <= i < |nodes| :: nodes[i].node
    // {
    //   set i, o | 0 <= i < |nodes| && o in nodes[i].node.subtreeObjects :: o
    // }

    // lemma SeqSubtreeObjectsDecreasing()
    //   requires WF()
    //   requires 1 < nchildren
    //   ensures forall i :: 0 <= i < nchildren ==> children[i].node.subtreeObjects < SeqSubtreeObjects(children[..nchildren])
    //   decreases subtreeObjects, 1
    // {
    //   forall i | 0 <= i < nchildren
    //     ensures children[i].node.subtreeObjects < SeqSubtreeObjects(children[..nchildren])
    //   {
    //     if 0 < i {
    //       assert children[i-1].node.WF();
    //       assert children[i-1].node !in children[i].node.subtreeObjects;
    //     } else {
    //       assert children[i+1].node.WF();
    //       assert children[i+1].node !in children[i].node.subtreeObjects;
    //     }
    //   }
    // }
    
    // static function SeqToImmutableNodeSeq(nodes: seq<NodeBox>) : (result: seq<ImmutableNode>)
    //   requires forall i :: 0 <= i < |nodes| ==> nodes[i].node != null
    //   requires forall i :: 0 <= i < |nodes| ==> nodes[i].node.subtreeObjects < SeqSubtreeObjects(nodes)
    //   requires forall i :: 0 <= i < |nodes| ==> nodes[i].node.WF()
    //   reads set i | 0 <= i < |nodes| :: nodes[i].node
    //   reads SeqSubtreeObjects(nodes)
    //   decreases SeqSubtreeObjects(nodes)
    // {
    //   if nodes == [] then
    //     []
    //   else
    //     assert Last(nodes).node.subtreeObjects < SeqSubtreeObjects(nodes);
    //     SeqToImmutableNodeSeq(DropLast(nodes)) + [Last(nodes).node.ToImmutableNode()]
    // }
    
    function ToImmutableNode() : (imnode: ImmutableNode)
      requires WF()
      ensures WFNode(imnode)
      reads this, subtreeObjects
      decreases subtreeObjects, 2
    // {
    //   var impivots := pivots[..nchildren-1];
    //   SeqSubtreeObjectsDecreasing();
    //   assert SeqSubtreeObjects(children[..nchildren]) < subtreeObjects;
    //   var imchildren := SeqToImmutableNodeSeq(children[..nchildren]);
    //   ImmutableIndex(impivots, imchildren)
    // }
    
    // lemma AllKeysStrictlyDecreasing()
    //   requires WF()
    //   ensures forall i :: 0 <= i < nchildren ==> children[i].node.allKeys < allKeys
    // {
    //   forall i | 0 <= i < nchildren
    //     ensures children[i].node.allKeys < allKeys
    //   {
    //     var i' := if i < nchildren-1 then i+1 else 0;
    //     assert i' != i;
    //     assert children[i].node.allKeys !! children[i'].node.allKeys;
    //     assert children[i].node.allKeys <= 
    //     assert children[i].node.allKeys <= allKeys;
    //   }
    // }
    
    // method Query(needle: Key) returns (result: QueryResult)
    //   requires WF()
    //   ensures needle in Interpretation() ==> result == Found(Interpretation()[needle])
    //   ensures needle !in Interpretation() ==> result == NotFound
    //   // ensures result == QueryDef(needle)
    //   decreases subtreeObjects
    // {
    //   var posplus1 := Keys.ArrayLargestLtePlus1(pivots, 0, nchildren-1, needle);
    //   result := children[posplus1].node.Query(needle);
    // }

    // predicate method Full()
    //   requires WF()
    //   reads this, subtreeObjects
    // {
    //   nchildren == MaxChildren()
    // }

    // method SplitChild(key: Key, childidx: uint64)
    //   requires WF()
    //   requires !Full()
    //   requires childidx as int == 1 + Keys.LargestLte(pivots[..nchildren-1], key)
    //   requires children[childidx].node.Full()
    //   ensures WF()
    //   //ensures Interpretation() == old(Interpretation())
    //   ensures SplitChildOfIndex(old(ToImmutableNode()), ToImmutableNode(), childidx as int)
    //   ensures fresh(subtreeObjects-old(subtreeObjects))
    //   modifies this, pivots, children, children[childidx].node
    // {
    //   ghost var oldchildren := children;
      
    //   var pivot, right := children[childidx].node.Split();
    //   Arrays.Insert(pivots, nchildren - 1, pivot, childidx);
    //   Arrays.Insert(children, nchildren, NodeBox(right), childidx + 1);
    //   nchildren := nchildren + 1;
    //   subtreeObjects := subtreeObjects + right.subtreeObjects;

      
    //   // Keys.LargestLteIsUnique(old(pivots[..nchildren-1]), pivot, childidx as int - 1);
    //   // Keys.strictlySortedInsert(old(pivots[..nchildren-1]), pivot, childidx as int - 1);

    //   assert forall i: uint64 :: 0 <= i < childidx ==> children[i] == oldchildren[i];
    //   assert children[childidx as int + 1].node == right;
    //   assert forall i: uint64 :: childidx + 1 < i < nchildren ==> children[i] == oldchildren[i-1];
    //   // forall i: int, j: int {:trigger children[i].node.subtreeObjects, children[j].node.subtreeObjects}
    //   // | 0 <= i < j < nchildren as int
    //   //   ensures children[i].node.subtreeObjects !! children[j].node.subtreeObjects
    //   // {
    //   //   if                                   j  < childidx as int {
    //   //   } else if                            j == childidx as int {
    //   //   } else if i  < childidx as int     && j == childidx as int + 1 {
    //   //   } else if i == childidx as int     && j == childidx as int + 1 {
    //   //   } else if i  < childidx as int     && j  > childidx as int + 1 {
    //   //   } else if i == childidx as int     && j  > childidx as int + 1 {
    //   //   } else if i == childidx as int + 1 && j  > childidx as int + 1 {
    //   //   } else {
    //   //   }
    //   // }
    //   // // forall i: int, key | 0 <= i < (nchildren as int)-1 && key in children[i].node.allKeys
    //   // //   ensures Keys.lt(key, pivots[i])
    //   // // {
    //   // //   if childidx as int + 1 < i {
    //   // //     assert children[i] == old(children[i-1]);
    //   // //   }
    //   // // }
    //   // // forall i: int, key | 0 < i < nchildren as int && key in children[i].node.allKeys
    //   // //   ensures Keys.lt(pivots[i-1], key)
    //   // // {
    //   // //   if i < childidx as int {
    //   // //     assert Keys.lt(pivots[i-1], key);
    //   // //   } else if i == childidx as int {
    //   // //     assert Keys.lt(pivots[i-1], key);
    //   // //   } else if i == childidx as int + 1 {
    //   // //     assert Keys.lt(pivots[i-1], key);
    //   // //   } else {
    //   // //     assert Keys.lt(pivots[i-1], key);
    //   // //   }
    //   // // }
    //   // assert WF();
        
    //   // forall key | key in old(Interpretation())
    //   //   ensures key in Interpretation() && Interpretation()[key] == old(Interpretation()[key])
    //   // {
    //   //   var llte: int := Keys.LargestLte(old(pivots[..nchildren-1]), key);
    //   //   assert key in old(children[llte+1].node.Interpretation());
    //   //   assert old(children[llte+1].node.Interpretation()[key]) == old(Interpretation()[key]);
    //   //   if llte < childidx as int {
    //   //     assert key in Interpretation() && Interpretation()[key] == old(Interpretation()[key]);
    //   //   } else if llte == childidx as int {
    //   //     if Keys.lt(key, pivot) {
    //   //       assert key in Interpretation() && Interpretation()[key] == old(Interpretation()[key]);
    //   //     } else {
    //   //       assert key in Interpretation() && Interpretation()[key] == old(Interpretation()[key]);
    //   //     }
    //   //   } else {
    //   //     assert key in Interpretation() && Interpretation()[key] == old(Interpretation()[key]);
    //   //   }
    //   // }
    //   // forall key | key in Interpretation()
    //   //   ensures key in old(Interpretation()) && Interpretation()[key] == old(Interpretation()[key])
    //   // {
    //   //   var llte: int := Keys.LargestLte(pivots[..nchildren-1], key);
    //   //   if llte < childidx as int {
    //   //   } else if llte == childidx as int {
    //   //   } else if llte == childidx as int + 1 {
    //   //   } else {
    //   //   }
    //   // }
    // }
    
    // function UnionSubtreeObjects() : set<object>
    //   requires nchildren as int <= children.Length
    //   requires forall i :: 0 <= i < nchildren ==> children[i].node != null
    //   reads this, children, set i | 0 <= i < nchildren :: children[i].node
    // {
    //   set o, i | 0 <= i < nchildren && o in children[i].node.subtreeObjects :: o
    // }
    
    // method Split() returns (pivot: Key, rightnode: Node)
    //   requires WF()
    //   requires Full()
    //   ensures WF()
    //   ensures rightnode.WF()
    //   ensures SplitNode(old(ToImmutableNode()), ToImmutableNode(), rightnode.ToImmutableNode(), pivot)
    //   ensures !Full()
    //   ensures !rightnode.Full()
    //   ensures subtreeObjects <= old(subtreeObjects)
    //   ensures subtreeObjects !! rightnode.subtreeObjects
    //   ensures fresh(rightnode.subtreeObjects - old(subtreeObjects))
    //   modifies this      
    // {
    //   var right := new Index();
    //   var boundary := nchildren/2;
    //   Arrays.Memcpy(right.pivots, 0, pivots[boundary..nchildren-1]); // FIXME: remove conversion to seq
    //   Arrays.Memcpy(right.children, 0, children[boundary..nchildren]); // FIXME: remove conversion to seq
    //   right.nchildren := nchildren - boundary;
    //   nchildren := boundary;
    //   subtreeObjects := {this, pivots, children} + UnionSubtreeObjects();
    //   right.subtreeObjects := right.subtreeObjects + right.UnionSubtreeObjects();

    //   pivot := pivots[boundary-1];

    //   rightnode := right;
      
    //   // Keys.reveal_IsStrictlySorted();
    //   // assert WF();
    //   // assert rightnode.WF();
    //   // assert MergeMaps(Interpretation(), pivot, rightnode.Interpretation()) == old(Interpretation());
    // }

    // // method Insert(key: Key, value: Value)
    // //   requires WF()
    // //   requires !Full()
    // //   ensures WF()
    // //   ensures Interpretation() == old(Interpretation())[key := value]
    // //   ensures allKeys == old(allKeys) + {key}
    // //   ensures fresh(subtreeObjects - old(subtreeObjects))
    // //   modifies this, subtreeObjects
    // //   decreases allKeys
    // // {
    // //   var posplus1 := Keys.ArrayLargestLtePlus1(pivots, 0, nchildren - 1, key);
    // //   var childidx := (posplus1) as uint64;
    // //   if children[posplus1].node.Full() {
    // //     childidx := SplitChild(key, childidx);
    // //   }
    // //   //AllKeysStrictlyDecreasing();
    // //   children[childidx].node.Insert(key, value);
    // //   subtreeObjects := subtreeObjects + children[childidx].node.subtreeObjects;
    // //   allKeys := allKeys + {key};
    // //   forall key' | key' in old(Interpretation()) && key' != key
    // //     ensures key' in Interpretation() && Interpretation()[key'] == old(Interpretation()[key'])
    // //   {
    // //     var i :| 0 <= i < old(nchildren) && key' in old(children[i].node.Interpretation());
    // //   }
      
    // // }

    // constructor()
    //   ensures nchildren == 0
    //   ensures pivots.Length == (MaxChildren() as int)-1
    //   ensures children.Length == (MaxChildren() as int)
    //   ensures forall i :: 0 <= i < children.Length ==> children[i].node == null
    //   ensures subtreeObjects == {this, pivots, children}
    //   ensures fresh(pivots)
    //   ensures fresh(children)
    // {
    //   pivots := new Key[MaxChildren()-1](_ => DefaultKey());
    //   children := new NodeBox[MaxChildren()](_ => NodeBox(null));
    //   nchildren := 0;
    //   subtreeObjects := {this, pivots, children};
    // }
  }

  // class MutableBtree {
  //   var root: Node

  //   function Interpretation() : map<Key, Value>
  //     requires root.WF()
  //     reads this, root, root.subtreeObjects
  //   {
  //     root.Interpretation()
  //   }

  //   method Query(needle: Key) returns (result: QueryResult)
  //     requires root.WF()
  //     ensures result == NotFound ==> needle !in Interpretation()
  //     ensures result.Found? ==> needle in Interpretation() && Interpretation()[needle] == result.value
  //   {
  //     result := root.Query(needle);
  //   }

  //   method Insert(key: Key, value: Value)
  //     requires root.WF()
  //     ensures root.WF()
  //     ensures Interpretation() == old(Interpretation())[key := value]
  //     modifies this, root, root.subtreeObjects
  //   {
  //     if root.Full() {
  //       var newroot := new Index();
  //       newroot.children[0] := NodeBox(root);
  //       newroot.nchildren := 1;
  //       newroot.subtreeObjects := newroot.subtreeObjects + root.subtreeObjects;
  //       newroot.allKeys := root.allKeys;
  //       root := newroot;
  //     }
  //     AssumeFalse();
  //     root.Insert(key, value);
  //   }
    
  //   constructor()
  //     ensures root.WF()
  //     ensures Interpretation() == map[]
  //   {
  //     root := new Leaf();
  //   }
  // }
}

// module TestMutableBtree refines MutableBtree {
//   import Keys = Uint64_Order
//   type Value = uint64

//   function method MaxKeysPerLeaf() : uint64 { 64 }
//   function method MaxChildren() : uint64 { 64 }

//   function method DefaultValue() : Value { 0 }
//   function method DefaultKey() : Key { 0 }
// }

// module MainModule {
//   import opened NativeTypes
//   import TestMutableBtree
    
//   method Main()
//   {
//     // var n: uint64 := 1_000_000;
//     // var p: uint64 := 300_007;
//     var n: uint64 := 10_000_000;
//     var p: uint64 := 3_000_017;
//     // var n: uint64 := 100_000_000;
//     // var p: uint64 := 1_073_741_827;
//     var t := new TestMutableBtree.MutableBtree();
//     var i: uint64 := 0;
//     while i < n
//       invariant 0 <= i <= n
//       invariant t.root.WF()
//       modifies t, t.root, t.root.subtreeObjects
//     {
//       t.Insert((i * p) % n , i);
//       i := i + 1;
//     }

//     // i := 0;
//     // while i < n
//     //   invariant 0 <= i <= n
//     // {
//     //   var needle := (i * p) % n;
//     //   var qr := t.Query(needle);
//     //   if qr != TestMutableBtree.Found(i) {
//     //     print "Test failed";
//   //   } else {
//   //     //print "Query ", i, " for ", needle, "resulted in ", qr.value, "\n";
//   //   }
//   //   i := i + 1;
//   // }

//   // i := 0;
//   // while i < n
//   //   invariant 0 <= i <= n
//   // {
//   //   var qr := t.Query(n + ((i * p) % n));
//   //   if qr != TestMutableBtree.NotFound {
//   //     print "Test failed";
//   //   } else {
//   //     //print "Didn't return bullsh*t\n";
//   //   }
//   //   i := i + 1;
//   // }
//     print "PASSED\n";
//   }
// } 
