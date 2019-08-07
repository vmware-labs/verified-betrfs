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

  lemma AssumeFalse()
    //ensures false
  {
    //assert false;
  }

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

  // lemma SplitLeafAllKeys(oldleaf: ImmutableNode, leftleaf: ImmutableNode, rightleaf: ImmutableNode, pivot: Key)
  //   requires SplitLeaf(oldleaf, leftleaf, rightleaf, pivot)
  //   ensures AllKeysNode(oldleaf) == AllKeysNode(leftleaf) + AllKeysNode(rightleaf)
  //   ensures AllKeysNode(leftleaf) == set k | k in AllKeysNode(oldleaf) && Keys.lt(k, pivot)
  //   ensures AllKeysNode(rightleaf) == set k | k in AllKeysNode(oldleaf) && Keys.lte(pivot, k)
  // {
  //   Keys.reveal_IsStrictlySorted();
  // }

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

  // lemma SplitIndexAllKeys(oldindex: ImmutableNode, leftindex: ImmutableNode, rightindex: ImmutableNode, pivot: Key)
  //   requires SplitIndex(oldindex, leftindex, rightindex, pivot)
  //   ensures AllKeysNode(oldindex) == AllKeysNode(leftindex) + AllKeysNode(rightindex)
  //   ensures AllKeysNode(leftindex) == set k | k in AllKeysNode(oldindex) && Keys.lt(k, pivot)
  //   ensures AllKeysNode(rightindex) == set k | k in AllKeysNode(oldindex) && Keys.lte(pivot, k)
  // {
  //   assert AllKeysNode(oldindex) <= AllKeysNode(leftindex) + AllKeysNode(rightindex);
  //   forall key | key in AllKeysNode(leftindex) + AllKeysNode(rightindex)
  //     ensures key in AllKeysNode(oldindex)
  //   {
  //     if key in AllKeysNode(leftindex) {
  //       var i :| 0 <= i < |leftindex.children| && key in AllKeysNode(leftindex.children[i]);
  //       assert key in AllKeysNode(oldindex.children[i]);
  //     } else {
  //       var i :| 0 <= i < |rightindex.children| && key in AllKeysNode(rightindex.children[i]);
  //       assert key in AllKeysNode(oldindex.children[|leftindex.children|+i]);
  //     }
  //   }
  //   forall key | key in AllKeysNode(leftindex)
  //     ensures Keys.lt(key, pivot)
  //   {
      
  //   }
  //   assert AllKeysNode(leftindex) <= set k | k in AllKeysNode(oldindex) && Keys.lt(k, pivot);
  //   assert AllKeysNode(leftindex) >= set k | k in AllKeysNode(oldindex) && Keys.lt(k, pivot);
  //   assert AllKeysNode(rightindex) <= set k | k in AllKeysNode(oldindex) && Keys.lte(pivot, k);
  //   assert AllKeysNode(rightindex) >= set k | k in AllKeysNode(oldindex) && Keys.lte(pivot, k);
  // }
  
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
      } else {
      }
    }
    
  }
  
  predicate SplitNode(oldnode: ImmutableNode, leftnode: ImmutableNode, rightnode: ImmutableNode, pivot: Key)
  {
    || SplitLeaf(oldnode, leftnode, rightnode, pivot)
    || SplitIndex(oldnode, leftnode, rightnode, pivot)
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
    
    assert WFIndex(oldindex); // WTF?  Dafny can't see these (from emacs flycheck mode)
    assert WFIndex(newindex);

    forall key | key in oldint
      ensures key in newint && newint[key] == oldint[key]
    {
      assert key in InterpretIndex(oldindex);
      var llte := Keys.LargestLte(oldindex.pivots, key);
      var oldchild := oldindex.children[llte+1];
      var oldchildint := InterpretNode(oldchild);
      assert key in oldchildint;
      assert oldint[key] == oldchildint[key];
      if llte + 1 < childidx {
        var newllte := llte;
        assert newllte == Keys.LargestLte(newindex.pivots, key);
        var newchildint := InterpretNode(newindex.children[newllte+1]);
        assert newindex.children[newllte+1] == oldindex.children[llte+1];
        assert newchildint == oldchildint;
        assert key in newchildint;
        assert key in AllKeysNode(newindex);
        assert newint == InterpretIndex(newindex);
        assert key in newint;
        assert newint[key] == newchildint[key];
      } else if llte + 1 == childidx {
        assert key in AllKeysNode(oldchild);
        var leftchild := newindex.children[childidx];
        var rightchild := newindex.children[childidx+1];
        assert key in AllKeysNode(leftchild) + AllKeysNode(rightchild);
        if Keys.lt(key, newindex.pivots[childidx]) {
          var newllte := llte;
          assert newllte == Keys.LargestLte(newindex.pivots, key);
          var newchild := leftchild;
          var newchildint := InterpretNode(newchild);
          assert key in AllKeysNode(newchild);
          assert key in newchildint;
          assert key in newint;
          assert newint[key] == newchildint[key];
        } else {
          var newllte := llte + 1;
          assert newllte == Keys.LargestLte(newindex.pivots, key);
          assume false;
        }
      } else {
        var newllte := llte + 1;
        assert newllte == Keys.LargestLte(newindex.pivots, key);
        var newchildint := InterpretNode(newindex.children[newllte+1]);
        assert newindex.children[newllte+1] == oldindex.children[llte+1];
        assert newchildint == oldchildint;
        assert key in newchildint;
        assert key in AllKeysNode(newindex);
        assert newint == InterpretIndex(newindex);
        assert key in newint;
        assert newint[key] == newchildint[key];
      }
    }

    forall key | key in newint
      ensures key in oldint
    {
      assume false;
    }
  }
    
//   trait Node {
//     ghost var subtreeObjects: set<object>
//     ghost var allKeys: set<Key>

//     function ToImmutableNode() : ImmutableNode
//       reads this, subtreeObjects
//       decreases subtreeObjects, 0
      
//     predicate WF()
//       reads this, subtreeObjects
//       ensures WF() ==> this in subtreeObjects
//       decreases subtreeObjects, 0

//     // function QueryDef(needle: Key) : QueryResult
//     //   requires WF()
//     //   reads this, subtreeObjects
//     //   decreases subtreeObjects
      
//     function Interpretation() : map<Key, Value>
//       requires WF()
//       // ensures forall key :: QueryDef(key).Found? ==> MapsTo(Interpretation(), key, QueryDef(key).value)
//       // ensures forall key :: QueryDef(key).NotFound? ==> key !in Interpretation()
//       reads this, subtreeObjects
//       decreases subtreeObjects

//     method Query(needle: Key) returns (result: QueryResult)
//       requires WF()
//       //ensures result == QueryDef(needle)
//       ensures needle in Interpretation() ==> result == Found(Interpretation()[needle])
//       ensures needle !in Interpretation() ==> result == NotFound
//       decreases subtreeObjects

//     predicate method Full()
//       requires WF()
//       reads this, subtreeObjects
      
//     method Insert(key: Key, value: Value)
//       requires WF()
//       requires !Full()
//       ensures WF()
//       ensures Interpretation() == old(Interpretation())[key := value]
//       ensures allKeys == old(allKeys) + {key}
//       ensures fresh(subtreeObjects-old(subtreeObjects))
//       modifies this, subtreeObjects
//       decreases allKeys
      
//     predicate SplitEnsures(oldint: map<Key, Value>, pivot: Key, rightnode: Node)
//       reads this, subtreeObjects
//       reads rightnode, rightnode.subtreeObjects
//     {
//       && WF()
//       && !Full()
//       && rightnode.WF()
//       && !rightnode.Full()
//       && MergeMaps(Interpretation(), pivot, rightnode.Interpretation()) == oldint
//       && allKeys != {}
//       && rightnode.allKeys != {}
//       && (forall key :: key in allKeys ==> Keys.lt(key, pivot))
//       && (forall key :: key in rightnode.allKeys ==> Keys.lte(pivot, key))
//     }
      
//     method Split() returns (ghost wit: Key, pivot: Key, rightnode: Node)
//       requires WF()
//       requires Full()
//       ensures SplitEnsures(old(Interpretation()), pivot, rightnode)
//       ensures allKeys <= old(allKeys)
//       ensures rightnode.allKeys <= old(allKeys)
//       ensures pivot in old(allKeys)
//       ensures wit in old(allKeys)
//       ensures Keys.lt(wit, pivot)
//       ensures subtreeObjects <= old(subtreeObjects)
//       ensures subtreeObjects !! rightnode.subtreeObjects
//       ensures fresh(rightnode.subtreeObjects - old(subtreeObjects))
//       modifies this
//   }

//   datatype NodeBox = NodeBox(node: Node?)

//   class Leaf extends Node {
//     var nkeys : uint64
//     var keys: array<Key>
//     var values: array<Value>

//     function ToImmutableNode() : (result: ImmutableNode)
//       ensures result.ImmutableLeaf?
//       reads this, subtreeObjects
//       decreases subtreeObjects, 0
//     {
//       ImmutableLeaf(allKeys, keys[..nkeys], values[..nkeys])
//     }
    
//     predicate WF()
//       reads this, subtreeObjects
//       ensures WFLEaf() ==> this in subtreeObjects
//       decreases subtreeObjects, 0
//     {
//       && subtreeObjects == {this, keys, values}
//       && keys != values
//       && keys.Length == MaxKeysPerLeaf() as int
//       && values.Length == MaxKeysPerLeaf() as int
//       && 0 <= nkeys <= keys.Length as uint64
//       && WFLeaf(ToImmutableNode())
//     }

//     function Interpretation() : map<Key, Value>
//       requires WF()
//       reads this, subtreeObjects
//       decreases subtreeObjects
//     {
//       InterpretationLeaf(ToImmutableNode())
//     }

//     method Query(needle: Key) returns (result: QueryResult)
//       requires WF()
//       ensures needle in Interpretation() ==> result == Found(Interpretation()[needle])
//       ensures needle !in Interpretation() ==> result == NotFound
//       //ensures result == QueryDef(needle)
//       decreases subtreeObjects
//     {
//       //Keys.reveal_IsStrictlySorted();
//       var posplus1: uint64 := Keys.ArrayLargestLtePlus1(keys, 0, nkeys, needle);
//       if 1 <= posplus1 && keys[posplus1-1] == needle {
//         result := Found(values[posplus1-1]);
//       } else {
//         result := NotFound;
//       }
//     }

//     predicate method Full()
//       requires WF()
//       reads this, subtreeObjects
//     {
//       nkeys >= MaxKeysPerLeaf()
//     }
    
//     method Insert(key: Key, value: Value)
//       requires WF()
//       requires !Full()
//       ensures WF()
//       ensures Interpretation() == old(Interpretation())[key := value]
//       ensures allKeys == old(allKeys) + {key}
//       ensures fresh(subtreeObjects-old(subtreeObjects))
//       modifies this, subtreeObjects
//       decreases allKeys
//     {
//       var posplus1 := Keys.ArrayLargestLtePlus1(keys, 0, nkeys, key);

//       if 1 <= posplus1 && keys[posplus1-1] == key {
//         values[posplus1-1] := value;
//       } else {
//         ghost var oldkeys := keys[..nkeys];
//         Arrays.Insert(keys, nkeys, key, posplus1);
//         Arrays.Insert(values, nkeys, value, posplus1);
//         nkeys := nkeys + 1;
//         allKeys := allKeys + {key};

//         InsertMultiset(oldkeys, key, posplus1 as int); // OBSERVE
//         Keys.strictlySortedInsert(oldkeys, key, posplus1 as int - 1); // OBSERVE
//         Keys.PosEqLargestLte(keys[..nkeys], key, posplus1 as int);
//         forall key' |  key' != key && key' in old(Interpretation())
//           ensures key' in Interpretation() && Interpretation()[key'] == old(Interpretation())[key']
//         {
//           var i: int := Keys.LargestLte(old(keys[..nkeys]), key');
//           //assert 0 <= i;
//           if i < posplus1 as int {
//             //assert keys[i] == key';
//             Keys.PosEqLargestLte(keys[..nkeys], key', i);
//           } else {
//             //assert keys[i+1] == key';
//             Keys.PosEqLargestLte(keys[..nkeys], key', i+1);
//           }
//         }
//         forall key' | key' != key && key' in Interpretation()
//           ensures key' in old(Interpretation()) && old(Interpretation())[key'] == Interpretation()[key']
//         {
//           var i: int := Keys.LargestLte(keys[..nkeys], key');
//           if i < posplus1 as int {
//             Keys.PosEqLargestLte(old(keys[..nkeys]), key', i);
//           } else {
//             Keys.PosEqLargestLte(old(keys[..nkeys]), key', i-1);
//           }
//         }
//       }
//     }

//     method Split() returns (ghost wit: Key, pivot: Key, rightnode: Node)
//       requires WF()
//       requires Full()
//       ensures SplitEnsures(old(Interpretation()), pivot, rightnode)
//       ensures allKeys <= old(allKeys)
//       ensures rightnode.allKeys <= old(allKeys)
//       ensures pivot in old(allKeys)
//       ensures wit in old(allKeys)
//       ensures Keys.lt(wit, pivot)
//       ensures subtreeObjects <= old(subtreeObjects)
//       ensures subtreeObjects !! rightnode.subtreeObjects
//       ensures fresh(rightnode.subtreeObjects - old(subtreeObjects))
//       modifies this
//     {
//       var right := new Leaf();
//       var boundary := nkeys/2;
//       Arrays.Memcpy(right.keys, 0, keys[boundary..nkeys]); // FIXME: remove conversion to seq
//       Arrays.Memcpy(right.values, 0, values[boundary..nkeys]); // FIXME: remove conversion to seq
//       right.nkeys := nkeys - boundary;
//       nkeys := boundary;
//       allKeys := set key | key in multiset(keys[..nkeys]);
//       right.allKeys := set key | key in multiset(right.keys[..right.nkeys]);
//       assert keys[0] in allKeys;
//       assert right.keys[0] in right.allKeys;
//       wit := keys[0];
//       pivot := right.keys[0];
//       rightnode := right;

//       assert keys[..nkeys] == old(keys[..nkeys])[..nkeys];
//       Keys.StrictlySortedSubsequence(old(keys[..nkeys]), 0, nkeys as int);
//       assert WF();
//       assert right.keys[..right.nkeys] == old(keys[..nkeys])[boundary..old(nkeys)];
//       Keys.StrictlySortedSubsequence(old(keys[..nkeys]), boundary as int, old(nkeys) as int);
//       assert Keys.IsStrictlySorted(right.keys[..right.nkeys]);
//       assert right.WF();
//       Keys.IsStrictlySortedImpliesLt(old(keys[..nkeys]), 0, boundary as int);
//       forall i | 0 <= i < nkeys
//         ensures Keys.lt(keys[i], pivot)
//       {
//         Keys.IsStrictlySortedImpliesLt(old(keys[..nkeys]), i as int, boundary as int);
//       }
//       ghost var mergedint := MergeMaps(Interpretation(), pivot, rightnode.Interpretation());
//       forall key | key in old(Interpretation())
//         ensures key in mergedint && mergedint[key] == old(Interpretation())[key]
//       {
//         if Keys.lt(key, pivot) {
//           assert Keys.LargestLte(old(keys[..nkeys]), key) < boundary as int;
//         } else {
//         }
//       }
//     }
      
//     constructor()
//       ensures WF()
//       ensures Interpretation() == map[]
//       ensures !Full()
//       ensures fresh(keys)
//       ensures fresh(values)
//     {
//       nkeys := 0;
//       keys := new Key[MaxKeysPerLeaf()](_ => DefaultKey());
//       values := new Value[MaxKeysPerLeaf()](_ => DefaultValue());
//       allKeys := {};
//       subtreeObjects := {this, keys, values};
//     }
//   }

//   class Index extends Node {
//     var nchildren: uint64
//     var pivots: array<Key>
//     var children: array<NodeBox>

//     predicate WF()
//       reads this, subtreeObjects
//       ensures WF() ==> this in subtreeObjects
//       decreases subtreeObjects, 0
//     {
//       && {this, pivots, children} <= subtreeObjects
//       && pivots.Length == (MaxChildren() as int) - 1
//       && children.Length == MaxChildren() as int
//       && 1 <= nchildren <= MaxChildren()
//       && (forall i :: 0 <= i < nchildren ==> children[i].node != null)
//       && (forall i :: 0 <= i < nchildren ==> children[i].node in subtreeObjects)
//       && (forall i {:trigger children[i].node.subtreeObjects} :: 0 <= i < nchildren as int ==> children[i].node.subtreeObjects < subtreeObjects)
//       && (forall i {:trigger children[i].node.subtreeObjects} :: 0 <= i < nchildren as int ==> {this, pivots, children} !! children[i].node.subtreeObjects)
//       && (forall i, j {:trigger children[i].node.subtreeObjects, children[j].node.subtreeObjects} :: 0 <= i < j < nchildren as int ==> children[i].node.subtreeObjects !! children[j].node.subtreeObjects)
//       && WFIndex(ToImmutableNode())
//     }

//     // lemma AllKeysStrictlyDecreasing()
//     //   requires WF()
//     //   ensures forall i :: 0 <= i < nchildren ==> children[i].node.allKeys < allKeys
//     // {
//     //   forall i | 0 <= i < nchildren
//     //     ensures children[i].node.allKeys < allKeys
//     //   {
//     //     var i' := if i < nchildren-1 then i+1 else 0;
//     //     assert i' != i;
//     //     assert children[i].node.allKeys !! children[i'].node.allKeys;
//     //     assert children[i].node.allKeys <= 
//     //     assert children[i].node.allKeys <= allKeys;
//     //   }
//     // }
    
//     // function QueryDef(needle: Key) : QueryResult
//     //   requires WF()
//     //   reads this, subtreeObjects
//     //   decreases subtreeObjects
//     // {
//     //   var pos := Keys.LargestLte(pivots[..nchildren-1], needle);
//     //   children[pos + 1].node.QueryDef(needle)
//     // }
    
//     function Interpretation() : (result: map<Key, Value>)
//       requires WF()
//       // ensures forall key :: QueryDef(key).Found? ==> MapsTo(result, key, QueryDef(key).value)
//       // ensures forall key :: QueryDef(key).NotFound? ==> key !in Interpretation()
//       reads this, subtreeObjects
//       decreases subtreeObjects
//     {
//       // This is just to prove finiteness.  Thanks to James Wilcox for the trick:
//       // https://stackoverflow.com/a/47585360
//       var allkeys := set key, i | 0 <= i < nchildren && key in children[i].node.Interpretation() :: key;
//       var result := map key |
//         && key in allkeys
//         && key in children[Keys.LargestLte(pivots[..nchildren-1], key) + 1].node.Interpretation()
//         :: children[Keys.LargestLte(pivots[..nchildren-1], key) + 1].node.Interpretation()[key];

//       // assert forall key :: QueryDef(key).Found? ==> key in children[Keys.LargestLte(pivots[..nchildren-1], key)+1].node.Interpretation();
        
//       result
//     }

//     method Query(needle: Key) returns (result: QueryResult)
//       requires WF()
//       ensures needle in Interpretation() ==> result == Found(Interpretation()[needle])
//       ensures needle !in Interpretation() ==> result == NotFound
//       // ensures result == QueryDef(needle)
//       decreases subtreeObjects
//     {
//       var posplus1 := Keys.ArrayLargestLtePlus1(pivots, 0, nchildren-1, needle);
//       result := children[posplus1].node.Query(needle);
//     }

//     predicate method Full()
//       requires WF()
//       reads this, subtreeObjects
//     {
//       nchildren == MaxChildren()
//     }

//     static lemma SplitChildIsCorrect()
    
//     method SplitChild(key: Key, childidx: uint64) returns (newchildidx: uint64)
//       requires WF()
//       requires !Full()
//       requires childidx as int == 1 + Keys.LargestLte(pivots[..nchildren-1], key)
//       requires children[childidx].node.Full()
//       ensures WF()
//       ensures Interpretation() == old(Interpretation())
//       ensures newchildidx as int == 1 + Keys.LargestLte(pivots[..nchildren-1], key)
//       ensures !children[newchildidx].node.Full()
//       ensures allKeys == old(allKeys)
//       ensures fresh(subtreeObjects-old(subtreeObjects))
//       modifies this, pivots, children, children[childidx].node
//     {
//       ghost var oldchildren := children[..nchildren];
      
//       var wit, pivot, right := children[childidx].node.Split();
//       Arrays.Insert(pivots, nchildren - 1, pivot, childidx);
//       Arrays.Insert(children, nchildren, NodeBox(right), childidx + 1);
//       nchildren := nchildren + 1;
//       subtreeObjects := subtreeObjects + right.subtreeObjects;
//       if Keys.lte(pivot, key) {
//         newchildidx := childidx + 1;
//       } else {
//         newchildidx := childidx;
//       }

//       Keys.LargestLteIsUnique(old(pivots[..nchildren-1]), pivot, childidx as int - 1);
//       Keys.strictlySortedInsert(old(pivots[..nchildren-1]), pivot, childidx as int - 1);

//       assert forall i :: 0 <= i < childidx as int ==> children[i] == oldchildren[i];
//       assert children[childidx as int + 1].node == right;
//       assert forall i :: childidx as int + 1 < i < nchildren as int  ==> children[i] == oldchildren[i-1];
//       forall i: int, j: int {:trigger children[i].node.subtreeObjects, children[j].node.subtreeObjects}
//       | 0 <= i < j < nchildren as int
//         ensures children[i].node.subtreeObjects !! children[j].node.subtreeObjects
//       {
//         if                                   j  < childidx as int {
//         } else if                            j == childidx as int {
//         } else if i  < childidx as int     && j == childidx as int + 1 {
//         } else if i == childidx as int     && j == childidx as int + 1 {
//         } else if i  < childidx as int     && j  > childidx as int + 1 {
//         } else if i == childidx as int     && j  > childidx as int + 1 {
//         } else if i == childidx as int + 1 && j  > childidx as int + 1 {
//         } else {
//         }
//       }
//       // forall i: int, key | 0 <= i < (nchildren as int)-1 && key in children[i].node.allKeys
//       //   ensures Keys.lt(key, pivots[i])
//       // {
//       //   if childidx as int + 1 < i {
//       //     assert children[i] == old(children[i-1]);
//       //   }
//       // }
//       // forall i: int, key | 0 < i < nchildren as int && key in children[i].node.allKeys
//       //   ensures Keys.lt(pivots[i-1], key)
//       // {
//       //   if i < childidx as int {
//       //     assert Keys.lt(pivots[i-1], key);
//       //   } else if i == childidx as int {
//       //     assert Keys.lt(pivots[i-1], key);
//       //   } else if i == childidx as int + 1 {
//       //     assert Keys.lt(pivots[i-1], key);
//       //   } else {
//       //     assert Keys.lt(pivots[i-1], key);
//       //   }
//       // }
//       assert WF();
        
//       forall key | key in old(Interpretation())
//         ensures key in Interpretation() && Interpretation()[key] == old(Interpretation()[key])
//       {
//         var llte: int := Keys.LargestLte(old(pivots[..nchildren-1]), key);
//         assert key in old(children[llte+1].node.Interpretation());
//         assert old(children[llte+1].node.Interpretation()[key]) == old(Interpretation()[key]);
//         if llte < childidx as int {
//           assert key in Interpretation() && Interpretation()[key] == old(Interpretation()[key]);
//         } else if llte == childidx as int {
//           if Keys.lt(key, pivot) {
//             assert key in Interpretation() && Interpretation()[key] == old(Interpretation()[key]);
//           } else {
//             assert key in Interpretation() && Interpretation()[key] == old(Interpretation()[key]);
//           }
//         } else {
//           assert key in Interpretation() && Interpretation()[key] == old(Interpretation()[key]);
//         }
//       }
//       forall key | key in Interpretation()
//         ensures key in old(Interpretation()) && Interpretation()[key] == old(Interpretation()[key])
//       {
//         var llte: int := Keys.LargestLte(pivots[..nchildren-1], key);
//         if llte < childidx as int {
//         } else if llte == childidx as int {
//         } else if llte == childidx as int + 1 {
//         } else {
//         }
//       }
//     }
    
//     method Insert(key: Key, value: Value)
//       requires WF()
//       requires !Full()
//       ensures WF()
//       ensures Interpretation() == old(Interpretation())[key := value]
//       ensures allKeys == old(allKeys) + {key}
//       ensures fresh(subtreeObjects - old(subtreeObjects))
//       modifies this, subtreeObjects
//       decreases allKeys
//     {
//       var posplus1 := Keys.ArrayLargestLtePlus1(pivots, 0, nchildren - 1, key);
//       var childidx := (posplus1) as uint64;
//       if children[posplus1].node.Full() {
//         childidx := SplitChild(key, childidx);
//       }
//       //AllKeysStrictlyDecreasing();
//       children[childidx].node.Insert(key, value);
//       subtreeObjects := subtreeObjects + children[childidx].node.subtreeObjects;
//       allKeys := allKeys + {key};
//       forall key' | key' in old(Interpretation()) && key' != key
//         ensures key' in Interpretation() && Interpretation()[key'] == old(Interpretation()[key'])
//       {
//         var i :| 0 <= i < old(nchildren) && key' in old(children[i].node.Interpretation());
//       }
      
//     }

//     function UnionSubtreeObjects() : set<object>
//       requires nchildren as int <= children.Length
//       requires forall i :: 0 <= i < nchildren ==> children[i].node != null
//       reads this, children, set i | 0 <= i < nchildren :: children[i].node
//     {
//       set o, i | 0 <= i < nchildren && o in children[i].node.subtreeObjects :: o
//     }
    
//     method Split() returns (ghost wit: Key, pivot: Key, rightnode: Node)
//       requires WF()
//       requires Full()
//       ensures SplitEnsures(old(Interpretation()), pivot, rightnode)
//       ensures allKeys <= old(allKeys)
//       ensures rightnode.allKeys <= old(allKeys)
//       ensures pivot in old(allKeys)
//       ensures wit in old(allKeys)
//       ensures Keys.lt(wit, pivot)
//       ensures subtreeObjects <= old(subtreeObjects)
//       ensures subtreeObjects !! rightnode.subtreeObjects
//       ensures fresh(rightnode.subtreeObjects - old(subtreeObjects))
//       modifies this
//     {
//       var right := new Index();
//       var boundary := nchildren/2;
//       Arrays.Memcpy(right.pivots, 0, pivots[boundary..nchildren-1]); // FIXME: remove conversion to seq
//       Arrays.Memcpy(right.children, 0, children[boundary..nchildren]); // FIXME: remove conversion to seq
//       right.nchildren := nchildren - boundary;
//       nchildren := boundary;
//       subtreeObjects := {this, pivots, children} + UnionSubtreeObjects();
//       right.subtreeObjects := right.subtreeObjects + right.UnionSubtreeObjects();

//       pivot := pivots[boundary-1];

//       right.allKeys := set k | k in allKeys && Keys.lte(pivot, k);
//       allKeys := set k | k in allKeys && Keys.lt(k, pivot);
      
//       wit := right.pivots[0];
//       rightnode := right;
//       AssumeFalse();
      
//       // Keys.reveal_IsStrictlySorted();
//       // assert WF();
//       // assert rightnode.WF();
//       // assert MergeMaps(Interpretation(), pivot, rightnode.Interpretation()) == old(Interpretation());
//     }

//     constructor()
//       ensures nchildren == 0
//       ensures pivots.Length == (MaxChildren() as int)-1
//       ensures children.Length == (MaxChildren() as int)
//       ensures forall i :: 0 <= i < children.Length ==> children[i].node == null
//       ensures subtreeObjects == {this, pivots, children}
//       ensures allKeys == {}
//       ensures fresh(pivots)
//       ensures fresh(children)
//     {
//       pivots := new Key[MaxChildren()-1](_ => DefaultKey());
//       children := new NodeBox[MaxChildren()](_ => NodeBox(null));
//       nchildren := 0;
//       subtreeObjects := {this, pivots, children};
//       allKeys := {};
//     }
//   }

//   class MutableBtree {
//     var root: Node

//     function Interpretation() : map<Key, Value>
//       requires root.WF()
//       reads this, root, root.subtreeObjects
//     {
//       root.Interpretation()
//     }

//     method Query(needle: Key) returns (result: QueryResult)
//       requires root.WF()
//       ensures result == NotFound ==> needle !in Interpretation()
//       ensures result.Found? ==> needle in Interpretation() && Interpretation()[needle] == result.value
//     {
//       result := root.Query(needle);
//     }

//     method Insert(key: Key, value: Value)
//       requires root.WF()
//       ensures root.WF()
//       ensures Interpretation() == old(Interpretation())[key := value]
//       modifies this, root, root.subtreeObjects
//     {
//       if root.Full() {
//         var newroot := new Index();
//         newroot.children[0] := NodeBox(root);
//         newroot.nchildren := 1;
//         newroot.subtreeObjects := newroot.subtreeObjects + root.subtreeObjects;
//         newroot.allKeys := root.allKeys;
//         root := newroot;
//       }
//       AssumeFalse();
//       root.Insert(key, value);
//     }
    
//     constructor()
//       ensures root.WF()
//       ensures Interpretation() == map[]
//     {
//       root := new Leaf();
//     }
//   }
// }

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
} 
