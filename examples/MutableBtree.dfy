include "../lib/NativeTypes.dfy"
include "../lib/total_order.dfy"
include "../lib/sequences.dfy"
include "../lib/Arrays.dfy"
include "../lib/Maps.dfy"
include "BtreeSpec.dfy"

abstract module MutableBtree {
  import opened NativeTypes
  import opened Seq = Sequences
  import opened Maps
  import BS : BtreeSpec
  
  type Key = BS.Keys.Element
  type Value = BS.Value

    
  function method MaxKeysPerLeaf() : uint64
    ensures 1 < MaxKeysPerLeaf() as int < Uint64UpperBound() / 2

  function method MaxChildren() : uint64
    ensures 3 < MaxChildren() as int < Uint64UpperBound() / 2

  function method DefaultValue() : Value
  function method DefaultKey() : Key

  datatype Node =
    | Leaf(ghost repr: set<object>, nkeys: uint64, keys: array<Key>, values: array<Value>)
    | Index(ghost repr: set<object>, nchildren: uint64, pivots: array<Key>, children: array<Node>)

  predicate WFShape(node: Node)
    reads node.repr
    decreases node.repr
  {
    match node {
      case Leaf(repr, nkeys, keys, values) =>
        && keys in repr
        && values in repr
        && 0 <= nkeys as int <= MaxKeysPerLeaf() as int == keys.Length
        && values.Length == keys.Length
      case Index(repr, nchildren, pivots, children) =>
        && pivots in repr
        && children in repr
        && 0 < nchildren as int <= MaxChildren() as int == children.Length
        && pivots.Length == MaxChildren() as int - 1
        && (forall i :: 0 <= i < nchildren ==> children[i].repr < repr)
        && (forall i {:trigger children[i].repr} :: 0 <= i < nchildren as int ==> pivots !in children[i].repr)
        && (forall i {:trigger children[i].repr} :: 0 <= i < nchildren as int ==> children !in children[i].repr)
        && (forall i, j {:trigger children[i].repr, children[j].repr} :: 0 <= i < j < nchildren as int ==> children[i].repr !! children[j].repr)
        && (forall i :: 0 <= i < nchildren ==> WFShape(children[i]))
    }
  }

  function LocalKeys(node: Node) : set<Key>
    requires WFShape(node)
    reads node.repr
  {
    match node {
      case Leaf(_, nkeys, keys, _) => set k | k in keys[..nkeys]
      case Index(_, nchildren, pivots, _) => set i | 0 <= i < nchildren-1 :: pivots[i]
    }    
  }
  
  predicate WFLeaf(node: Node)
    requires WFShape(node)
    requires node.Leaf?
    reads node.repr
  {
    && BS.Keys.IsStrictlySorted(node.keys[..node.nkeys])
  }

  predicate WFIndex(node: Node)
    requires WFShape(node)
    requires node.Index?
    reads node.repr
    decreases node.repr, 0
  {
    && BS.Keys.IsStrictlySorted(node.pivots[..node.nchildren-1])
    && (forall i :: 0 <= i < node.nchildren ==> WF(node.children[i]))
    && (forall i :: 0 <= i < node.nchildren ==> LocalKeys(node.children[i]) != {})
    && (forall i, key :: 0 <= i < node.nchildren-1 && key in LocalKeys(node.children[i]) ==> BS.Keys.lt(key, node.pivots[i]))
    && (forall i, key :: 0 < i < node.nchildren   && key in LocalKeys(node.children[i]) ==> BS.Keys.lte(node.pivots[i-1], key))
  }

  predicate WF(node: Node)
    requires WFShape(node)
    reads node.repr
    decreases node.repr, 1
  {
    match node {
      case Leaf(_, _, _, _) => WFLeaf(node)
      case Index(_, _, _, _) => WFIndex(node)
    }
  }

  function IndexPrefix(node: Node) : (result: Node)
    requires WFShape(node)
    requires WF(node)
    requires node.Index?
    requires 1 < node.nchildren
    reads node.repr
  {
    Index(node.repr - node.children[node.nchildren-1].repr, node.nchildren-1, node.pivots, node.children)
  }

  lemma IndexPrefixWF(node: Node)
    requires WFShape(node)
    requires WF(node)
    requires node.Index?
    requires 1 < node.nchildren
    ensures WF(IndexPrefix(node))
  {
    BS.Keys.reveal_IsStrictlySorted();
  }
  
  function ToImmutableNode(node: Node) : (result: BS.Node)
    requires WFShape(node)
    requires WF(node)
    reads node.repr
    decreases node.repr
  {
    match node {
      case Leaf(_, nkeys, keys, values) => BS.Leaf(keys[..nkeys], values[..nkeys])
      case Index(repr, nchildren, pivots, children) =>
        assert WFIndex(node); // FIXME: WFT?  Dafny can't see this in emacs
        if nchildren == 1 then
          BS.Index([], [ToImmutableNode(children[0])])
        else
          IndexPrefixWF(node);
          var imprefix := ToImmutableNode(IndexPrefix(node));
          var imlastchild := ToImmutableNode(children[nchildren-1]);
          BS.Index(imprefix.pivots + [pivots[nchildren-2]], imprefix.children + [imlastchild])
    }
  }

  lemma ImmutableWF(node: Node)
    requires WFShape(node)
    requires WF(node)
    ensures BS.WF(ToImmutableNode(node))
    ensures node.Index? ==> BS.AllKeys(ToImmutableNode(node)) != {}
    ensures node.Index? ==> ToImmutableNode(node).pivots == node.pivots[..node.nchildren-1]
    decreases node.repr
  {
    if node.Leaf? {
    } else if node.nchildren == 1 {
      var imnode := ToImmutableNode(node);
      if imnode.children[0].Leaf? {
        assert imnode.children[0].keys[0] in BS.AllKeys(imnode.children[0]);
      } else {
        ImmutableWF(node.children[0]);
      }
    } else {
      IndexPrefixWF(node);
      var imprefix := ToImmutableNode(IndexPrefix(node));
      ImmutableWF(IndexPrefix(node));
      var imlastchild := ToImmutableNode(node.children[node.nchildren-1]);
      var imnode := BS.Index(imprefix.pivots + [node.pivots[node.nchildren-2]], imprefix.children + [imlastchild]);
      assert imnode.pivots == node.pivots[..node.nchildren-1];
      assert BS.LocalKeys(Last(imnode.children)) == LocalKeys(node.children[node.nchildren-1]);
    }
  }

  lemma ImmutableChildIndices(node: Node)
    requires WFShape(node)
    requires WF(node)
    requires node.Index?
    ensures |ToImmutableNode(node).children| == node.nchildren as int
    ensures forall i :: 0 <= i < node.nchildren ==>
           ToImmutableNode(node).children[i] == ToImmutableNode(node.children[i])
    decreases node.repr
  {
    if node.nchildren == 1 {
    } else {
      IndexPrefixWF(node);
    }
  }
  
  function Interpretation(node: Node) : map<Key, Value>
    requires WFShape(node)
    requires WF(node)
    reads node.repr
    decreases node.repr
  {
    ImmutableWF(node);
    BS.InterpretNode(ToImmutableNode(node))
  }
  
  method QueryLeaf(node: Node, needle: Key) returns (result: BS.QueryResult)
    requires WFShape(node)
    requires WF(node)
    requires node.Leaf?
    ensures needle in Interpretation(node) ==> result == BS.Found(Interpretation(node)[needle])
    ensures needle !in Interpretation(node) ==> result == BS.NotFound
    decreases node.repr, 0
  {
    var posplus1: uint64 := BS.Keys.ArrayLargestLtePlus1(node.keys, 0, node.nkeys, needle);
    if 1 <= posplus1 && node.keys[posplus1-1] == needle {
      result := BS.Found(node.values[posplus1-1]);
    } else {
      result := BS.NotFound;
    }
  }

  method QueryIndex(node: Node, needle: Key) returns (result: BS.QueryResult)
    requires WFShape(node)
    requires WF(node)
    requires node.Index?
    ensures needle in Interpretation(node) ==> result == BS.Found(Interpretation(node)[needle])
    ensures needle !in Interpretation(node) ==> result == BS.NotFound
    decreases node.repr, 0
  {
    var posplus1 := BS.Keys.ArrayLargestLtePlus1(node.pivots, 0, node.nchildren-1, needle);
    result := Query(node.children[posplus1], needle);

    ghost var imnode := ToImmutableNode(node);
    ImmutableWF(node);
    ImmutableChildIndices(node);
    if needle in Interpretation(node) {
      //assert needle in BS.InterpretNode(imnode);
      //assert imnode.Index?;
      assert needle in BS.InterpretIndex(imnode);
      //assert posplus1 as int == BS.Keys.LargestLte(imnode.pivots, needle) + 1;
      //assert needle in BS.InterpretNode(imnode.children[posplus1]);
      //assert BS.InterpretNode(imnode)[needle] == BS.InterpretNode(imnode.children[posplus1])[needle];
      //assert imnode.children[posplus1] == ToImmutableNode(node.children[posplus1]);
      //assert needle in Interpretation(node.children[posplus1]);
    } else {
      assert needle !in BS.InterpretIndex(imnode);
      //assert needle !in BS.AllKeys(imnode) || needle !in BS.InterpretNode(imnode.children[posplus1]);
      //BS.AllKeysIsConsistentWithInterpretationUniversal(imnode);
      if needle !in BS.AllKeys(imnode) {
        assert needle !in BS.AllKeys(imnode.children[posplus1]);
      }
      assert needle !in BS.InterpretNode(imnode.children[posplus1]);
    }
  }

  method Query(node: Node, needle: Key) returns (result: BS.QueryResult)
    requires WFShape(node)
    requires WF(node)
    ensures needle in Interpretation(node) ==> result == BS.Found(Interpretation(node)[needle])
    ensures needle !in Interpretation(node) ==> result == BS.NotFound
    decreases node.repr, 1
  {
    match node {
      case Leaf(_, _, _, _) => result := QueryLeaf(node, needle);
      case Index(_, _, _, _) => result := QueryIndex(node, needle);
    }
  }
    
  // predicate method Full()
  //   requires WF()
  //   reads this, subtreeObjects
  // {
  //   nchildren == MaxChildren()
  // }

  //   // predicate method Full()
  //   //   requires WF()
  //   //   reads this, subtreeObjects
  //   // {
  //   //   nkeys >= MaxKeysPerLeaf()
  //   // }
    
  //   // method Split() returns (pivot: Key, rightnode: Node)
  //   //   requires WF()
  //   //   requires Full()
  //   //   ensures WF()
  //   //   ensures rightnode.WF()
  //   //   ensures SplitNode(old(ToImmutableNode()), ToImmutableNode(), rightnode.ToImmutableNode(), pivot)
  //   //   ensures !Full()
  //   //   ensures !rightnode.Full()
  //   //   ensures subtreeObjects <= old(subtreeObjects)
  //   //   ensures subtreeObjects !! rightnode.subtreeObjects
  //   //   ensures fresh(rightnode.subtreeObjects - old(subtreeObjects))
  //   //   modifies this
  //   // {
  //   //   var right := new Leaf();
  //   //   var boundary := nkeys/2;
  //   //   Arrays.Memcpy(right.keys, 0, keys[boundary..nkeys]); // FIXME: remove conversion to seq
  //   //   Arrays.Memcpy(right.values, 0, values[boundary..nkeys]); // FIXME: remove conversion to seq
  //   //   right.nkeys := nkeys - boundary;
  //   //   nkeys := boundary;
  //   //   pivot := right.keys[0];
  //   //   rightnode := right;

  //   //   assert keys[..nkeys] == old(keys[..nkeys])[..nkeys];
  //   //   Keys.StrictlySortedSubsequence(old(keys[..nkeys]), 0, nkeys as int);
  //   //   assert right.keys[..right.nkeys] == old(keys[..nkeys])[boundary..old(nkeys)];
  //   //   Keys.StrictlySortedSubsequence(old(keys[..nkeys]), boundary as int, old(nkeys) as int);
  //   //   Keys.reveal_IsStrictlySorted();
  //   //   assert SplitLeaf(old(ToImmutableNode()), ToImmutableNode(), rightnode.ToImmutableNode(), pivot);
  //   // }
      
  //   // method Insert(key: Key, value: Value)
  //   //   requires WF()
  //   //   requires !Full()
  //   //   ensures WF()
  //   //   ensures Interpretation() == old(Interpretation())[key := value]
  //   //   ensures AllKeys() == old(AllKeys()) + {key}
  //   //   ensures fresh(subtreeObjects-old(subtreeObjects))
  //   //   modifies this, subtreeObjects
  //   //   decreases AllKeys()
  //   // {
  //   //   var posplus1 := Keys.ArrayLargestLtePlus1(keys, 0, nkeys, key);

  //   //   if 1 <= posplus1 && keys[posplus1-1] == key {
  //   //     values[posplus1-1] := value;
  //   //   } else {
  //   //     ghost var oldkeys := keys[..nkeys];
  //   //     Arrays.Insert(keys, nkeys, key, posplus1);
  //   //     Arrays.Insert(values, nkeys, value, posplus1);
  //   //     nkeys := nkeys + 1;

  //   //     InsertMultiset(oldkeys, key, posplus1 as int); // OBSERVE
  //   //     Keys.strictlySortedInsert(oldkeys, key, posplus1 as int - 1); // OBSERVE
  //   //     Keys.PosEqLargestLte(keys[..nkeys], key, posplus1 as int);
  //   //     forall key' |  key' != key && key' in old(Interpretation())
  //   //       ensures key' in Interpretation() && Interpretation()[key'] == old(Interpretation())[key']
  //   //     {
  //   //       var i: int := Keys.LargestLte(old(keys[..nkeys]), key');
  //   //       //assert 0 <= i;
  //   //       if i < posplus1 as int {
  //   //         //assert keys[i] == key';
  //   //         Keys.PosEqLargestLte(keys[..nkeys], key', i);
  //   //       } else {
  //   //         //assert keys[i+1] == key';
  //   //         Keys.PosEqLargestLte(keys[..nkeys], key', i+1);
  //   //       }
  //   //     }
  //   //     forall key' | key' != key && key' in Interpretation()
  //   //       ensures key' in old(Interpretation()) && old(Interpretation())[key'] == Interpretation()[key']
  //   //     {
  //   //       var i: int := Keys.LargestLte(keys[..nkeys], key');
  //   //       if i < posplus1 as int {
  //   //         Keys.PosEqLargestLte(old(keys[..nkeys]), key', i);
  //   //       } else {
  //   //         Keys.PosEqLargestLte(old(keys[..nkeys]), key', i-1);
  //   //       }
  //   //     }
  //   //   }
  //   // }

  //   // constructor()
  //   //   ensures WF()
  //   //   ensures Interpretation() == map[]
  //   //   ensures !Full()
  //   //   ensures fresh(keys)
  //   //   ensures fresh(values)
  //   // {
  //   //   nkeys := 0;
  //   //   keys := new Key[MaxKeysPerLeaf()](_ => DefaultKey());
  //   //   values := new Value[MaxKeysPerLeaf()](_ => DefaultValue());
  //   //   subtreeObjects := {this, keys, values};
  //   // }
  // }

  // class Index extends Node {
  //   var nchildren: uint64
  //   var pivots: array<Key>
  //   var children: array<NodeBox>


  //   // lemma AllKeysStrictlyDecreasing()
  //   //   requires WF()
  //   //   ensures forall i :: 0 <= i < nchildren ==> children[i].node.allKeys < allKeys
  //   // {
  //   //   forall i | 0 <= i < nchildren
  //   //     ensures children[i].node.allKeys < allKeys
  //   //   {
  //   //     var i' := if i < nchildren-1 then i+1 else 0;
  //   //     assert i' != i;
  //   //     assert children[i].node.allKeys !! children[i'].node.allKeys;
  //   //     assert children[i].node.allKeys <= 
  //   //     assert children[i].node.allKeys <= allKeys;
  //   //   }
  //   // }
    
  //   // method SplitChild(key: Key, childidx: uint64)
  //   //   requires WF()
  //   //   requires !Full()
  //   //   requires childidx as int == 1 + Keys.LargestLte(pivots[..nchildren-1], key)
  //   //   requires children[childidx].node.Full()
  //   //   ensures WF()
  //   //   //ensures Interpretation() == old(Interpretation())
  //   //   ensures SplitChildOfIndex(old(ToImmutableNode()), ToImmutableNode(), childidx as int)
  //   //   ensures fresh(subtreeObjects-old(subtreeObjects))
  //   //   modifies this, pivots, children, children[childidx].node
  //   // {
  //   //   ghost var oldchildren := children;
      
  //   //   var pivot, right := children[childidx].node.Split();
  //   //   Arrays.Insert(pivots, nchildren - 1, pivot, childidx);
  //   //   Arrays.Insert(children, nchildren, NodeBox(right), childidx + 1);
  //   //   nchildren := nchildren + 1;
  //   //   subtreeObjects := subtreeObjects + right.subtreeObjects;

      
  //   //   // Keys.LargestLteIsUnique(old(pivots[..nchildren-1]), pivot, childidx as int - 1);
  //   //   // Keys.strictlySortedInsert(old(pivots[..nchildren-1]), pivot, childidx as int - 1);

  //   //   assert forall i: uint64 :: 0 <= i < childidx ==> children[i] == oldchildren[i];
  //   //   assert children[childidx as int + 1].node == right;
  //   //   assert forall i: uint64 :: childidx + 1 < i < nchildren ==> children[i] == oldchildren[i-1];
  //   //   // forall i: int, j: int {:trigger children[i].node.subtreeObjects, children[j].node.subtreeObjects}
  //   //   // | 0 <= i < j < nchildren as int
  //   //   //   ensures children[i].node.subtreeObjects !! children[j].node.subtreeObjects
  //   //   // {
  //   //   //   if                                   j  < childidx as int {
  //   //   //   } else if                            j == childidx as int {
  //   //   //   } else if i  < childidx as int     && j == childidx as int + 1 {
  //   //   //   } else if i == childidx as int     && j == childidx as int + 1 {
  //   //   //   } else if i  < childidx as int     && j  > childidx as int + 1 {
  //   //   //   } else if i == childidx as int     && j  > childidx as int + 1 {
  //   //   //   } else if i == childidx as int + 1 && j  > childidx as int + 1 {
  //   //   //   } else {
  //   //   //   }
  //   //   // }
  //   //   // // forall i: int, key | 0 <= i < (nchildren as int)-1 && key in children[i].node.allKeys
  //   //   // //   ensures Keys.lt(key, pivots[i])
  //   //   // // {
  //   //   // //   if childidx as int + 1 < i {
  //   //   // //     assert children[i] == old(children[i-1]);
  //   //   // //   }
  //   //   // // }
  //   //   // // forall i: int, key | 0 < i < nchildren as int && key in children[i].node.allKeys
  //   //   // //   ensures Keys.lt(pivots[i-1], key)
  //   //   // // {
  //   //   // //   if i < childidx as int {
  //   //   // //     assert Keys.lt(pivots[i-1], key);
  //   //   // //   } else if i == childidx as int {
  //   //   // //     assert Keys.lt(pivots[i-1], key);
  //   //   // //   } else if i == childidx as int + 1 {
  //   //   // //     assert Keys.lt(pivots[i-1], key);
  //   //   // //   } else {
  //   //   // //     assert Keys.lt(pivots[i-1], key);
  //   //   // //   }
  //   //   // // }
  //   //   // assert WF();
        
  //   //   // forall key | key in old(Interpretation())
  //   //   //   ensures key in Interpretation() && Interpretation()[key] == old(Interpretation()[key])
  //   //   // {
  //   //   //   var llte: int := Keys.LargestLte(old(pivots[..nchildren-1]), key);
  //   //   //   assert key in old(children[llte+1].node.Interpretation());
  //   //   //   assert old(children[llte+1].node.Interpretation()[key]) == old(Interpretation()[key]);
  //   //   //   if llte < childidx as int {
  //   //   //     assert key in Interpretation() && Interpretation()[key] == old(Interpretation()[key]);
  //   //   //   } else if llte == childidx as int {
  //   //   //     if Keys.lt(key, pivot) {
  //   //   //       assert key in Interpretation() && Interpretation()[key] == old(Interpretation()[key]);
  //   //   //     } else {
  //   //   //       assert key in Interpretation() && Interpretation()[key] == old(Interpretation()[key]);
  //   //   //     }
  //   //   //   } else {
  //   //   //     assert key in Interpretation() && Interpretation()[key] == old(Interpretation()[key]);
  //   //   //   }
  //   //   // }
  //   //   // forall key | key in Interpretation()
  //   //   //   ensures key in old(Interpretation()) && Interpretation()[key] == old(Interpretation()[key])
  //   //   // {
  //   //   //   var llte: int := Keys.LargestLte(pivots[..nchildren-1], key);
  //   //   //   if llte < childidx as int {
  //   //   //   } else if llte == childidx as int {
  //   //   //   } else if llte == childidx as int + 1 {
  //   //   //   } else {
  //   //   //   }
  //   //   // }
  //   // }
    
  //   // function UnionSubtreeObjects() : set<object>
  //   //   requires nchildren as int <= children.Length
  //   //   requires forall i :: 0 <= i < nchildren ==> children[i].node != null
  //   //   reads this, children, set i | 0 <= i < nchildren :: children[i].node
  //   // {
  //   //   set o, i | 0 <= i < nchildren && o in children[i].node.subtreeObjects :: o
  //   // }
    
  //   // method Split() returns (pivot: Key, rightnode: Node)
  //   //   requires WF()
  //   //   requires Full()
  //   //   ensures WF()
  //   //   ensures rightnode.WF()
  //   //   ensures SplitNode(old(ToImmutableNode()), ToImmutableNode(), rightnode.ToImmutableNode(), pivot)
  //   //   ensures !Full()
  //   //   ensures !rightnode.Full()
  //   //   ensures subtreeObjects <= old(subtreeObjects)
  //   //   ensures subtreeObjects !! rightnode.subtreeObjects
  //   //   ensures fresh(rightnode.subtreeObjects - old(subtreeObjects))
  //   //   modifies this      
  //   // {
  //   //   var right := new Index();
  //   //   var boundary := nchildren/2;
  //   //   Arrays.Memcpy(right.pivots, 0, pivots[boundary..nchildren-1]); // FIXME: remove conversion to seq
  //   //   Arrays.Memcpy(right.children, 0, children[boundary..nchildren]); // FIXME: remove conversion to seq
  //   //   right.nchildren := nchildren - boundary;
  //   //   nchildren := boundary;
  //   //   subtreeObjects := {this, pivots, children} + UnionSubtreeObjects();
  //   //   right.subtreeObjects := right.subtreeObjects + right.UnionSubtreeObjects();

  //   //   pivot := pivots[boundary-1];

  //   //   rightnode := right;
      
  //   //   // Keys.reveal_IsStrictlySorted();
  //   //   // assert WF();
  //   //   // assert rightnode.WF();
  //   //   // assert MergeMaps(Interpretation(), pivot, rightnode.Interpretation()) == old(Interpretation());
  //   // }

  //   // // method Insert(key: Key, value: Value)
  //   // //   requires WF()
  //   // //   requires !Full()
  //   // //   ensures WF()
  //   // //   ensures Interpretation() == old(Interpretation())[key := value]
  //   // //   ensures allKeys == old(allKeys) + {key}
  //   // //   ensures fresh(subtreeObjects - old(subtreeObjects))
  //   // //   modifies this, subtreeObjects
  //   // //   decreases allKeys
  //   // // {
  //   // //   var posplus1 := Keys.ArrayLargestLtePlus1(pivots, 0, nchildren - 1, key);
  //   // //   var childidx := (posplus1) as uint64;
  //   // //   if children[posplus1].node.Full() {
  //   // //     childidx := SplitChild(key, childidx);
  //   // //   }
  //   // //   //AllKeysStrictlyDecreasing();
  //   // //   children[childidx].node.Insert(key, value);
  //   // //   subtreeObjects := subtreeObjects + children[childidx].node.subtreeObjects;
  //   // //   allKeys := allKeys + {key};
  //   // //   forall key' | key' in old(Interpretation()) && key' != key
  //   // //     ensures key' in Interpretation() && Interpretation()[key'] == old(Interpretation()[key'])
  //   // //   {
  //   // //     var i :| 0 <= i < old(nchildren) && key' in old(children[i].node.Interpretation());
  //   // //   }
      
  //   // // }

  //   // constructor()
  //   //   ensures nchildren == 0
  //   //   ensures pivots.Length == (MaxChildren() as int)-1
  //   //   ensures children.Length == (MaxChildren() as int)
  //   //   ensures forall i :: 0 <= i < children.Length ==> children[i].node == null
  //   //   ensures subtreeObjects == {this, pivots, children}
  //   //   ensures fresh(pivots)
  //   //   ensures fresh(children)
  //   // {
  //   //   pivots := new Key[MaxChildren()-1](_ => DefaultKey());
  //   //   children := new NodeBox[MaxChildren()](_ => NodeBox(null));
  //   //   nchildren := 0;
  //   //   subtreeObjects := {this, pivots, children};
  //   // }
  // }

  // // class MutableBtree {
  // //   var root: Node

  // //   function Interpretation() : map<Key, Value>
  // //     requires root.WF()
  // //     reads this, root, root.subtreeObjects
  // //   {
  // //     root.Interpretation()
  // //   }

  // //   method Query(needle: Key) returns (result: QueryResult)
  // //     requires root.WF()
  // //     ensures result == NotFound ==> needle !in Interpretation()
  // //     ensures result.Found? ==> needle in Interpretation() && Interpretation()[needle] == result.value
  // //   {
  // //     result := root.Query(needle);
  // //   }

  // //   method Insert(key: Key, value: Value)
  // //     requires root.WF()
  // //     ensures root.WF()
  // //     ensures Interpretation() == old(Interpretation())[key := value]
  // //     modifies this, root, root.subtreeObjects
  // //   {
  // //     if root.Full() {
  // //       var newroot := new Index();
  // //       newroot.children[0] := NodeBox(root);
  // //       newroot.nchildren := 1;
  // //       newroot.subtreeObjects := newroot.subtreeObjects + root.subtreeObjects;
  // //       newroot.allKeys := root.allKeys;
  // //       root := newroot;
  // //     }
  // //     AssumeFalse();
  // //     root.Insert(key, value);
  // //   }
    
  // //   constructor()
  // //     ensures root.WF()
  // //     ensures Interpretation() == map[]
  // //   {
  // //     root := new Leaf();
  // //   }
  // // }
}

module TestBtreeSpec refines BtreeSpec {
  import Keys = Integer_Order
  type Value = int
}

module TestMutableBtree refines MutableBtree {
  import BS = TestBtreeSpec
    
  function method MaxKeysPerLeaf() : uint64 { 64 }
  function method MaxChildren() : uint64 { 64 }

  function method DefaultValue() : Value { 0 }
  function method DefaultKey() : Key { 0 }
}

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
