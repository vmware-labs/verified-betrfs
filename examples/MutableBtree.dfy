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
  import Arrays
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
    | NotInUse // For entries in children arrays that are not currently in use
    | Leaf(ghost repr: set<object>, nkeys: uint64, keys: array<Key>, values: array<Value>)
    | Index(ghost repr: set<object>, nchildren: uint64, pivots: array<Key>, children: array<Node>)

  function LocalKeys(node: Node) : set<Key>
    requires !node.NotInUse?
    requires node.Leaf? ==> 0 <= node.nkeys as int <= node.keys.Length
    requires node.Index? ==> 0 < node.nchildren as int <= node.pivots.Length + 1
    reads if node.Leaf? then node.keys else node.pivots
  {
    match node {
      case Leaf(_, nkeys, keys, _) => set k | k in keys[..nkeys]
      case Index(_, nchildren, pivots, _) => set i | 0 <= i < nchildren-1 :: pivots[i]
    }    
  }
  
  predicate DisjointSubtrees(node: Node, i: int, j: int)
    requires node.Index?
    requires 0 <= i < node.children.Length
    requires 0 <= j < node.children.Length
    requires !node.children[i].NotInUse?
    requires !node.children[j].NotInUse?
    requires i != j
    reads node.children
  {
    node.children[i].repr !! node.children[j].repr
  }

  predicate {:fuel 2} WFShape(node: Node)
    reads if node.NotInUse? then {} else node.repr
    decreases if node.NotInUse? then {} else node.repr
  {
    if node.NotInUse? then false
    else if node.Leaf? then
      && node.repr == { node.keys, node.values }
      && 0 <= node.nkeys as int <= MaxKeysPerLeaf() as int == node.keys.Length
      && node.values.Length == node.keys.Length
    else 
      && node.pivots in node.repr
      && node.children in node.repr
      && 0 < node.nchildren as int <= MaxChildren() as int == node.children.Length
      && node.pivots.Length == MaxChildren() as int - 1
      && (forall i :: 0 <= i < node.nchildren ==> !node.children[i].NotInUse?)
      && (forall i :: 0 <= i < node.nchildren ==> node.children[i].repr < node.repr)
      && (forall i :: 0 <= i < node.nchildren as int ==> node.pivots !in node.children[i].repr)
      && (forall i :: 0 <= i < node.nchildren as int ==> node.children !in node.children[i].repr)
      && (forall i, j :: 0 <= i < j < node.nchildren as int ==> DisjointSubtrees(node, i, j))
      && (forall i :: 0 <= i < node.nchildren ==> WFShape(node.children[i]))
  }

  predicate {:fuel 2} WF(node: Node)
    requires WFShape(node)
    reads node.repr
    decreases node.repr
  {
    if node.NotInUse? then true
    else if node.Leaf? then
      && BS.Keys.IsStrictlySorted(node.keys[..node.nkeys])
    else
      && BS.Keys.IsStrictlySorted(node.pivots[..node.nchildren-1])
      && (forall i :: 0 <= i < node.nchildren ==> LocalKeys(node.children[i]) != {})
      && (forall i, key :: 0 <= i < node.nchildren-1 && key in LocalKeys(node.children[i]) ==> BS.Keys.lt(key, node.pivots[i]))
      && (forall i, key :: 0 < i < node.nchildren   && key in LocalKeys(node.children[i]) ==> BS.Keys.lte(node.pivots[i-1], key))
      && (forall i :: 0 <= i < node.nchildren ==> WF(node.children[i]))
  }

  predicate ObjectIsInSubtree(node: Node, o: object, i: int)
    requires WFShape(node)
    requires node.Index?
    requires 0 <= i < node.nchildren as int
    reads node.repr
  {
    o in node.children[i].repr
  }

  function {:opaque} SubRepr(node: Node, from: int, to: int) : (result: set<object>)
    requires WFShape(node)
    requires WF(node)
    requires node.Index?
    requires 0 <= from <= to <= node.nchildren as int
    reads node.repr
  {
    set i: int, o | 0 <= from <= i < to && o in node.repr && ObjectIsInSubtree(node, o, i) :: o
  }

  lemma SubReprFits(node: Node, from: int, to: int)
    requires WFShape(node)
    requires WF(node)
    requires node.Index?
    requires 1 < node.nchildren
    requires 0 <= from <= to <= node.nchildren as int
    ensures SubRepr(node, from, to) <= node.repr - {node.pivots, node.children}
    ensures to - from < node.nchildren as int ==> SubRepr(node, from, to) < node.repr - {node.pivots, node.children}
    ensures forall i :: from <= i < to ==> node.children[i].repr <= SubRepr(node, from, to)
  {
    var subrepr := SubRepr(node, from, to);
    var nchildren := node.nchildren;
    var children := node.children;
    
    reveal_SubRepr();
    assert subrepr <= node.repr;
    assert node.pivots !in subrepr;
    assert node.children !in subrepr;
    assert subrepr <= node.repr - {node.pivots, node.children};
    
    if to - from < nchildren as int {
      assert children[0].repr < node.repr;
      assert children[0].repr != {};
      assert children[nchildren-1].repr < node.repr;
      assert children[nchildren-1].repr != {};
      if 0 < from {
        forall o | o in subrepr
          ensures o !in children[0].repr
        {
          if o == node.pivots {
          } else if o == children {
          } else {
            var i :| from <= i < to && o in node.repr && ObjectIsInSubtree(node, o, i);
            assert DisjointSubtrees(node, 0, i);
          }
        }
        assert subrepr < node.repr - {node.pivots, node.children};
      } else {
        assert to < nchildren as int;
        forall o | o in subrepr
          ensures o !in children[nchildren - 1].repr
        {
          if o == node.pivots {
          } else if o == children {
          } else {
            var i :| from <= i < to && o in node.repr && ObjectIsInSubtree(node, o, i);
            assert DisjointSubtrees(node, i, nchildren as int - 1);
          }
        }
        var wit :| wit in children[nchildren-1].repr;
        assert wit !in subrepr;
        assert subrepr < node.repr - {node.pivots, node.children};
      }
    }
    forall i | from <= i < to
      ensures children[i].repr <= subrepr
    {
      forall o | o in children[i].repr
        ensures o in subrepr
      {
        assert ObjectIsInSubtree(node, o, i);
      }
    }
  }
  
  function method IndexPrefix(node: Node, newnchildren: int) : (result: Node)
    requires WFShape(node)
    requires WF(node)
    requires node.Index?
    requires 1 < node.nchildren
    requires 0 <= newnchildren <= node.nchildren as int
    reads node.repr
  {
    Index(SubRepr(node, 0, newnchildren) + {node.pivots, node.children}, newnchildren as uint64, node.pivots, node.children)
  }

  lemma IndexPrefixWF(node: Node, newnchildren: int)
    requires WFShape(node)
    requires WF(node)
    requires node.Index?
    requires 1 < node.nchildren
    requires 0 < newnchildren <= node.nchildren as int
    ensures WFShape(IndexPrefix(node, newnchildren))
    ensures WF(IndexPrefix(node, newnchildren))
    ensures newnchildren < node.nchildren as int ==> IndexPrefix(node, newnchildren).repr < node.repr
  {
    BS.Keys.reveal_IsStrictlySorted();
    var pnode := IndexPrefix(node, newnchildren);
    forall i: int, j: int | 0 <= i < j < pnode.nchildren as int
      ensures DisjointSubtrees(pnode, i, j)
    {
      assert DisjointSubtrees(node, i, j);
    }
    SubReprFits(node, 0, newnchildren);
  }

  function ToImmutableNode(node: Node) : (result: BS.Node)
    requires WFShape(node)
    requires WF(node)
    ensures node.Leaf? ==> result.Leaf?
    ensures node.Index? ==> result.Index?
    reads node.repr
    decreases node.repr
  {
    match node {
      case Leaf(_, nkeys, keys, values) => BS.Leaf(keys[..nkeys], values[..nkeys])
      case Index(repr, nchildren, pivots, children) =>
        if nchildren == 1 then
          BS.Index([], [ToImmutableNode(children[0])])
        else
          IndexPrefixWF(node, node.nchildren as int - 1);
          var imprefix := ToImmutableNode(IndexPrefix(node, node.nchildren as int - 1));
          var imlastchild := ToImmutableNode(children[nchildren-1]);
          BS.Index(imprefix.pivots + [pivots[nchildren-2]], imprefix.children + [imlastchild])
    }
  }

  lemma ImmutableWF(node: Node)
    requires WFShape(node)
    requires WF(node)
    ensures BS.WF(ToImmutableNode(node))
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
      IndexPrefixWF(node, node.nchildren as int - 1);
      var imprefix := ToImmutableNode(IndexPrefix(node, node.nchildren as int - 1));
      ImmutableWF(IndexPrefix(node, node.nchildren as int - 1));
      var imlastchild := ToImmutableNode(node.children[node.nchildren-1]);
      var imnode := BS.Index(imprefix.pivots + [node.pivots[node.nchildren-2]], imprefix.children + [imlastchild]);
      assert imnode.pivots == node.pivots[..node.nchildren-1];
      assert BS.LocalKeys(Last(imnode.children)) == LocalKeys(node.children[node.nchildren-1]);
    }
  }

  function ToImmutableWFNode(node: Node) : (result: BS.Node)
    requires WFShape(node)
    requires WF(node)
    ensures node.Leaf? ==> result.Leaf?
    ensures node.Index? ==> result.Index?
    ensures BS.WF(result)
    ensures node.Index? ==> result.pivots == node.pivots[..node.nchildren-1]
    reads node.repr
  {
    ImmutableWF(node);
    ToImmutableNode(node)
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
      IndexPrefixWF(node, node.nchildren as int - 1);
    }
  }
  
  function Interpretation(node: Node) : map<Key, Value>
    requires WFShape(node)
    requires WF(node)
    reads node.repr
    decreases node.repr
  {
    ImmutableWF(node);
    BS.Interpretation(ToImmutableNode(node))
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
      assert needle in BS.Interpretation(imnode);
    } else {
      assert needle !in BS.Interpretation(imnode);
      if needle !in BS.AllKeys(imnode) {
        assert needle !in BS.AllKeys(imnode.children[posplus1]);
      }
      assert needle !in BS.Interpretation(imnode.children[posplus1]);
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

  predicate method Full(node: Node)
    requires !node.NotInUse?
  {
    match node {
      case Leaf(_, nkeys, _, _) => nkeys == MaxKeysPerLeaf()
      case Index(_, nchildren, _, _) => nchildren == MaxChildren()
    }
  }

  method SplitLeaf(node: Node) returns (left: Node, pivot: Key, right: Node)
    requires WFShape(node)
    requires WF(node)
    requires node.Leaf?
    requires Full(node)
    ensures WFShape(left)
    ensures WFShape(right)
    ensures WF(left)
    ensures WF(right)
    ensures BS.SplitLeaf(ToImmutableNode(node), ToImmutableNode(left), ToImmutableNode(right), pivot)
  {
    var rightkeys := new Key[MaxKeysPerLeaf()](_ => DefaultKey());
    var rightvalues := new Value[MaxKeysPerLeaf()](_ => DefaultValue());
    var boundary := node.nkeys / 2;
    Arrays.Memcpy(rightkeys, 0, node.keys[boundary..node.nkeys]); // FIXME: remove conversion to seq
    Arrays.Memcpy(rightvalues, 0, node.values[boundary..node.nkeys]); // FIXME: remove conversion to seq
    left := Leaf(node.repr, boundary, node.keys, node.values);
    right := Leaf({rightkeys, rightvalues}, node.nkeys - boundary, rightkeys, rightvalues);
    pivot := right.keys[0];
    
    BS.Keys.reveal_IsStrictlySorted();
    ghost var imright := ToImmutableNode(right);
    assert BS.WF(imright);
  }

  method SubIndex(node: Node, from: uint64, to: uint64) returns (subnode: Node)
    requires WFShape(node)
    requires WF(node)
    requires node.Index?
    requires 1 < node.nchildren
    requires 0 <= from < to <= node.nchildren
    ensures subnode.Index?
    ensures WFShape(subnode)
    ensures WF(subnode)
    ensures subnode.repr == SubRepr(node, from as int, to as int) + {subnode.pivots, subnode.children}
    ensures ToImmutableNode(subnode) == BS.SubIndex(ToImmutableWFNode(node), from as int, to as int)
    ensures fresh(subnode.pivots)
    ensures fresh(subnode.children)
  {
    var subnchildren := to - from;
    var subpivots := new Key[MaxChildren()-1]
      (i
      requires 0 <= i <= (MaxChildren()-1) as int
      reads node.pivots
      =>
      if i < subnchildren as int - 1 then node.pivots[from as int + i]
      else DefaultKey());
    var subchildren := new Node[MaxChildren()]
      (i
      requires 0 <= i <= MaxChildren() as int
      reads node.children
      =>
      if i < subnchildren as int then node.children[from as int + i]
      else NotInUse);
    ghost var subrepr := SubRepr(node, from as int, to as int) + {subpivots, subchildren};
    subnode := Index(subrepr, subnchildren, subpivots, subchildren);

    SubReprFits(node, from as int, to as int);
    forall i, j | 0 <= i < j < subnode.nchildren as int
      ensures DisjointSubtrees(subnode, i, j)
    {
      assert subnode.children[i] == node.children[from as int + i];
      assert subnode.children[j] == node.children[from as int + j];
      assert DisjointSubtrees(node, from as int + i, from as int + j);
    }
    BS.Keys.StrictlySortedSubsequence(node.pivots[..node.nchildren-1], from as int, (to-1) as int);
    assert subnode.pivots[..subnode.nchildren-1] == node.pivots[from..to-1];
    assert node.pivots[from..to-1] == node.pivots[..node.nchildren-1][from..to-1];
    
    ImmutableWF(node);
    ImmutableWF(subnode);
    ghost var imnode := ToImmutableNode(node);
    ghost var imsubnode := ToImmutableNode(subnode);
    assert imsubnode.pivots == imnode.pivots[from..to-1];
    assert subnode.children[..subnode.nchildren] == node.children[from..to];
    assert node.children[from..to] == node.children[..node.nchildren][from..to];
    ImmutableChildIndices(node);
    ImmutableChildIndices(subnode);
    assert imsubnode.children == imnode.children[from..to];
  }

  
  // method SplitIndex(node: Node) returns (left: Node, pivot: Key, right: Node)
  //   requires WFShape(node)
  //   requires WF(node)
  //   requires node.Index?
  //   requires Full(node)
  //   ensures left.Index?
  //   ensures left.nchildren == node.nchildren/2;
  //   ensures left.pivots == node.pivots
  //   ensures left.children == node.children
  //   ensures WFShape(left)
  //   ensures WF(left)
  //   ensures right.Index?
  //   ensures right.nchildren == node.nchildren - node.nchildren/2;
  //   ensures fresh (right.pivots)
  //   ensures fresh(right.children)
  //   ensures WFShape(right)
  //   ensures WF(right)
  //   ensures right.pivots[..right.nchildren-1] == node.pivots[node.nchildren/2..node.nchildren-1];
  //   ensures right.children[..right.nchildren] == node.children[node.nchildren/2..node.nchildren];
  //   ensures left.repr !! right.repr
  //   // ensures BS.SplitIndex(ToImmutableNode(node), ToImmutableNode(left), ToImmutableNode(right), pivot)
  // {
  //   ghost var oldnchildren := node.nchildren;
  //   var boundary: uint64 := node.nchildren/2;
  //   var rightpivots := new Key[MaxChildren()-1]
  //     (i
  //     requires 0 <= i <= (MaxChildren()-1) as int
  //     reads node.pivots
  //     =>
  //     if i < (node.nchildren - boundary - 1) as int then node.pivots[boundary as int + i]
  //     else DefaultKey());
  //   var rightchildren := new Node[MaxChildren()]
  //     (i
  //     requires 0 <= i <= MaxChildren() as int
  //     reads node.children
  //     =>
  //     if i < (node.nchildren - boundary) as int then node.children[boundary as int + i]
  //     else NotInUse);

  //   ghost var leftrepr := {node.pivots, node.children} +
  //       (set i, o | 0 <= i < boundary && o in node.children[i].repr :: o);
  //   ghost var rightrepr: set<object> := 
  //       (set i, o | 0 <= i < node.nchildren - boundary && o in rightchildren[i].repr :: o);
  //   rightrepr := rightrepr + {rightpivots};
  //   rightrepr := rightrepr + {rightchildren};

  //   left := Index(leftrepr, boundary, node.pivots, node.children);
  //   right := Index(rightrepr, node.nchildren - boundary, rightpivots, rightchildren);
  //   pivot := node.pivots[boundary - 1];

  //   forall i, j | 0 <= i < j < left.nchildren as int
  //     ensures DisjointSubtrees(left, i, j)
  //   {
  //     assert DisjointSubtrees(node, i, j);
  //   }
  //   forall i, j | 0 <= i < j < right.nchildren as int
  //     ensures DisjointSubtrees(right, i, j)
  //   {
  //     assert right.children[i] == node.children[boundary as int + i];
  //     assert right.children[j] == node.children[boundary as int + j];
  //     assert DisjointSubtrees(node, boundary as int + i, boundary as int + j);
  //   }
  //   assert WFShape(left);
  //   assert WFShape(right);
    
  //   BS.Keys.StrictlySortedSubsequence(node.pivots[..oldnchildren-1], 0, boundary as int - 1);
  //   assert node.pivots[0..boundary-1] == node.pivots[..node.nchildren-1][0..boundary-1];
  //   BS.Keys.StrictlySortedSubsequence(node.pivots[..oldnchildren-1], boundary as int, (oldnchildren-1) as int);
  //   assert right.pivots[..right.nchildren-1] == node.pivots[..oldnchildren-1][boundary..oldnchildren-1];
  //   assert WF(left);
  //   assert WF(right);
    
  //   // ImmutableWF(node);
  //   // ImmutableWF(left);
  //   // ImmutableWF(right);
    
  //   // ghost var imnode := ToImmutableNode(node);
  //   // ghost var imleft := ToImmutableNode(left);
  //   // ghost var imright := ToImmutableNode(right);

  //   // assert node.pivots[..oldnchildren - 1] ==
  //   //   node.pivots[..oldnchildren - 1][0..boundary - 1]
  //   //   + [pivot]
  //   //   + node.pivots[..oldnchildren-1][boundary..oldnchildren-1];
      
  //   // assert BS.SplitIndex(imnode, imleft, imright, pivot);
  // }

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
