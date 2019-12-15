include "../Base/NativeTypes.s.dfy"
include "../Base/NativeArrays.s.dfy"
include "../Base/total_order.i.dfy"
include "../Base/sequences.i.dfy"
include "../Base/Arrays.i.dfy"
include "../Base/Maps.s.dfy"
include "../Base/Option.s.dfy"
include "BtreeSpec.i.dfy"

abstract module MutableBtree {
  import opened NativeTypes
  import opened NativeArrays
  import opened Seq = Sequences
  import opened Options
  import opened Maps
  import Arrays
  import Spec : BtreeSpec

  export API provides WF, Interpretation, EmptyTree, Insert, Query, NativeTypes, Spec, Options reveals Node, NodeContents, Key, Value
  export All reveals *
    
  type Key = Spec.Keys.Element
  type Value = Spec.Value

  function method MaxKeysPerLeaf() : uint64
    ensures 1 < MaxKeysPerLeaf() as int < Uint64UpperBound() / 4

  function method MaxChildren() : uint64
    ensures 3 < MaxChildren() as int < Uint64UpperBound() / 4

  function method DefaultValue() : Value
  function method DefaultKey() : Key

  class Node {
    var contents: NodeContents
    ghost var repr: set<object>
    ghost var height: nat
  }
  
  datatype NodeContents =
    | Leaf(nkeys: uint64, keys: array<Key>, values: array<Value>)
    | Index(nchildren: uint64, pivots: array<Key>, children: array<Node?>)


  predicate DisjointReprs(a: Node, b: Node)
    reads a, b
  {
    a.repr !! b.repr
  }
  
  predicate WFShapeChildren(nodes: seq<Node?>, parentRepr: set<object>, parentHeight: int)
    reads parentRepr
    decreases parentHeight, 0
  {
    && (forall i :: 0 <= i < |nodes| ==> nodes[i] != null)
    && (forall i :: 0 <= i < |nodes| ==> nodes[i] in parentRepr)
    && (forall i :: 0 <= i < |nodes| ==> nodes[i].repr < parentRepr)
    && (forall i :: 0 <= i < |nodes| ==> nodes[i].height < parentHeight)
    && (forall i :: 0 <= i < |nodes| ==> WFShape(nodes[i]))
    && (forall i, j :: 0 <= i < j < |nodes| as int ==> DisjointReprs(nodes[i], nodes[j]))
  }

  predicate DisjointSubtrees(contents: NodeContents, i: int, j: int)
    requires contents.Index?
    requires 0 <= i < contents.children.Length
    requires 0 <= j < contents.children.Length
    requires contents.children[i] != null
    requires contents.children[j] != null
    reads contents.children, contents.children[i], contents.children[j]
  {
    DisjointReprs(contents.children[i], contents.children[j])
  }
  
  predicate WFShape(node: Node)
    reads node, node.repr
    decreases node.height, 1
  {
    if node.contents.Leaf? then
      && node.repr == { node, node.contents.keys, node.contents.values }
      //&& node.contents.keys != node.contents.values
      && |node.repr| == 3
      && node.height == 0
      && 0 <= node.contents.nkeys as int <= MaxKeysPerLeaf() as int == node.contents.keys.Length
      && node.contents.values.Length == node.contents.keys.Length
    else
      && { node, node.contents.pivots, node.contents.children } <= node.repr
      && 0 < node.contents.nchildren as int <= MaxChildren() as int == node.contents.children.Length
      && node.contents.pivots.Length == MaxChildren() as int - 1
      && WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height)
      && (forall i :: 0 <= i < node.contents.nchildren ==> node !in node.contents.children[i].repr)
      && (forall i :: 0 <= i < node.contents.nchildren ==> node.contents.pivots !in node.contents.children[i].repr)
      && (forall i :: 0 <= i < node.contents.nchildren ==> node.contents.children !in node.contents.children[i].repr)
  }

  function Ichildren(nodes: seq<Node>, parentheight: int) : (result: seq<Spec.Node>)
    requires forall i :: 0 <= i < |nodes| ==> WFShape(nodes[i])
    requires forall i :: 0 <= i < |nodes| ==> nodes[i].height < parentheight
    ensures |result| == |nodes|
    ensures forall i :: 0 <= i < |result| ==> result[i] == I(nodes[i])
    reads set i | 0 <= i < |nodes| :: nodes[i]
    reads set i, o | 0 <= i < |nodes| && o in nodes[i].repr :: o
    decreases parentheight, |nodes|
  {
    if |nodes| == 0 then []
    else Ichildren(DropLast(nodes), parentheight) + [I(Last(nodes))]
  }
  
  function {:opaque} I(node: Node) : (result: Spec.Node)
    requires WFShape(node)
    ensures node.contents.Leaf? <==> I(node).Leaf?
    ensures node.contents.Leaf? ==> I(node).keys == node.contents.keys[..node.contents.nkeys]
    ensures node.contents.Leaf? ==> I(node).values == node.contents.values[..node.contents.nkeys]
    ensures node.contents.Index? ==> I(node).pivots == node.contents.pivots[..node.contents.nchildren-1]
    ensures node.contents.Index? ==> |I(node).children| == node.contents.nchildren as int
    reads node, node.repr
    decreases node.height
  {
    match node.contents {
      case Leaf(nkeys, keys, values) => Spec.Leaf(keys[..nkeys], values[..nkeys])
      case Index(nchildren, pivots, children) =>
        assert WFShapeChildren(children[..nchildren], node.repr, node.height);
        var bschildren := Ichildren(children[..nchildren], node.height);
        Spec.Index(pivots[..nchildren-1], bschildren)
    }
  }

  lemma IOfChild(node: Node, childidx: int)
    requires WFShape(node)
    requires node.contents.Index?
    requires 0 <= childidx < node.contents.nchildren as int
    ensures node.contents.children[childidx] != null
    ensures WFShape(node.contents.children[childidx])
    ensures I(node).children[childidx] == I(node.contents.children[childidx])
  {
    reveal_I();
  }

  predicate WF(node: Node)
    ensures WF(node) ==> node in node.repr
    reads node, node.repr
  {
    && WFShape(node)
    && Spec.WF(I(node))
  }

  function Interpretation(node: Node) : map<Key, Value>
    requires WF(node)
    reads node.repr
  {
    Spec.Interpretation(I(node))
  }
    

  method QueryLeaf(node: Node, needle: Key) returns (result: Option<Value>)
    requires WF(node)
    requires node.contents.Leaf?
    ensures needle in Interpretation(node) ==> result == Some(Interpretation(node)[needle])
    ensures needle !in Interpretation(node) ==> result == None
    decreases node.repr, 0
  {
    reveal_I();
    var posplus1: uint64 := Spec.Keys.ArrayLargestLtePlus1(node.contents.keys, 0, node.contents.nkeys, needle);
    if 1 <= posplus1 && node.contents.keys[posplus1-1] == needle {
      result := Some(node.contents.values[posplus1-1]);
    } else {
      result := None;
    }
  }

  method QueryIndex(node: Node, needle: Key) returns (result: Option<Value>)
    requires WF(node)
    requires node.contents.Index?
    ensures needle in Spec.Interpretation(I(node)) ==> result == Some(Spec.Interpretation(I(node))[needle])
    ensures needle !in Spec.Interpretation(I(node)) ==> result == None
    decreases node.repr, 0
  {
    reveal_I();
    var posplus1: uint64 := Spec.Keys.ArrayLargestLtePlus1(node.contents.pivots, 0, node.contents.nchildren-1, needle);
    assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
    result := Query(node.contents.children[posplus1], needle);
  }

  method Query(node: Node, needle: Key) returns (result: Option<Value>)
    requires WF(node)
    ensures needle in Interpretation(node) ==> result == Some(Interpretation(node)[needle])
    ensures needle !in Interpretation(node) ==> result == None
    decreases node.repr, 1
  {
    match node.contents {
      case Leaf(_, _, _) => result := QueryLeaf(node, needle);
      case Index(_, _, _) => result := QueryIndex(node, needle);
    }
  }

  method EmptyTree() returns (root: Node)
    ensures WF(root)
    ensures fresh(root.repr)
    ensures Interpretation(root) == map[]
    ensures root.contents.Leaf?
  {
    var rootkeys := newArrayFill(MaxKeysPerLeaf(), DefaultKey());
    var rootvalues := newArrayFill(MaxKeysPerLeaf(), DefaultValue());
    root := new Node;
    root.contents := Leaf(0, rootkeys, rootvalues);
    root.repr := {root, rootkeys, rootvalues};
    root.height := 0;
  }

  method LeafFromSeqs(keys: seq<Key>, values: seq<Value>)
    returns (node: Node)
    requires |keys| == |values| <= MaxKeysPerLeaf() as int
    ensures WFShape(node)
    ensures node.contents.Leaf?
    ensures fresh(node.repr)
    ensures node.contents.keys[..node.contents.nkeys] == keys
    ensures node.contents.values[..node.contents.nkeys] == values
  {
    node := EmptyTree();
    Arrays.Memcpy(node.contents.keys, 0, keys);
    Arrays.Memcpy(node.contents.values, 0, values);
    node.contents := node.contents.(nkeys := |keys|);
    assert node.contents.keys[..node.contents.nkeys] == keys;
  }

  predicate method Full(node: Node)
    reads node
  {
    match node.contents {
      case Leaf(nkeys, _, _) => nkeys == MaxKeysPerLeaf()
      case Index(nchildren, _, _) => nchildren == MaxChildren()
    }
  }

  method SplitLeaf(node: Node, nleft: uint64, ghost pivot: Key) returns (right: Node, ghost wit: Key)
    requires WF(node)
    requires node.contents.Leaf?
    requires 0 < nleft < node.contents.nkeys
    requires Spec.Keys.lt(node.contents.keys[nleft-1], pivot)
    requires Spec.Keys.lte(pivot, node.contents.keys[nleft])
    ensures WFShape(node)
    ensures WFShape(right)
    ensures node.repr == old(node.repr)
    ensures fresh(right.repr)
    ensures Spec.SplitLeaf(old(I(node)), I(node), I(right), wit, pivot)
    ensures node.contents.nkeys == nleft
    modifies node
  {
    reveal_I();
    Spec.Keys.StrictlySortedSubsequence(node.contents.keys[..node.contents.nkeys], nleft as int, node.contents.nkeys as int);
    assert node.contents.keys[nleft..node.contents.nkeys] == node.contents.keys[..node.contents.nkeys][nleft..node.contents.nkeys];
    right := LeafFromSeqs(node.contents.keys[nleft..node.contents.nkeys], node.contents.values[nleft..node.contents.nkeys]);

    node.contents := Leaf(nleft, node.contents.keys, node.contents.values);
    wit := node.contents.keys[0];
    Spec.Keys.IsStrictlySortedImpliesLt(old(node.contents.keys[..node.contents.nkeys]), nleft as int - 1, nleft as int);
  }

  predicate ObjectIsInSubtree(node: Node, o: object, i: int)
    requires WFShape(node)
    requires node.contents.Index?
    requires 0 <= i < node.contents.nchildren as int
    reads node.repr
  {
    assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
    o in node.contents.children[i].repr
  }

  function {:opaque} SeqRepr(nodes: seq<Node>) : set<object>
    ensures forall i :: 0 <= i < |nodes| ==> nodes[i].repr <= SeqRepr(nodes)
    reads Set(nodes)
  {
    if |nodes| == 0 then {}
    else SeqRepr(DropLast(nodes)) + Last(nodes).repr
  }
  
  function {:opaque} SubRepr(node: Node, from: int, to: int) : (result: set<object>)
    requires WFShape(node)
    requires node.contents.Index?
    requires 0 <= from <= to <= node.contents.nchildren as int
    ensures {node, node.contents.pivots, node.contents.children} !! SubRepr(node, from, to)
    reads node.repr
  {
    set i: int, o | 0 <= from <= i < to && o in node.repr && ObjectIsInSubtree(node, o, i) :: o
  }

  lemma SubReprUpperBound(node: Node, from: int, to: int)
    requires WFShape(node)
    requires node.contents.Index?
    requires 1 < node.contents.nchildren
    requires 0 <= from <= to <= node.contents.nchildren as int
    ensures SubRepr(node, from, to) <= node.repr - {node, node.contents.pivots, node.contents.children}
    ensures to - from < node.contents.nchildren as int ==> SubRepr(node, from, to) < node.repr - {node, node.contents.pivots, node.contents.children}
  {
    reveal_SubRepr();
    
    var subrepr := SubRepr(node, from, to);
    var nchildren := node.contents.nchildren;
    var pivots := node.contents.pivots;
    var children := node.contents.children;
    
    assert subrepr <= node.repr;
    assert pivots !in subrepr;
    assert children !in subrepr;
    assert subrepr <= node.repr - {node, pivots, children};
    
    if to - from < nchildren as int {
      assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
      assert children[0].repr < node.repr;
      assert children[0].repr != {};
      assert children[nchildren-1].repr < node.repr;
      assert children[nchildren-1].repr != {};
      if 0 < from {
        forall o | o in subrepr
          ensures o !in children[0].repr
        {
          if o == pivots {
          } else if o == children {
          } else {
            var i :| from <= i < to && o in node.repr && ObjectIsInSubtree(node, o, i);
            assert DisjointSubtrees(node.contents, 0, i);
          }
        }
        assert subrepr < node.repr - {node, pivots, children};
      } else {
        assert to < nchildren as int;
        forall o | o in subrepr
          ensures o !in children[nchildren - 1].repr
        {
          if o == pivots {
          } else if o == children {
          } else {
            var i :| from <= i < to && o in node.repr && ObjectIsInSubtree(node, o, i);
            assert DisjointSubtrees(node.contents, i, nchildren as int - 1);
          }
        }
        var wit :| wit in children[nchildren-1].repr;
        assert wit !in subrepr;
        assert subrepr < node.repr - {node, pivots, children};
      }
    }
  }

  lemma SubReprLowerBound(node: Node, from: int, to: int)
    requires WFShape(node)
    requires node.contents.Index?
    requires 1 <= node.contents.nchildren
    requires 0 <= from <= to <= node.contents.nchildren as int
    ensures forall i :: from <= i < to ==> node.contents.children[i] != null
    ensures forall i :: from <= i < to ==> node.contents.children[i].repr <= SubRepr(node, from, to)
  {
    reveal_SubRepr();
    
    var subrepr := SubRepr(node, from, to);
    var nchildren := node.contents.nchildren;
    var pivots := node.contents.pivots;
    var children := node.contents.children;
    
    assert subrepr <= node.repr;
    assert pivots !in subrepr;
    assert children !in subrepr;
    assert subrepr <= node.repr - {node, pivots, children};
    
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

  
  method IndexPrefix(node: Node, newnchildren: uint64)
    requires WF(node)
    requires node.contents.Index?
    requires 1 <= newnchildren
    requires 0 <= newnchildren <= node.contents.nchildren
    ensures WFShape(node)
    ensures node.repr == old({node, node.contents.pivots, node.contents.children} + SubRepr(node, 0, newnchildren as int))
    ensures node.height == old(node.height)
    ensures I(node) == Spec.SubIndex(old(I(node)), 0, newnchildren as int)
    modifies node
  {
    assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
    ghost var oldinode := I(node);
    SubReprLowerBound(node, 0, newnchildren as int);
    node.repr := {node, node.contents.pivots, node.contents.children} + SubRepr(node, 0, newnchildren as int);
    node.contents := node.contents.(nchildren := newnchildren);
    forall i, j | 0 <= i < j < node.contents.nchildren as int
      ensures DisjointSubtrees(node.contents, i, j)
    {
      assert old(DisjointSubtrees(node.contents, i, j));
    }
    forall i | 0 <= i < newnchildren
      ensures node.contents.children[i] in node.repr
    {
      assert WFShape(node.contents.children[i]);
    }
    assert WFShape(node);
    ghost var newinode := I(node);
    reveal_I();
    assert newinode == Spec.SubIndex(oldinode, 0, newnchildren as int);
  }

  method SubIndex(node: Node, from: uint64, to: uint64) returns (subnode: Node)
    requires WF(node)
    requires node.contents.Index?
    requires 1 < node.contents.nchildren
    requires 0 <= from < to <= node.contents.nchildren
    ensures WFShape(subnode)
    ensures subnode.contents.Index?
    ensures subnode.repr == SubRepr(node, from as int, to as int) + {subnode, subnode.contents.pivots, subnode.contents.children}
    ensures subnode.height == node.height
    ensures I(subnode) == Spec.SubIndex(I(node), from as int, to as int)
    ensures fresh(subnode)
    ensures fresh(subnode.contents.pivots)
    ensures fresh(subnode.contents.children)
  {
    assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
    var subpivots := newArrayFill(MaxChildren()-1, DefaultKey());
    var subchildren := newArrayFill(MaxChildren(), null);
    Arrays.Memcpy(subpivots, 0, node.contents.pivots[from..to-1]); // FIXME: remove conversion to seq
    Arrays.Memcpy(subchildren, 0, node.contents.children[from..to]); // FIXME: remove conversion to seq
    subnode := new Node;
    subnode.repr := SubRepr(node, from as int, to as int) + {subnode, subpivots, subchildren};
    subnode.height := node.height;
    subnode.contents := Index(to - from, subpivots, subchildren);

    //assert forall i :: 0 <= i < to - from ==> subnode.contents.children[i as int] == node.contents.children[(from + i) as int];

    assert forall i :: 0 <= i < subnode.contents.nchildren ==> subnode.contents.children[i] == node.contents.children[from + i];

    forall i, j | 0 <= i < j < subnode.contents.nchildren
      ensures DisjointReprs(subnode.contents.children[i], subnode.contents.children[j])
    {
      assert DisjointReprs(node.contents.children[from + i], node.contents.children[from + j]);
    }

    SubReprLowerBound(node, from as int, to as int);
    forall i | 0 <= i < subnode.contents.nchildren
      ensures subnode.contents.children[i] in subnode.repr
    {
      assert subnode.contents.children[i] == node.contents.children[from + i];
      assert WFShape(node.contents.children[from + i]);
      assert node.contents.children[from + i] in node.contents.children[from + i].repr;
      assert node.contents.children[from + i].repr <= subnode.repr;
      assert node.contents.children[from + i] in subnode.repr;
    }
    forall i | 0 <= i < subnode.contents.nchildren
      ensures subnode.contents.children[i].height < subnode.height
    {
    }
    assert WFShapeChildren(subnode.contents.children[..subnode.contents.nchildren], subnode.repr, subnode.height);
    ghost var isubnode := I(subnode);
    ghost var inode := I(node);
    forall ensures isubnode.children == inode.children[from..to]
    {
      reveal_I();
    }
  }

  lemma SubReprsDisjoint(node: Node, from1: int, to1: int, from2: int, to2: int)
    requires WFShape(node)
    requires node.contents.Index?
    requires 0 <= from1 <= to1 <= from2 <= to2 <= node.contents.nchildren as int
    ensures SubRepr(node, from1, to1) !! SubRepr(node, from2, to2)
  {
    reveal_SubRepr();
    var subrepr1 := SubRepr(node, from1, to1);
    var subrepr2 := SubRepr(node, from2, to2);

    if o :| o in subrepr1 && o in subrepr2 {
      var i1 :| 0 <= from1 <= i1 < to1 && o in node.repr && ObjectIsInSubtree(node, o, i1);
      var i2 :| 0 <= from2 <= i2 < to2 && o in node.repr && ObjectIsInSubtree(node, o, i2);
      assert i1 < i2;
      assert DisjointSubtrees(node.contents, i1, i2);
    }
  }
  

  method SplitIndex(node: Node, nleft: uint64) returns (right: Node, ghost wit: Key, pivot: Key)
    requires WF(node)
    requires node.contents.Index?
    requires 2 <= node.contents.nchildren
    requires 0 < nleft < node.contents.nchildren
    ensures WFShape(node)
    ensures WFShape(right)
    ensures node.repr <= old(node.repr)
    ensures node.repr !! right.repr
    ensures fresh(right.repr - old(node.repr))
    ensures node.height == old(node.height) == right.height
    ensures Spec.SplitIndex(old(I(node)), I(node), I(right), wit, pivot)
    ensures node.contents.nchildren == nleft
    ensures pivot == old(node.contents.pivots[nleft-1])
    modifies node
  {
    SubReprsDisjoint(node, 0, nleft as int, nleft as int, node.contents.nchildren as int);
    SubReprUpperBound(node, 0, nleft as int);
    SubReprUpperBound(node, nleft as int, node.contents.nchildren as int);
    right := SubIndex(node, nleft, node.contents.nchildren);
    pivot := node.contents.pivots[nleft-1];
    IOfChild(node, 0);
    wit :| wit in Spec.AllKeys(I(node.contents.children[0]));
    IndexPrefix(node, nleft);
    ghost var inode := old(I(node));
    assert Spec.AllKeysBelowBound(inode, 0);
    Spec.Keys.IsStrictlySortedImpliesLte(old(I(node)).pivots, 0, (nleft - 1) as int);
    assert Spec.Keys.lt(wit, inode.pivots[0]);
    assert wit in Spec.AllKeys(inode);
    reveal_I();
  }

  method SplitNode(node: Node) returns (right: Node, ghost wit: Key, pivot: Key)
    requires WF(node)
    requires Full(node)
    ensures WFShape(node)
    ensures WFShape(right)
    ensures node.height == old(node.height)
    ensures right.height == old(node.height)
    ensures node.repr <= old(node.repr)
    ensures fresh(right.repr - old(node.repr))
    ensures node.repr !! right.repr
    ensures !Full(node)
    ensures !Full(right)
    ensures Spec.SplitNode(old(I(node)), I(node), I(right), wit, pivot)
    ensures pivot in Spec.AllKeys(old(I(node)))
    modifies node
  {
    if node.contents.Leaf? {
      var boundary := node.contents.nkeys/2;
      pivot := node.contents.keys[boundary];
      Spec.Keys.IsStrictlySortedImpliesLt(node.contents.keys[..node.contents.nkeys], boundary as int - 1, boundary as int);
      right, wit := SplitLeaf(node, node.contents.nkeys / 2, pivot);
    } else {
      var boundary := node.contents.nchildren/2;
      right, wit, pivot := SplitIndex(node, boundary);
    }
  }

  lemma ChildrenAreDistinct(node: Node)
    requires WFShape(node)
    requires node.contents.Index?
    ensures forall i, j :: 0 <= i < j < node.contents.nchildren ==> node.contents.children[i] != node.contents.children[j]
    ensures forall i :: 0 <= i < node.contents.nchildren ==> node.contents.children[i] != node
  {
    forall i, j | 0 <= i < j < node.contents.nchildren
      ensures node.contents.children[i] != node.contents.children[j]
    {
      assert WFShape(node.contents.children[i]);
      assert node.contents.children[i] in node.contents.children[i].repr;
      assert DisjointSubtrees(node.contents, i as int, j as int);
      if node.contents.children[i] == node.contents.children[j] {
        assert node.contents.children[i].repr == node.contents.children[j].repr;
        assert node.contents.children[i] in node.contents.children[j].repr;
        assert node.contents.children[i] in node.contents.children[i].repr * node.contents.children[j].repr;
        assert !(node.contents.children[i].repr !! node.contents.children[j].repr);
        assert false;
      }
    }
  }

  // twostate lemma SplitChildOfIndexPreservesDisjointSubtrees(node: Node, childidx: int)
  //   requires old(WFShape(node))
  //   requires old(node.contents).Index?
  //   requires old(!Full(node))
  //   requires 0 <= childidx < old(node.contents).nchildren as int
  //   requires node.contents.Index?
  //   requires node.contents.nchildren == old(node.contents).nchildren + 1
  //   requires node.contents.children.Length == old(node.contents.children.Length)
  //   requires forall i :: 0 <= i < node.contents.nchildren ==> node.contents.children[i] != null
  //   requires forall i :: 0 <= i < childidx ==> node.contents.children[i].repr == old(node.contents.children[i].repr)
  //   requires node.contents.children[childidx].repr <= old(node.contents.children[childidx].repr)
  //   requires fresh(node.contents.children[childidx+1].repr - old(node.contents.children[childidx].repr))
  //   requires forall i :: childidx+1 < i < node.contents.nchildren as int ==> node.contents.children[i].repr == old(node.contents.children[i-1].repr)
  //   requires DisjointSubtrees(node.contents, childidx, (childidx + 1));
  //   ensures forall i, j :: 0 <= i < j < node.contents.nchildren ==> DisjointSubtrees(node.contents, i as int, j as int)
  // {
  //   forall i, j | 0 <= i < j < node.contents.nchildren as int
  //     ensures DisjointSubtrees(node.contents, i, j)
  //   {
  //     if                           j <  childidx       {
  //       assert old(DisjointSubtrees(node.contents, i, j));
  //     } else if                    j == childidx       {
  //       assert old(DisjointSubtrees(node.contents, i, j));
  //     } else if i < childidx     && j == childidx+1     {
  //       assert old(DisjointSubtrees(node.contents, i, j - 1));
  //     } else if i == childidx    && j == childidx+1     {
  //       assert DisjointSubtrees(node.contents, childidx, (childidx + 1));
  //     } else if i < childidx     &&      childidx+1 < j {
  //       assert old(DisjointSubtrees(node.contents, i, (j-1)));
  //     } else if i == childidx    &&      childidx+1 < j {
  //       assert old(DisjointSubtrees(node.contents, i, (j-1)));
  //     } else if i == childidx+1  &&      childidx+1 < j {
  //       assert old(DisjointSubtrees(node.contents, (i-1), (j-1)));
  //     } else {
  //       assert old(DisjointSubtrees(node.contents, (i-1), (j-1)));
  //     }
  //   }
  // }

  twostate predicate SubtreeUnchanged(node: Node, oldchildidx: int, newchildidx: int)
    requires old(WFShape(node))
    requires old(node.contents).Index?
    requires node.contents.Index?
    requires node.contents.children == old(node.contents.children)
    requires 0 <= oldchildidx < old(node.contents).nchildren as int
    requires 0 <= newchildidx < node.contents.nchildren as int <= node.contents.children.Length
    reads node, node.contents.children, node.contents.children[newchildidx]
  {
    assert old(WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height));
    && node.contents.children[newchildidx] == old(node.contents.children[oldchildidx])
    && node.contents.children[newchildidx].repr == old(node.contents.children[oldchildidx].repr)
    && unchanged(node.contents.children[newchildidx].repr)
  }
    
  twostate lemma SplitChildOfIndexPreservesWFShape(node: Node, childidx: int)
    requires old(WFShape(node))
    requires old(node.contents).Index?
    requires old(!Full(node))
    requires 0 <= childidx < old(node.contents).nchildren as int
    requires node.contents.Index?
    requires node.contents.nchildren == old(node.contents).nchildren + 1
    requires node.contents.children == old(node.contents.children)
    requires node.contents.pivots == old(node.contents.pivots)
    requires node.height == old(node.height)
    requires unchanged(old(node.repr) - {node, node.contents.pivots, node.contents.children, node.contents.children[childidx]})
    requires forall i :: 0 <= i < childidx ==> node.contents.children[i] == old(node.contents.children[i])
    requires forall i :: childidx + 1 < i < node.contents.nchildren as int ==> node.contents.children[i] == old(node.contents.children[i-1])
    requires old(node.contents.children[childidx]) != null
    requires node.contents.children[childidx] != null
    requires WFShape(node.contents.children[childidx])
    requires node.contents.children[childidx].repr <= old(node.contents.children[childidx].repr)
    requires node.contents.children[childidx].height == old(node.contents.children[childidx].height)
    requires node.contents.children[childidx+1] != null
    requires WFShape(node.contents.children[childidx+1])
    requires fresh(node.contents.children[childidx+1].repr - old(node.contents.children[childidx].repr))
    requires node.contents.children[childidx+1].height == old(node.contents.children[childidx].height)
    requires DisjointSubtrees(node.contents, childidx, (childidx + 1))
    requires node.repr == old(node.repr) + node.contents.children[childidx+1].repr
    ensures WFShape(node)
  {
    assert old(WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height));
    
    forall i | 0 <= i < node.contents.nchildren as int
      ensures node.contents.children[i] != null
      ensures node.contents.children[i] in node.repr
      ensures node.contents.children[i].repr < node.repr
      ensures node !in node.contents.children[i].repr
      ensures node.contents.pivots !in node.contents.children[i].repr
      ensures node.contents.children !in node.contents.children[i].repr
      ensures node.contents.children[i].height < node.height
      ensures WFShape(node.contents.children[i])
    {
      if i < childidx {
        assert old(DisjointSubtrees(node.contents, i, childidx));
        assert SubtreeUnchanged(node, i, i);
      } else if i == childidx {
      } else if i == childidx + 1 {
      } else {
        assert old(DisjointSubtrees(node.contents, childidx, i-1));
        assert SubtreeUnchanged(node, i-1, i);
      }
    }

    forall i, j | 0 <= i < j < node.contents.nchildren as int
      ensures DisjointSubtrees(node.contents, i, j)
    {
      if                           j <  childidx       {
        assert old(DisjointSubtrees(node.contents, i, childidx));
        assert old(DisjointSubtrees(node.contents, j, childidx));
        assert SubtreeUnchanged(node, i, i);
        assert SubtreeUnchanged(node, j, j);
        assert old(DisjointSubtrees(node.contents, i, j));
      } else if                    j == childidx       {
        assert old(DisjointSubtrees(node.contents, i, childidx));
        assert SubtreeUnchanged(node, i, i);
        assert old(DisjointSubtrees(node.contents, i, j));
      } else if i < childidx     && j == childidx+1     {
        assert old(DisjointSubtrees(node.contents, i, childidx));
        assert SubtreeUnchanged(node, i, i);
        assert old(DisjointSubtrees(node.contents, i, j - 1));
      } else if i == childidx    && j == childidx+1     {
        assert DisjointSubtrees(node.contents, childidx, (childidx + 1));
      } else if i < childidx     &&      childidx+1 < j {
        assert old(DisjointSubtrees(node.contents, i, childidx));
        assert old(DisjointSubtrees(node.contents, childidx, (j-1)));
        assert SubtreeUnchanged(node, i, i);
        assert SubtreeUnchanged(node, j-1, j);
        assert old(DisjointSubtrees(node.contents, i, (j-1)));
      } else if i == childidx    &&      childidx+1 < j {
        assert old(DisjointSubtrees(node.contents, childidx, (j-1)));
        assert SubtreeUnchanged(node, j-1, j);
        assert old(DisjointSubtrees(node.contents, i, (j-1)));
      } else if i == childidx+1  &&      childidx+1 < j {
        assert old(DisjointSubtrees(node.contents, childidx, (j-1)));
        assert SubtreeUnchanged(node, j-1, j);
        assert old(DisjointSubtrees(node.contents, (i-1), (j-1)));
      } else {
        assert old(DisjointSubtrees(node.contents, childidx, (i-1)));
        assert old(DisjointSubtrees(node.contents, childidx, (j-1)));
        assert SubtreeUnchanged(node, i-1, i);
        assert SubtreeUnchanged(node, j-1, j);
        assert old(DisjointSubtrees(node.contents, (i-1), (j-1)));
      }
    }
  }
  
  method SplitChildOfIndex(node: Node, childidx: uint64)  returns (ghost wit: Key)
    requires WF(node)
    requires node.contents.Index?
    requires !Full(node)
    requires 0 <= childidx < node.contents.nchildren
    requires node.contents.children[childidx] != null
    requires Full(node.contents.children[childidx]);
    ensures WFShape(node)
    ensures node.contents.Index?
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures Spec.SplitChildOfIndex(old(I(node)), I(node), childidx as int, wit)
    ensures node.contents.children[childidx] != null
    ensures node.contents.children[childidx+1] != null
    ensures !Full(node.contents.children[childidx])
    ensures !Full(node.contents.children[childidx+1])
    ensures node.contents.pivots[childidx] in Spec.AllKeys(old(I(node)).children[childidx])
    modifies node, node.contents.pivots, node.contents.children, node.contents.children[childidx]
  {
    assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
    
    forall i | 0 <= i < node.contents.nchildren
      ensures I(node).children[i] == I(node.contents.children[i])
    {
      IOfChild(node, i as int);
    }
    
    var right, wit', pivot := SplitNode(node.contents.children[childidx]);
    Arrays.Insert(node.contents.pivots, node.contents.nchildren-1, pivot, childidx);
    Arrays.Insert(node.contents.children, node.contents.nchildren, right, childidx + 1);
    node.contents := node.contents.(nchildren := node.contents.nchildren + 1);
    node.repr := node.repr + right.repr;
    wit := wit';

    SplitChildOfIndexPreservesWFShape(node, childidx as int);
    
    ghost var ioldnode := old(I(node));
    ghost var inode := I(node);
    ghost var iright := I(right);
    ghost var target := Seq.replace1with2(ioldnode.children, inode.children[childidx], iright, childidx as int);
    forall i | 0 <= i < |inode.children|
      ensures inode.children[i] == target[i]
    {
      IOfChild(node, i);
      if i < childidx as int {
        assert old(DisjointSubtrees(node.contents, i as int, childidx as int));
      } else if i == childidx as int {
      } else if i == (childidx + 1) as int {
      } else {
        assert old(DisjointSubtrees(node.contents, childidx as int, (i-1) as int));      
      }
    }

    IOfChild(node, childidx as int);
    IOfChild(node, childidx as int + 1);
  }

  method InsertLeaf(node: Node, key: Key, value: Value)
    requires WF(node)
    requires node.contents.Leaf?
    requires !Full(node)
    ensures WFShape(node)
    ensures node.repr == old(node.repr)
    ensures I(node) == Spec.InsertLeaf(old(I(node)), key, value)
    ensures Spec.WF(I(node))
    ensures Spec.Interpretation(I(node)) == Spec.Interpretation(old(I(node)))[key := value]
    ensures Spec.AllKeys(I(node)) == Spec.AllKeys(old(I(node))) + {key}
    modifies node, node.contents.keys, node.contents.values
  {
    var posplus1: uint64 := Spec.Keys.ArrayLargestLtePlus1(node.contents.keys, 0, node.contents.nkeys, key);
    if 1 <= posplus1 && node.contents.keys[posplus1-1] == key {
      node.contents.values[posplus1-1] := value;
    } else {
      Arrays.Insert(node.contents.keys, node.contents.nkeys, key, posplus1);
      Arrays.Insert(node.contents.values, node.contents.nkeys, value, posplus1);
      node.contents := node.contents.(nkeys := node.contents.nkeys + 1);
    }
    Spec.InsertLeafIsCorrect(old(I(node)), key, value);
  }

  twostate lemma InsertIndexChildNotFullPreservesWFShape(node: Node, childidx: int)
    requires old(WFShape(node))
    requires old(node.contents).Index?
    requires 0 <= childidx < old(node.contents).nchildren as int
    requires node.contents.Index?
    requires node.contents.nchildren == old(node.contents).nchildren
    requires node.contents.children == old(node.contents.children)
    requires node.contents.pivots == old(node.contents.pivots)
    requires node.height == old(node.height)
    requires old(node.contents.children[childidx]) != null
    requires node.contents.children[childidx] != null
    requires unchanged(old(node.repr) - ({node} + old(node.contents.children[childidx].repr)))
    requires forall i :: 0 <= i < childidx ==> node.contents.children[i] == old(node.contents.children[i])
    requires forall i :: childidx < i < node.contents.nchildren as int ==> node.contents.children[i] == old(node.contents.children[i])
    requires WFShape(node.contents.children[childidx])
    requires node.contents.children[childidx].height == old(node.contents.children[childidx].height)
    requires fresh(node.contents.children[childidx].repr - old(node.contents.children[childidx].repr))
    requires node.repr == old(node.repr) + node.contents.children[childidx].repr
    ensures WFShape(node)
  {
    assert old(WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height));
    
    forall i | 0 <= i < node.contents.nchildren as int
      ensures node.contents.children[i] != null
      ensures node.contents.children[i] in node.repr
      ensures node.contents.children[i].repr < node.repr
      ensures node !in node.contents.children[i].repr
      ensures node.contents.pivots !in node.contents.children[i].repr
      ensures node.contents.children !in node.contents.children[i].repr
      ensures node.contents.children[i].height < node.height
      ensures WFShape(node.contents.children[i])
    {
      if i < childidx {
        assert old(DisjointSubtrees(node.contents, i, childidx));
        assert SubtreeUnchanged(node, i, i);
      } else if i == childidx {
      } else {
        assert old(DisjointSubtrees(node.contents, childidx, i));
        assert SubtreeUnchanged(node, i, i);
      }
    }

    forall i, j | 0 <= i < j < node.contents.nchildren as int
      ensures DisjointSubtrees(node.contents, i, j)
    {
      if                           j <  childidx       {
        assert old(DisjointSubtrees(node.contents, i, childidx));
        assert old(DisjointSubtrees(node.contents, j, childidx));
        assert SubtreeUnchanged(node, i, i);
        assert SubtreeUnchanged(node, j, j);
        assert old(DisjointSubtrees(node.contents, i, j));
      } else if                    j == childidx       {
        assert old(DisjointSubtrees(node.contents, i, childidx));
        assert SubtreeUnchanged(node, i, i);
        assert old(DisjointSubtrees(node.contents, i, j));
      } else if i < childidx     &&      childidx < j {
        assert old(DisjointSubtrees(node.contents, i, childidx));
        assert old(DisjointSubtrees(node.contents, childidx, j));
        assert SubtreeUnchanged(node, i, i);
        assert SubtreeUnchanged(node, j, j);
        assert old(DisjointSubtrees(node.contents, i, j));
      } else if i == childidx    &&      childidx < j {
        assert old(DisjointSubtrees(node.contents, childidx, j));
        assert SubtreeUnchanged(node, j, j);
        assert old(DisjointSubtrees(node.contents, i, j));
      } else {
        assert old(DisjointSubtrees(node.contents, childidx, i));
        assert old(DisjointSubtrees(node.contents, childidx, j));
        assert SubtreeUnchanged(node, i, i);
        assert SubtreeUnchanged(node, j, j);
        assert old(DisjointSubtrees(node.contents, i, j));
      }
    }
    
  }

  method InsertIndexChildNotFull(node: Node, childidx: uint64, key: Key, value: Value)
    requires WF(node)
    requires node.contents.Index?
    requires childidx as int == Spec.Keys.LargestLte(node.contents.pivots[..node.contents.nchildren-1], key) + 1
    requires node.contents.children[childidx] != null
    requires !Full(node.contents.children[childidx])
    ensures WFShape(node)
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures Spec.WF(I(node))
    ensures Spec.Interpretation(I(node)) == Spec.Interpretation(old(I(node)))[key := value]
    ensures Spec.AllKeys(I(node)) <= Spec.AllKeys(old(I(node))) + {key}
    modifies node, node.contents.children[childidx], node.contents.children[childidx].repr
    decreases node.height, 0
  {
    assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);

    forall i | 0 <= i < node.contents.nchildren
      ensures I(node.contents.children[i]) == I(node).children[i]
    {
      IOfChild(node, i as int);
    }
    
    InsertNode(node.contents.children[childidx], key, value);
    node.repr := node.repr + node.contents.children[childidx].repr;
    
    InsertIndexChildNotFullPreservesWFShape(node, childidx as int);
    
    ghost var oldinode := old(I(node));
    ghost var inode := I(node);
    ghost var oldchild := oldinode.children[childidx];
    ghost var newchild := inode.children[childidx];

    forall i | 0 <= i < childidx as int
      ensures inode.children[i] == oldinode.children[i]
    {
      IOfChild(node, i);
      assert old(DisjointSubtrees(node.contents, i as int, childidx as int));
    }
    forall i | childidx as int < i < |inode.children|
      ensures inode.children[i] == oldinode.children[i]
    {
      IOfChild(node, i);
      assert old(DisjointSubtrees(node.contents, childidx as int, i as int));
    }

    IOfChild(node, childidx as int);
    Spec.RecursiveInsertIsCorrect(oldinode, key, value, childidx as int, inode, inode.children[childidx]);
  }

  method InsertIndexSelectAndPrepareChild(node: Node, key: Key) returns (childidx: uint64)
    requires WF(node)
    requires node.contents.Index?
    requires !Full(node)
    ensures WFShape(node)
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures Spec.WF(I(node))
    ensures node.contents.Index?
    ensures childidx as int == Spec.Keys.LargestLte(node.contents.pivots[..node.contents.nchildren-1], key) + 1
    ensures node.contents.children[childidx] != null
    ensures !Full(node.contents.children[childidx])
    ensures Spec.Interpretation(I(node)) == Spec.Interpretation(old(I(node)))
    ensures Spec.AllKeys(I(node)) == Spec.AllKeys(old(I(node)))
    modifies node, node.repr
  {
    assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);

    childidx := Spec.Keys.ArrayLargestLtePlus1(node.contents.pivots, 0, node.contents.nchildren-1, key);
    if Full(node.contents.children[childidx]) {
      ghost var oldpivots := node.contents.pivots[..node.contents.nchildren-1];
      var wit := SplitChildOfIndex(node, childidx);
      ghost var newpivots := node.contents.pivots[..node.contents.nchildren-1];
      Spec.SplitChildOfIndexPreservesWF(old(I(node)), I(node), childidx as int, wit);
      Spec.SplitChildOfIndexPreservesInterpretation(old(I(node)), I(node), childidx as int, wit);
      Spec.SplitChildOfIndexPreservesAllKeys(old(I(node)), I(node), childidx as int, wit);

      var t: int32 := Spec.Keys.cmp(node.contents.pivots[childidx], key);
      if  t <= 0 {
        childidx := childidx + 1;
        forall i | childidx as int - 1 < i < |newpivots|
          ensures Spec.Keys.lt(key, newpivots[i])
        {
          assert newpivots[i] == oldpivots[i-1];
        }
      }
      Spec.Keys.LargestLteIsUnique(node.contents.pivots[..node.contents.nchildren-1], key, childidx as int - 1);
    }
  }
  
  method InsertIndex(node: Node, key: Key, value: Value)
    requires WF(node)
    requires node.contents.Index?
    requires !Full(node)
    ensures WFShape(node)
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures Spec.WF(I(node))
    ensures Spec.Interpretation(I(node)) == Spec.Interpretation(old(I(node)))[key := value]
    ensures Spec.AllKeys(I(node)) <= Spec.AllKeys(old(I(node))) + {key}
    modifies node, node.repr
    decreases node.height, 1
  {
    var childidx: uint64 := InsertIndexSelectAndPrepareChild(node, key);
    InsertIndexChildNotFull(node, childidx, key, value);
  }
  
  method InsertNode(node: Node, key: Key, value: Value)
    requires WF(node)
    requires !Full(node)
    ensures WFShape(node)
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures Spec.WF(I(node))
    ensures Spec.Interpretation(I(node)) == Spec.Interpretation(old(I(node)))[key := value]
    ensures Spec.AllKeys(I(node)) <= Spec.AllKeys(old(I(node))) + {key}
    modifies node, node.repr
    decreases node.height, 2
  {
    if node.contents.Leaf? {
      InsertLeaf(node, key, value);
    } else {
      InsertIndex(node, key, value);
    }
  }

  method Grow(root: Node) returns (newroot: Node)
    requires WF(root)
    requires Full(root)
    ensures WFShape(newroot)
    ensures fresh(newroot.repr - root.repr)
    ensures newroot.height == root.height + 1
    ensures I(newroot) == Spec.Grow(I(root))
    ensures !Full(newroot)
  {
    newroot := new Node;
    var newpivots := newArrayFill(MaxChildren()-1, DefaultKey());
    var newchildren := newArrayFill(MaxChildren(), null);
    newchildren[0] := root;
    newroot.contents := Index(1, newpivots, newchildren);
    newroot.repr := {newroot, newpivots, newchildren} + root.repr;
    newroot.height := root.height + 1;

    ghost var inewroot := I(newroot);
    IOfChild(newroot, 0);
    assert inewroot.children == [ I(root) ];
  }

  lemma FullImpliesAllKeysNonEmpty(node: Node)
    requires WF(node)
    requires Full(node)
    ensures Spec.AllKeys(I(node)) != {}
  {
    var inode := I(node);
    if inode.Leaf? {
      assert inode.keys[0] in Spec.AllKeys(inode);
    } else {
      assert inode.pivots[0] in Spec.AllKeys(inode);
    }
  }
  
  method Insert(root: Node, key: Key, value: Value) returns (newroot: Node)
    requires WF(root)
    ensures WF(newroot)
    ensures fresh(newroot.repr - old(root.repr))
    ensures Interpretation(newroot) == old(Interpretation(root))[key := value]
    modifies root.repr
  {
    if Full(root) {
      FullImpliesAllKeysNonEmpty(root);
      Spec.GrowPreservesWF(I(root));
      newroot := Grow(root);
      Spec.GrowPreservesInterpretation(I(root));
    } else {
      newroot := root;
    }
    assert Spec.Interpretation(I(newroot)) == Spec.Interpretation(old(I(root)));
    InsertNode(newroot, key, value);
  }
}

module TestBtreeSpec refines BtreeSpec {
  import opened NativeTypes
  import Keys = Uint64_Order
  type Value = uint64
}

module TestMutableBtree refines MutableBtree {
  import Spec = TestBtreeSpec
    
  function method MaxKeysPerLeaf() : uint64 { 64 }
  function method MaxChildren() : uint64 { 64 }

  function method DefaultValue() : Value { 0 }
  function method DefaultKey() : Key { 0 }
}

module MainModule {
  import opened NativeTypes
  import TMB = TestMutableBtree`API
  
  method Main()
  {
    // var n: uint64 := 1_000_000;
    // var p: uint64 := 300_007;
    var n: uint64 := 10_000_000;
    var p: uint64 := 3_000_017;
    // var n: uint64 := 100_000_000;
    // var p: uint64 := 1_073_741_827;
    var t := TMB.EmptyTree();
    var i: uint64 := 0;
    while i < n
      invariant 0 <= i <= n
      invariant TMB.WF(t)
      invariant fresh(t.repr)
    {
      t := TMB.Insert(t, ((i * p) % n), i);
      i := i + 1;
    }

    // i := 0;
    // while i < n
    //   invariant 0 <= i <= n
    // {
    //   var needle := (i * p) % n;
    //   var qr := t.Query(needle);
    //   if qr != TestMutableBtree.Found(i) {
    //     print "Test failed";
  //   } else {
  //     //print "Query ", i, " for ", needle, "resulted in ", qr.value, "\n";
  //   }
  //   i := i + 1;
  // }

  // i := 0;
  // while i < n
  //   invariant 0 <= i <= n
  // {
  //   var qr := t.Query(n + ((i * p) % n));
  //   if qr != TestMutableBtree.NotFound {
  //     print "Test failed";
  //   } else {
  //     //print "Didn't return bullsh*t\n";
  //   }
  //   i := i + 1;
  // }
    print "PASSED\n";
  }
} 
