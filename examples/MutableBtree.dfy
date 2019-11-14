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

  class Node {
    var contents: NodeContents
    ghost var repr: set<object>
    ghost var height: nat
  }
    
  datatype NodeContents =
    | Leaf(nkeys: uint64, keys: array<Key>, values: array<Value>)
    | Index(nchildren: uint64, pivots: array<Key>, children: array<Node?>)

  predicate DisjointSubtrees(node: NodeContents, i: int, j: int)
    requires node.Index?
    requires 0 <= i < node.children.Length
    requires 0 <= j < node.children.Length
    requires node.children[i] != null
    requires node.children[j] != null
    requires i != j
    reads node.children, node.children[i], node.children[j]
  {
    node.children[i].repr !! node.children[j].repr
  }

  predicate WFShape(node: Node)
    reads node, node.repr
    decreases node.height
  {
    if node.contents.Leaf? then
      && node.repr == { node, node.contents.keys, node.contents.values }
      && node.contents.keys != node.contents.values
      && node.height == 0
      && 0 <= node.contents.nkeys as int <= MaxKeysPerLeaf() as int == node.contents.keys.Length
      && node.contents.values.Length == node.contents.keys.Length
    else
      && { node, node.contents.pivots, node.contents.children } <= node.repr
      && 0 < node.contents.nchildren as int <= MaxChildren() as int == node.contents.children.Length
      && node.contents.pivots.Length == MaxChildren() as int - 1
      && (forall i :: 0 <= i < node.contents.nchildren ==> node.contents.children[i] != null)
      && (forall i :: 0 <= i < node.contents.nchildren ==> node.contents.children[i] in node.repr)
      && (forall i :: 0 <= i < node.contents.nchildren ==> node.contents.children[i].repr < node.repr)
      && (forall i :: 0 <= i < node.contents.nchildren ==> node !in node.contents.children[i].repr)
      && (forall i :: 0 <= i < node.contents.nchildren ==> node.contents.pivots !in node.contents.children[i].repr)
      && (forall i :: 0 <= i < node.contents.nchildren ==> node.contents.children !in node.contents.children[i].repr)
      && (forall i, j :: 0 <= i < j < node.contents.nchildren as int ==> DisjointSubtrees(node.contents, i, j))
      && (forall i :: 0 <= i < node.contents.nchildren ==> node.contents.children[i].height < node.height)
      && (forall i :: 0 <= i < node.contents.nchildren ==> WFShape(node.contents.children[i]))
  }

  function Ichildren(nodes: seq<Node>, parentheight: int) : (result: seq<BS.Node>)
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
  
  function I(node: Node) : (result: BS.Node)
    requires WFShape(node)
    reads node, node.repr
    decreases node.height
  {
    match node.contents {
      case Leaf(nkeys, keys, values) => BS.Leaf(keys[..nkeys], values[..nkeys])
      case Index(nchildren, pivots, children) =>
        var bschildren := Ichildren(children[..nchildren], node.height);
        BS.Index(pivots[..nchildren-1], bschildren)
    }
  }

  method QueryLeaf(node: Node, needle: Key) returns (result: BS.QueryResult)
    requires WFShape(node)
    requires BS.WF(I(node))
    requires node.contents.Leaf?
    ensures needle in BS.Interpretation(I(node)) ==> result == BS.Found(BS.Interpretation(I(node))[needle])
    ensures needle !in BS.Interpretation(I(node)) ==> result == BS.NotFound
    decreases node.height, 0
  {
    var posplus1: uint64 := BS.Keys.ArrayLargestLtePlus1(node.contents.keys, 0, node.contents.nkeys, needle);
    if 1 <= posplus1 && node.contents.keys[posplus1-1] == needle {
      result := BS.Found(node.contents.values[posplus1-1]);
    } else {
      result := BS.NotFound;
    }
  }

  method QueryIndex(node: Node, needle: Key) returns (result: BS.QueryResult)
    requires WFShape(node)
    requires BS.WF(I(node))
    requires node.contents.Index?
    ensures needle in BS.Interpretation(I(node)) ==> result == BS.Found(BS.Interpretation(I(node))[needle])
    ensures needle !in BS.Interpretation(I(node)) ==> result == BS.NotFound
    decreases node.height, 0
  {
    var posplus1 := BS.Keys.ArrayLargestLtePlus1(node.contents.pivots, 0, node.contents.nchildren-1, needle);
    result := Query(node.contents.children[posplus1], needle);
  }

  method Query(node: Node, needle: Key) returns (result: BS.QueryResult)
    requires WFShape(node)
    requires BS.WF(I(node))
    ensures needle in BS.Interpretation(I(node)) ==> result == BS.Found(BS.Interpretation(I(node))[needle])
    ensures needle !in BS.Interpretation(I(node)) ==> result == BS.NotFound
    decreases node.height, 1
  {
    match node.contents {
      case Leaf(_, _, _) => result := QueryLeaf(node, needle);
      case Index(_, _, _) => result := QueryIndex(node, needle);
    }
  }

  predicate method Full(node: Node)
    reads node
  {
    match node.contents {
      case Leaf(nkeys, _, _) => nkeys == MaxKeysPerLeaf()
      case Index(nchildren, _, _) => nchildren == MaxChildren()
    }
  }

  method SplitLeaf(node: Node) returns (right: Node, ghost wit: Key, pivot: Key)
    requires WFShape(node)
    requires BS.WF(I(node))
    requires node.contents.Leaf?
    requires Full(node)
    ensures WFShape(node)
    ensures WFShape(right)
    ensures BS.SplitLeaf(old(I(node)), I(node), I(right), wit, pivot)
    ensures node.repr == old(node.repr)
    ensures fresh(right.repr)
    modifies node
  {
    var rightkeys := new Key[MaxKeysPerLeaf()](_ => DefaultKey());
    var rightvalues := new Value[MaxKeysPerLeaf()](_ => DefaultValue());
    var boundary := node.contents.nkeys / 2;
    Arrays.Memcpy(rightkeys, 0, node.contents.keys[boundary..node.contents.nkeys]); // FIXME: remove conversion to seq
    Arrays.Memcpy(rightvalues, 0, node.contents.values[boundary..node.contents.nkeys]); // FIXME: remove conversion to seq

    right := new Node;
    right.repr := {right, rightkeys, rightvalues};
    right.height := 0;
    right.contents := Leaf(node.contents.nkeys - boundary, rightkeys, rightvalues);

    node.contents := Leaf(boundary, node.contents.keys, node.contents.values);
    wit := node.contents.keys[0];
    pivot := right.contents.keys[0];
  }

  predicate ObjectIsInSubtree(node: Node, o: object, i: int)
    requires WFShape(node)
    requires node.contents.Index?
    requires 0 <= i < node.contents.nchildren as int
    reads node.repr
  {
    o in node.contents.children[i].repr
  }

  function SubRepr(node: Node, from: int, to: int) : (result: set<object>)
    requires WFShape(node)
    requires node.contents.Index?
    requires 0 <= from <= to <= node.contents.nchildren as int
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
    var subrepr := SubRepr(node, from, to);
    var nchildren := node.contents.nchildren;
    var pivots := node.contents.pivots;
    var children := node.contents.children;
    
    assert subrepr <= node.repr;
    assert pivots !in subrepr;
    assert children !in subrepr;
    assert subrepr <= node.repr - {node, pivots, children};
    
    if to - from < nchildren as int {
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
    requires 1 < node.contents.nchildren
    requires 0 <= from <= to <= node.contents.nchildren as int
    ensures forall i :: from <= i < to ==> node.contents.children[i].repr <= SubRepr(node, from, to)
  {
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
    requires WFShape(node)
    requires BS.WF(I(node))
    requires node.contents.Index?
    requires 1 < newnchildren
    requires 0 <= newnchildren <= node.contents.nchildren
    ensures WFShape(node)
    ensures node.repr == old({node, node.contents.pivots, node.contents.children} + SubRepr(node, 0, newnchildren as int))
    ensures node.height == old(node.height)
    ensures I(node) == BS.SubIndex(old(I(node)), 0, newnchildren as int)
    modifies node
  {
    ghost var oldinode := I(node);
    SubReprLowerBound(node, 0, newnchildren as int);
    node.repr := {node, node.contents.pivots, node.contents.children} + SubRepr(node, 0, newnchildren as int);
    node.contents := node.contents.(nchildren := newnchildren);
    forall i, j | 0 <= i < j < node.contents.nchildren as int
      ensures DisjointSubtrees(node.contents, i, j)
    {
      assert old(DisjointSubtrees(node.contents, i, j));
    }
    ghost var newinode := I(node);
    assert newinode == BS.SubIndex(oldinode, 0, newnchildren as int);
  }

  method SubIndex(node: Node, from: uint64, to: uint64) returns (subnode: Node)
    requires WFShape(node)
    requires BS.WF(I(node))
    requires node.contents.Index?
    requires 1 < node.contents.nchildren
    requires 0 <= from < to <= node.contents.nchildren
    ensures WFShape(subnode)
    ensures subnode.contents.Index?
    ensures subnode.repr == SubRepr(node, from as int, to as int) + {subnode, subnode.contents.pivots, subnode.contents.children}
    ensures subnode.height == node.height
    ensures I(subnode) == BS.SubIndex(I(node), from as int, to as int)
    ensures fresh(subnode)
    ensures fresh(subnode.contents.pivots)
    ensures fresh(subnode.contents.children)
  {
    var subpivots := new Key[MaxChildren()-1](_ => DefaultKey());
    var subchildren := new Node?[MaxChildren()](_ => null);
    Arrays.Memcpy(subpivots, 0, node.contents.pivots[from..to-1]); // FIXME: remove conversion to seq
    Arrays.Memcpy(subchildren, 0, node.contents.children[from..to]); // FIXME: remove conversion to seq
    subnode := new Node;
    subnode.repr := SubRepr(node, from as int, to as int) + {subnode, subpivots, subchildren};
    subnode.height := node.height;
    subnode.contents := Index(to - from, subpivots, subchildren);

    assert forall i :: 0 <= i < to - from ==> subnode.contents.children[i as int] == node.contents.children[(from + i) as int];

    forall i, j | 0 <= i < j < subnode.contents.nchildren
      ensures DisjointSubtrees(subnode.contents, i as int, j as int)
    {
      assert DisjointSubtrees(node.contents, (from + i) as int, (from + j) as int);
    }

    SubReprLowerBound(node, from as int, to as int);

    // WTF?  Why is this necessary?
    ghost var inode := I(node);
    ghost var isubnode := I(subnode);
    assert I(subnode) == BS.SubIndex(I(node), from as int, to as int);
  }

  lemma SubReprsDisjoint(node: Node, from1: int, to1: int, from2: int, to2: int)
    requires WFShape(node)
    requires node.contents.Index?
    requires 0 <= from1 <= to1 <= from2 <= to2 <= node.contents.nchildren as int
    ensures SubRepr(node, from1, to1) !! SubRepr(node, from2, to2)
  {
    var subrepr1 := SubRepr(node, from1, to1);
    var subrepr2 := SubRepr(node, from2, to2);

    if o :| o in subrepr1 && o in subrepr2 {
      var i1 :| 0 <= from1 <= i1 < to1 && o in node.repr && ObjectIsInSubtree(node, o, i1);
      var i2 :| 0 <= from2 <= i2 < to2 && o in node.repr && ObjectIsInSubtree(node, o, i2);
      assert i1 < i2;
      assert DisjointSubtrees(node.contents, i1, i2);
    }
  }
  

  method SplitIndex(node: Node) returns (right: Node, ghost wit: Key, pivot: Key)
    requires WFShape(node)
    requires BS.WF(I(node))
    requires node.contents.Index?
    requires Full(node)
    ensures WFShape(node)
    ensures WFShape(right)
    ensures BS.SplitIndex(old(I(node)), I(node), I(right), wit, pivot)
    ensures node.repr <= old(node.repr)
    ensures node.repr !! right.repr
    ensures fresh(right.repr - old(node.repr))
    ensures node.height == old(node.height) == right.height
    modifies node
  {
    var boundary: uint64 := node.contents.nchildren / 2;
    SubReprsDisjoint(node, 0, boundary as int, boundary as int, node.contents.nchildren as int);
    right := SubIndex(node, boundary, node.contents.nchildren);
    pivot := node.contents.pivots[boundary-1];
    wit := node.contents.pivots[0];
    IndexPrefix(node, boundary);

    BS.Keys.IsStrictlySortedImpliesLt(old(I(node)).pivots, 0, (boundary - 1) as int);
  }
  
  method SplitNode(node: Node) returns (right: Node, ghost wit: Key, pivot: Key)
    requires WFShape(node)
    requires BS.WF(I(node))
    requires Full(node)
    ensures WFShape(node)
    ensures WFShape(right)
    ensures node.height == old(node.height)
    ensures right.height == old(node.height)
    ensures BS.SplitNode(old(I(node)), I(node), I(right), wit, pivot)
    ensures node.repr <= old(node.repr)
    ensures fresh(right.repr - old(node.repr))
    ensures node.repr !! right.repr
    modifies node
  {
    if node.contents.Leaf? {
      right, wit, pivot := SplitLeaf(node);
    } else {
      right, wit, pivot := SplitIndex(node);
    }
  }

  method SplitChildOfIndex(node: Node, childidx: uint64)  returns (ghost wit: Key)
    requires WFShape(node)
    requires BS.WF(I(node))
    requires node.contents.Index?
    requires !Full(node)
    requires 0 <= childidx < node.contents.nchildren
    requires Full(node.contents.children[childidx]);
    ensures WFShape(node)
    ensures node.contents.Index?
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures BS.SplitChildOfIndex(old(I(node)), I(node), childidx as int, wit)
    modifies node, node.contents.pivots, node.contents.children, node.contents.children[childidx]
  {
    ghost var oldnchildren := node.contents.nchildren;
    ghost var ioldnode := I(node);
    ghost var ichild := I(node.contents.children[childidx]);
    var right, wit', pivot := SplitNode(node.contents.children[childidx]);
    ghost var ileft := I(node.contents.children[childidx]);
    ghost var iright := I(right);

    Arrays.Insert(node.contents.pivots, node.contents.nchildren-1, pivot, childidx);
    Arrays.Insert(node.contents.children, node.contents.nchildren, right, childidx + 1);
    node.contents := node.contents.(nchildren := node.contents.nchildren + 1);
    node.repr := node.repr + right.repr;
    wit := wit';

    forall i | 0 <= i < node.contents.nchildren
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
        assert old(DisjointSubtrees(node.contents, i as int, childidx as int));
      } else if i == childidx {
      } else if i == childidx + 1 {
      } else {
        assert node.contents.children[i] == old(node.contents.children[i-1]);
        assert old(DisjointSubtrees(node.contents, childidx as int, (i-1) as int));
      }
    }

    forall i: uint64, j: uint64 | 0 <= i < j < node.contents.nchildren
      ensures DisjointSubtrees(node.contents, i as int, j as int)
    {
      if                           j <  childidx       {
        assert old(DisjointSubtrees(node.contents, i as int, j as int));
      } else if                    j == childidx       {
        assert old(DisjointSubtrees(node.contents, i as int, j as int));
      } else if i < childidx     && j == childidx+1     {
        assert old(DisjointSubtrees(node.contents, i as int, j as int - 1));
      } else if i == childidx    && j == childidx+1     {
        assert node.contents.children[childidx+1] == right;
        assert node.contents.children[childidx].repr !! right.repr;
        assert DisjointSubtrees(node.contents, childidx as int, (childidx + 1) as int);
      } else if i < childidx     &&      childidx+1 < j {
        assert node.contents.children[j] == old(node.contents.children[j-1]);
        assert old(DisjointSubtrees(node.contents, i as int, (j-1) as int));
      } else if i == childidx    &&      childidx+1 < j {
        assert node.contents.children[j] == old(node.contents.children[j-1]);
        assert old(DisjointSubtrees(node.contents, i as int, (j-1) as int));
      } else if i == childidx+1  &&      childidx+1 < j {
        assert node.contents.children[j] == old(node.contents.children[j-1]);
        assert old(DisjointSubtrees(node.contents, (i-1) as int, (j-1) as int));
      } else {
        assert node.contents.children[i] == old(node.contents.children[i-1]);
        assert node.contents.children[j] == old(node.contents.children[j-1]);
        assert old(DisjointSubtrees(node.contents, (i-1) as int, (j-1) as int));
      }
    }

    ghost var inode := I(node);

    ghost var target := Seq.replace1with2(ioldnode.children, inode.children[childidx], iright, childidx as int);
    forall i | 0 <= i < |inode.children|
      ensures inode.children[i] == target[i]
    {
      if i < childidx as int {
        assert old(DisjointSubtrees(node.contents, i as int, childidx as int));
        assert inode.children[i] == ioldnode.children[i] == target[i];
      } else if i == childidx as int {
        assert inode.children[i] == ileft == target[i];
      } else if i == (childidx + 1) as int {
        assert inode.children[i] == iright == target[i];
      } else {
        assert old(DisjointSubtrees(node.contents, childidx as int, (i-1) as int));      
        assert inode.children[i] == ioldnode.children[i-1] == target[i];
      }
    }
    assert inode.children == Seq.replace1with2(ioldnode.children, inode.children[childidx], iright, childidx as int);
    
    assert inode.pivots == Seq.insert(ioldnode.pivots, pivot, childidx as int);
  }


  // lemma SplitChildOfIndexPreservesDisjointReprs(oldchildren: seq<Node>, childidx: int, left: Node, right: Node)
  //   requires forall i :: 0 <= i < |oldchildren| ==> !oldchildren[i].NotInUse?
  //   requires 0 <= childidx < |oldchildren|
  //   requires !left.NotInUse?
  //   requires !right.NotInUse?
  //   requires forall i, j :: 0 <= i < j < |oldchildren| ==> oldchildren[i].repr !! oldchildren[j].repr
  //   requires left.repr !! right.repr
  //   requires left.repr <= oldchildren[childidx].repr
  //   requires forall i :: 0 <= i < |oldchildren| && i != childidx ==> right.repr !! oldchildren[i].repr
  //   ensures forall i :: 0 <= i < |Seq.replace1with2(oldchildren, left, right, childidx)| ==> !Seq.replace1with2(oldchildren, left, right, childidx)[i].NotInUse?
  //   ensures forall i, j :: 0 <= i < j < |oldchildren|+1 ==> Seq.replace1with2(oldchildren, left, right, childidx)[i].repr !! Seq.replace1with2(oldchildren, left, right, childidx)[j].repr
  // {
  //   var newchildren := Seq.replace1with2(oldchildren, left, right, childidx);
  //   forall i | 0 <= i < |newchildren|
  //     ensures !newchildren[i].NotInUse?
  //   {
  //     if i < childidx {
  //     } else if i == childidx {
  //     } else if i == childidx + 1 {
  //     } else {
  //       assert newchildren[i] == oldchildren[i-1];
  //     }
  //   }

  //   forall i: int, j: int | 0 <= i < j < |newchildren|
  //     ensures newchildren[i].repr !! newchildren[j].repr
  //   {
  //     if                           j <  childidx       {
  //     } else if                    j == childidx       {
  //     } else if i < childidx     && j == childidx+1     {
  //     } else if i == childidx    && j == childidx+1     {
  //     } else if i < childidx     &&      childidx+1 < j {
  //       assert newchildren[j] == oldchildren[j-1];
  //     } else if i == childidx    &&      childidx+1 < j {
  //       assert newchildren[j] == oldchildren[j-1];
  //     } else if i == childidx+1  &&      childidx+1 < j {
  //       assert newchildren[j] == oldchildren[j-1];
  //     } else {
  //       assert newchildren[i] == oldchildren[i-1];
  //       assert newchildren[j] == oldchildren[j-1];
  //     }
  //   }
  // }
  
  // method SplitChildOfIndexHelper(node: Node, childidx: uint64) returns (newnode: Node, ghost wit: Key)
  //   requires WFShape(node)
  //   requires BSWF(I(node))
  //   requires node.Index?
  //   requires !Full(node)
  //   requires 0 <= childidx < node.nchildren
  //   requires Full(node.children[childidx]);
  //   ensures WFShape(newnode)
  //   ensures newnode.Index?
  //   ensures fresh(newnode.repr - node.repr)
  //   ensures newnode.height == node.height
  //   ensures newnode.pivots[..newnode.nchildren-1] == Seq.insert(old(node.pivots[..node.nchildren-1]), newnode.pivots[childidx], childidx as int)
  //   ensures newnode.children[..newnode.nchildren] == Seq.replace1with2(old(node.children[..node.nchildren]), newnode.children[childidx], newnode.children[childidx+1], childidx as int)
  //   ensures old(WFShape(node.children[childidx]))
  //   ensures WFShape(newnode.children[childidx])
  //   ensures WFShape(newnode.children[childidx+1])
  //   ensures BSSplitNode(old(I(node.children[childidx])), I(newnode.children[childidx]), I(newnode.children[childidx+1]), wit, newnode.pivots[childidx])
  //   modifies node.pivots, node.children
  // {
  //   BSWFImpliesChildBSWF(I(node), childidx as int);
  //   var left, right, wit', pivot := SplitNode(node.children[childidx]);
  //   Arrays.replace1with2(node.children, node.nchildren, left, right, childidx);
  //   Arrays.Insert(node.pivots, node.nchildren-1, pivot, childidx);
  //   newnode := Index(node.repr + right.repr, node.height, node.nchildren + 1, node.pivots, node.children);
  //   wit := wit';
    
  //   ghost var oldchildren := old(node.children[..node.nchildren]);
  //   ghost var newchildren := newnode.children[..newnode.nchildren];
  //   ghost var ichildidx := childidx as int;
  //   assert newchildren == Seq.replace1with2(oldchildren, left, right, ichildidx);

  //   forall i: int, j: int | 0 <= i < j < newnode.nchildren as int
  //     ensures DisjointSubtrees(newnode, i, j)
  //   {
  //     if                            j <  ichildidx {
  //       assert old(DisjointSubtrees(node, i, j));
  //     } else if                     j == ichildidx {
  //       assert old(DisjointSubtrees(node, i, j));
  //     } else if i < ichildidx     && j == ichildidx+1 {
  //       assert old(DisjointSubtrees(node, i, j-1));
  //     } else if i == ichildidx    && j == ichildidx+1 {
  //       assert newnode.children[i] == left;
  //       assert newnode.children[j] == right;
  //     } else if i < ichildidx     &&      ichildidx+1 < j {
  //       assert old(DisjointSubtrees(node, i, j-1));
  //     } else if i == ichildidx    &&      ichildidx+1 < j {
  //       assert old(DisjointSubtrees(node, i, j-1));
  //     } else if i == ichildidx+1  &&      ichildidx+1 < j {
  //       assert old(DisjointSubtrees(node, i-1, j-1));
  //     } else {
  //       assert old(DisjointSubtrees(node, i-1, j-1));
  //     }
  //   }

  //   forall i | 0 <= i < newnode.nchildren
  //     ensures !newchildren[i].NotInUse?
  //     ensures newchildren[i].repr < newnode.repr
  //     ensures newnode.pivots !in newchildren[i].repr
  //     ensures newnode.children !in newchildren[i].repr
  //     ensures WFShape(newchildren[i])
  //   {
  //     if i < childidx {
  //       assert newchildren[i] == oldchildren[i];
  //       assert WFShape(newchildren[i]) == old(WFShape(oldchildren[i]));
  //     } else if i == childidx {
  //       assert newchildren[i] == left;
  //       assert WFShape(left);
  //     } else if i == childidx + 1 {
  //       assert newchildren[i] == right;
  //       assert WFShape(right);
  //     } else {
  //       assert newchildren[i] == oldchildren[ichildidx := left][i-1];
  //       assert WFShape(newchildren[i]) == old(WFShape(oldchildren[ichildidx := left][i-1]));
  //     }
  //   }

  //   forall o | o in newnode.repr - node.repr
  //     ensures fresh(o)
  //   {
  //     assert o in right.repr - node.repr;
  //   }

  // }
  
  // lemma SplitChildOfIndexIsBSSplitChildOfIndex(oldnode: BS.Node, newnode: BS.Node, childidx: int, wit: Key)
  //   requires BSWF(oldnode)
  //   requires oldnode.Index?
  //   requires newnode.Index?
  //   requires 0 <= childidx < |oldnode.children|
  //   requires |oldnode.pivots| == |oldnode.children|-1 // redundant, but necessary
  //   requires |newnode.children| == |oldnode.children| + 1
  //   requires |newnode.pivots| == |oldnode.pivots| + 1
  //   requires newnode.pivots == Seq.insert(oldnode.pivots, newnode.pivots[childidx], childidx)
  //   requires newnode.children == Seq.replace1with2(oldnode.children, newnode.children[childidx], newnode.children[childidx+1], childidx)
  //   requires BSSplitNode(oldnode.children[childidx], newnode.children[childidx], newnode.children[childidx+1], wit, newnode.pivots[childidx])
  //   ensures BSSplitChildOfIndex(oldnode, newnode, childidx, wit)
  // {
  //   reveal_BSWF();
  //   reveal_BSSplitNode();
  //   reveal_BSSplitChildOfIndex();
  // }
    
  // method SplitChildOfIndex(node: Node, childidx: uint64) returns (newnode: Node, ghost wit: Key)
  //   requires WFShape(node)
  //   requires BSWF(I(node))
  //   requires node.Index?
  //   requires !Full(node)
  //   requires 0 <= childidx < node.nchildren
  //   requires Full(node.children[childidx])
  //   ensures WFShape(newnode)
  //   ensures newnode.height == node.height
  //   ensures fresh(newnode.repr - node.repr)
  //   ensures BSSplitChildOfIndex(old(I(node)), I(newnode), childidx as int, wit)
  //   modifies node.pivots, node.children
  // {
  //   newnode, wit := SplitChildOfIndexHelper(node, childidx);
  //   assert newnode.children[..newnode.nchildren] == Seq.replace1with2(old(node.children[..node.nchildren]), newnode.children[childidx], newnode.children[childidx+1], childidx as int);

  //   ghost var ioldnode := old(I(node));
  //   ghost var inewnode := I(newnode);
  //   ghost var replaced := Seq.replace1with2(ioldnode.children, inewnode.children[childidx], inewnode.children[childidx+1], childidx as int);
  //   forall i | 0 <= i < |inewnode.children|
  //     ensures inewnode.children[i] == replaced[i]
  //   {
  //     if i < childidx as int {
  //     } else if i == childidx as int {
  //     } else if i == childidx as int + 1 {
  //     } else {
  //       assert newnode.children[i] == old(node.children[i-1]);
  //     }
  //   }
  //   SplitChildOfIndexIsBSSplitChildOfIndex(old(I(node)), I(newnode), childidx as int, wit);
  // }

  // method InsertLeaf(node: Node, key: Key, value: Value) returns (result: Node)
  //   requires WFShape(node)
  //   requires BSWF(I(node))
  //   requires node.Leaf?
  //   requires !Full(node)
  //   ensures WFShape(result)
  //   ensures result.repr == node.repr
  //   ensures result.Leaf?
  //   ensures BSWF(I(result))
  //   ensures BSInterpretation(I(result)) == BSInterpretation(old(I(node)))[key := value]
  //   ensures BSAllKeys(I(result)) <= old(BSAllKeys(I(node))) + {key}
  //   modifies node.keys, node.values
  // {
  //   reveal_BSWF();
  //   reveal_BSInsertLeaf();
  //   reveal_BSInterpretation();
    
  //   var posplus1: uint64 := BS.Keys.ArrayLargestLtePlus1(node.keys, 0, node.nkeys, key);
  //   if 1 <= posplus1 && node.keys[posplus1-1] == key {
  //     node.values[posplus1-1] := value;
  //     result := node;
  //   } else {
  //     Arrays.Insert(node.keys, node.nkeys, key, posplus1);
  //     Arrays.Insert(node.values, node.nkeys, value, posplus1);
  //     result := node.(nkeys := node.nkeys + 1);
  //   }
  //   assert I(result) == BSInsertLeaf(old(I(node)), key, value);
  //   reveal_BSAllKeys();
  //   BS.InsertLeafIsCorrect(old(I(node)), key, value);
  // }

  // method InsertIndexChildIsNotFullHelper(node: Node, key: Key, value: Value, childidx: uint64) returns (result: Node)
  //   requires WFShape(node)
  //   requires BSWF(I(node))
  //   requires node.Index?
  //   requires childidx as int == BSChildFor(I(node), key)
  //   requires BSWF(I(node).children[childidx])
  //   requires !Full(node.children[childidx])
  //   ensures WFShape(result)
  //   ensures result.height == node.height
  //   ensures fresh(result.repr - node.repr)
  //   ensures result.Index?
  //   ensures result.nchildren == node.nchildren
  //   ensures result.pivots == node.pivots
  //   ensures result.children == node.children
  //   ensures forall i :: 0 <= i < result.nchildren && i != childidx ==> result.children[i] == old(node.children[i])
  //   ensures BSWF(I(result.children[childidx]))
  //   ensures BSInterpretation(I(result.children[childidx])) == old(BSInterpretation(I(node).children[childidx]))[key := value]
  //   ensures BSAllKeys(I(result.children[childidx])) <= old(BSAllKeys(I(node.children[childidx]))) + {key}
  //   ensures childidx < node.nchildren-1 ==> (forall key :: key in BSAllKeys(I(result.children[childidx])) ==> BS.Keys.lt(key, node.pivots[childidx]))
  //   ensures BSWF(I(result))
  //   ensures BSInterpretation(I(result)) == BSInterpretation(old(I(node)))[key := value]
  //   modifies node.children, node.children[childidx].repr
  //   decreases node.height, 0
  // {
  //   reveal_BSWF();
  //   node.children[childidx] := InsertNode(node.children[childidx], key, value);
  //   result := node.(repr := node.repr + node.children[childidx].repr);

  //   ghost var ichildidx := childidx as int;
  //   forall i: int, j: int | 0 <= i < j < result.nchildren as int
  //     ensures DisjointSubtrees(result, i, j)
  //   {
  //     if                        j  < ichildidx {
  //       assert result.children[i] == old(node.children[i]);
  //       assert result.children[j] == old(node.children[j]);
  //       assert old(DisjointSubtrees(node, i, j));
  //       assert DisjointSubtrees(result, i, j);
  //     } else if                 j == ichildidx {
  //       assert result.children[i] == old(node.children[i]);
  //       assert old(DisjointSubtrees(node, i, j));
  //       assert DisjointSubtrees(result, i, j);
  //     } else if i  < ichildidx                 {
  //       assert result.children[i] == old(node.children[i]);
  //       assert result.children[j] == old(node.children[j]);
  //       assert old(DisjointSubtrees(node, i, j));
  //       assert DisjointSubtrees(result, i, j);
  //     } else if i == ichildidx                 {
  //       assert result.children[j] == old(node.children[j]);
  //       assert old(DisjointSubtrees(node, i, j));
  //       assert DisjointSubtrees(result, i, j);
  //     } else                                   {
  //       assert result.children[i] == old(node.children[i]);
  //       assert result.children[j] == old(node.children[j]);
  //       assert old(DisjointSubtrees(node, i, j));
  //       assert DisjointSubtrees(result, i, j);
  //     }
  //   }

  //   forall i | 0 <= i < result.nchildren
  //     ensures WFShape(result.children[i])
  //   {
  //     if i < childidx {
  //       assert old(DisjointSubtrees(node, i as int, childidx as int));
  //     } else if i == childidx {
  //     } else {
  //       assert old(DisjointSubtrees(node, childidx as int, i as int));
  //     }
  //   }
  // }

  // method InsertIndexChildIsNotFull(oldnode: Node, key: Key, value: Value, childidx: uint64) returns (result: Node)
  //   requires WFShape(oldnode)
  //   requires BSWF(I(oldnode))
  //   requires oldnode.Index?
  //   requires childidx as int == BSChildFor(I(oldnode), key)
  //   requires !Full(oldnode.children[childidx])
  //   ensures WFShape(result)
  //   ensures result.height == oldnode.height
  //   ensures fresh(result.repr - oldnode.repr)
  //   ensures BSWF(I(result))
  //   ensures BSInterpretation(I(result)) == BSInterpretation(old(I(oldnode)))[key := value]
  //   modifies oldnode.children, oldnode.children[childidx].repr
  //   decreases oldnode.height, 1
  // {
  //   ghost var node := I(oldnode);
  //   ghost var pos := childidx as int;
  //   reveal_BSWF();
  //   assert BSWF(I(oldnode).children[childidx]);

  //   result := InsertIndexChildIsNotFullHelper(oldnode, key, value, childidx);

  //   ghost var newnode := I(result);
  //   ghost var newchild := I(result.children[childidx]);
  //   reveal_BSChildFor();
  //   reveal_BSInterpretation();
  //   forall i | 0 <= i < |newnode.children|
  //     ensures newnode.children[i] == node.children[pos := newchild][i]
  //   {
  //     if i < pos {
  //       assert old(DisjointSubtrees(oldnode, i, pos));
  //     } else if i == pos {
  //     } else {
  //       assert old(DisjointSubtrees(oldnode, pos, i));
  //     }
  //   }
  //   reveal_BSAllKeys();
  //   BS.RecursiveInsertIsCorrect(node, key, value, pos, newnode, newchild);
  // }
  
  // method InsertIndex(node: Node, key: Key, value: Value) returns (result: Node)
  //   requires WFShape(node)
  //   requires BSWF(I(node))
  //   requires node.Index?
  //   requires !Full(node)
  //   // ensures WFShape(result)
  //   //ensures result.height == node.height
  //   // ensures fresh(result.repr - node.repr)
  //   //ensures BSWF(I(result))
  //   //ensures BSInterpretation(I(result)) == BSInterpretation(old(I(node)))[key := value]
  //   //ensures BSAllKeys(I(result)) <= old(BSAllKeys(I(node))) + {key}
  //   modifies node.repr
  //   decreases node.height, 2
  // {
  //   reveal_BSWF();
  //   reveal_BSSplitChildOfIndex();
  //   reveal_BSChildFor();
    
  //   var posplus1 := BS.Keys.ArrayLargestLtePlus1(node.pivots, 0, node.nchildren-1, key);
  //   if Full(node.children[posplus1]) {
  //     ghost var wit;
  //     result, wit := SplitChildOfIndex(node, posplus1);
  //     BS.SplitChildOfIndexPreservesWF(old(I(node)), I(result), posplus1 as int, wit);
  //     if BS.Keys.lte(result.pivots[posplus1], key) {
  //       posplus1 := posplus1 + 1;
  //       BS.Keys.LargestLteIsUnique2(result.pivots[..result.nchildren-1], key, posplus1 as int - 1);
  //     } else {
  //       BS.Keys.LargestLteIsUnique2(result.pivots[..result.nchildren-1], key, posplus1 as int - 1);
  //     }
  //   } else {
  //     result := node;
  //   }

  //   assert WFShape(result);
  //   assert BSWF(I(result));
  //   assert result.Index?;
  //   assert posplus1 as int == BSChildFor(I(result), key);
  //   assert !Full(result.children[posplus1]);
  //   result := InsertIndexChildIsNotFull(result, key, value, posplus1);
  // }

  // method InsertNode(node: Node, key: Key, value: Value) returns (result: Node)
  //   requires WFShape(node)
  //   requires BSWF(I(node))
  //   requires !Full(node)
  //   ensures WFShape(result)
  //   ensures result.height == node.height
  //   ensures fresh(result.repr - node.repr)
  //   ensures BSWF(I(result))
  //   ensures BSInterpretation(I(result)) == BSInterpretation(old(I(node)))[key := value]
  //   ensures BSAllKeys(I(result)) <= old(BSAllKeys(I(node))) + {key}
  //   modifies node.repr
  //   decreases node.height, 3
  // {
  //   if node.Leaf? {
  //     result := InsertLeaf(node, key, value);
  //   } else {
  //     result := InsertIndex(node, key, value);
  //   }
  // }
}

// module TestBtreeSpec refines BtreeSpec {
//   import Keys = Integer_Order
//   type Value = int
// }

// module TestMutableBtree refines MutableBtree {
//   import BS = TestBtreeSpec
    
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
