include "../Base/NativeTypes.s.dfy"
include "../Base/NativeArrays.s.dfy"
include "../Base/total_order.i.dfy"
include "../Base/sequences.i.dfy"
include "../Base/Arrays.i.dfy"
include "../Base/Maps.s.dfy"
include "BtreeSpec.i.dfy"

abstract module MutableBtree {
  import opened NativeTypes
  import opened NativeArrays
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
      //&& node.contents.keys != node.contents.values
      && |node.repr| == 3
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

  lemma IOfChild(node: Node, childidx: int)
    requires WFShape(node)
    requires node.contents.Index?
    requires 0 <= childidx < node.contents.nchildren as int
    ensures I(node).children[childidx] == I(node.contents.children[childidx])
  {
  }

  predicate WF(node: Node)
    reads node, node.repr
  {
    && WFShape(node)
    && BS.WF(I(node))
  }

  function Interpretation(node: Node) : map<Key, Value>
    requires WF(node)
    reads node, node.repr
  {
    BS.Interpretation(I(node))
  }  
  
  method QueryLeaf(node: Node, needle: Key) returns (result: BS.QueryResult)
    requires WF(node)
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
    requires WF(node)
    requires node.contents.Index?
    ensures needle in BS.Interpretation(I(node)) ==> result == BS.Found(BS.Interpretation(I(node))[needle])
    ensures needle !in BS.Interpretation(I(node)) ==> result == BS.NotFound
    decreases node.height, 0
  {
    var posplus1: uint64 := BS.Keys.ArrayLargestLtePlus1(node.contents.pivots, 0, node.contents.nchildren-1, needle);
    result := Query(node.contents.children[posplus1], needle);
  }

  method Query(node: Node, needle: Key) returns (result: BS.QueryResult)
    requires WF(node)
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

  method SplitLeaf(node: Node, nleft: uint64, ghost pivot: Key) returns (right: Node, ghost wit: Key)
    requires WF(node)
    requires node.contents.Leaf?
    requires 0 < nleft < node.contents.nkeys
    requires BS.Keys.lt(node.contents.keys[nleft-1], pivot)
    requires BS.Keys.lte(pivot, node.contents.keys[nleft])
    ensures WFShape(node)
    ensures WFShape(right)
    ensures node.repr == old(node.repr)
    ensures fresh(right.repr)
    ensures BS.SplitLeaf(old(I(node)), I(node), I(right), wit, pivot)
    ensures node.contents.nkeys == nleft
    modifies node
  {
    var rightkeys := newArrayFill(MaxKeysPerLeaf(), DefaultKey());
    var rightvalues := newArrayFill(MaxKeysPerLeaf(), DefaultValue());
    Arrays.Memcpy(rightkeys, 0, node.contents.keys[nleft..node.contents.nkeys]); // FIXME: remove conversion to seq
    Arrays.Memcpy(rightvalues, 0, node.contents.values[nleft..node.contents.nkeys]); // FIXME: remove conversion to seq

    right := new Node;
    right.repr := {right, rightkeys, rightvalues};
    right.height := 0;
    right.contents := Leaf(node.contents.nkeys - nleft, rightkeys, rightvalues);

    node.contents := Leaf(nleft, node.contents.keys, node.contents.values);
    wit := node.contents.keys[0];
    BS.Keys.IsStrictlySortedImpliesLt(old(node.contents.keys[..node.contents.nkeys]), nleft as int - 1, nleft as int);
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
    requires 1 <= node.contents.nchildren
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
    requires WF(node)
    requires node.contents.Index?
    requires 1 <= newnchildren
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
    requires WF(node)
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
    var subpivots := newArrayFill(MaxChildren()-1, DefaultKey());
    var subchildren := newArrayFill(MaxChildren(), null);
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
    forall i | 0 <= i < subnode.contents.nchildren
      ensures subnode.contents.children[i] in subnode.repr
    {
      assert subnode.contents.children[i] == node.contents.children[from + i];
      assert WFShape(node.contents.children[from + i]);
      assert node.contents.children[from + i] in node.contents.children[from + i].repr;
      assert node.contents.children[from + i].repr <= subnode.repr;
      assert node.contents.children[from + i] in subnode.repr;
    }
      
    ghost var isubnode := I(subnode);
    ghost var inode := I(node);
    assert isubnode.pivots == inode.pivots[from..to as int - 1];
    assert isubnode.children == inode.children[from..to];
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
    ensures BS.SplitIndex(old(I(node)), I(node), I(right), wit, pivot)
    ensures node.contents.nchildren == nleft
    ensures pivot == old(node.contents.pivots[nleft-1])
    modifies node
  {
    SubReprsDisjoint(node, 0, nleft as int, nleft as int, node.contents.nchildren as int);
    right := SubIndex(node, nleft, node.contents.nchildren);
    pivot := node.contents.pivots[nleft-1];
    assert BS.WF(I(node));
    assert BS.AllKeys(I(node).children[0]) != {};
    assert I(node).children[0] == I(node.contents.children[0]);
    assert BS.AllKeys(I(node.contents.children[0])) != {};
    wit :| wit in BS.AllKeys(I(node.contents.children[0]));
    IndexPrefix(node, nleft);
    ghost var inode := old(I(node));
    ghost var ileft := I(node);
    ghost var iright := I(right);
    assert BS.AllKeysBelowBound(inode, 0);
    BS.Keys.IsStrictlySortedImpliesLte(old(I(node)).pivots, 0, (nleft - 1) as int);
    assert BS.Keys.lt(wit, inode.pivots[0]);
    assert BS.Keys.lte(inode.pivots[0], pivot);
    assert BS.Keys.lt(wit, pivot);
    assert wit in BS.AllKeys(inode);
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
    ensures BS.SplitNode(old(I(node)), I(node), I(right), wit, pivot)
    ensures pivot in BS.AllKeys(old(I(node)))
    modifies node
  {
    if node.contents.Leaf? {
      var boundary := node.contents.nkeys/2;
      pivot := node.contents.keys[boundary];
      BS.Keys.IsStrictlySortedImpliesLt(node.contents.keys[..node.contents.nkeys], boundary as int - 1, boundary as int);
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

  twostate lemma SplitChildOfIndexPreservesDisjointSubtrees(node: Node, childidx: int)
    requires old(WFShape(node))
    requires old(node.contents).Index?
    requires old(!Full(node))
    requires 0 <= childidx < old(node.contents).nchildren as int
    requires node.contents.Index?
    requires node.contents.nchildren == old(node.contents).nchildren + 1
    requires node.contents.children.Length == old(node.contents.children.Length)
    requires forall i :: 0 <= i < node.contents.nchildren ==> node.contents.children[i] != null
    requires forall i :: 0 <= i < childidx ==> node.contents.children[i].repr == old(node.contents.children[i].repr)
    requires node.contents.children[childidx].repr <= old(node.contents.children[childidx].repr)
    requires fresh(node.contents.children[childidx+1].repr - old(node.contents.children[childidx].repr))
    requires forall i :: childidx+1 < i < node.contents.nchildren as int ==> node.contents.children[i].repr == old(node.contents.children[i-1].repr)
    requires DisjointSubtrees(node.contents, childidx, (childidx + 1));
    ensures forall i, j :: 0 <= i < j < node.contents.nchildren ==> DisjointSubtrees(node.contents, i as int, j as int)
  {
    forall i, j | 0 <= i < j < node.contents.nchildren as int
      ensures DisjointSubtrees(node.contents, i, j)
    {
      if                           j <  childidx       {
        assert old(DisjointSubtrees(node.contents, i, j));
      } else if                    j == childidx       {
        assert old(DisjointSubtrees(node.contents, i, j));
      } else if i < childidx     && j == childidx+1     {
        assert old(DisjointSubtrees(node.contents, i, j - 1));
      } else if i == childidx    && j == childidx+1     {
        assert DisjointSubtrees(node.contents, childidx, (childidx + 1));
      } else if i < childidx     &&      childidx+1 < j {
        assert old(DisjointSubtrees(node.contents, i, (j-1)));
      } else if i == childidx    &&      childidx+1 < j {
        assert old(DisjointSubtrees(node.contents, i, (j-1)));
      } else if i == childidx+1  &&      childidx+1 < j {
        assert old(DisjointSubtrees(node.contents, (i-1), (j-1)));
      } else {
        assert old(DisjointSubtrees(node.contents, (i-1), (j-1)));
      }
    }
  }

  twostate predicate SubtreeUnchanged(node: Node, oldchildidx: int, newchildidx: int)
    requires old(WFShape(node))
    requires old(node.contents).Index?
    requires node.contents.Index?
    requires node.contents.children == old(node.contents.children)
    requires 0 <= oldchildidx < old(node.contents).nchildren as int
    requires 0 <= newchildidx < node.contents.nchildren as int <= node.contents.children.Length
    reads node, node.contents.children, node.contents.children[newchildidx]
  {
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
    requires Full(node.contents.children[childidx]);
    ensures WFShape(node)
    ensures node.contents.Index?
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures BS.SplitChildOfIndex(old(I(node)), I(node), childidx as int, wit)
    ensures !Full(node.contents.children[childidx])
    ensures !Full(node.contents.children[childidx+1])
    ensures node.contents.pivots[childidx] in BS.AllKeys(old(I(node)).children[childidx])
    modifies node, node.contents.pivots, node.contents.children, node.contents.children[childidx]
  {
    ChildrenAreDistinct(node);
    
    ghost var ioldnode := I(node);
    var right, wit', pivot := SplitNode(node.contents.children[childidx]);
    ghost var ileft := I(node.contents.children[childidx]);
    ghost var iright := I(right);

    Arrays.Insert(node.contents.pivots, node.contents.nchildren-1, pivot, childidx);
    Arrays.Insert(node.contents.children, node.contents.nchildren, right, childidx + 1);
    node.contents := node.contents.(nchildren := node.contents.nchildren + 1);
    node.repr := node.repr + right.repr;
    wit := wit';

    assert node.contents.children[childidx] == old(node.contents.children[childidx]);
    SplitChildOfIndexPreservesWFShape(node, childidx as int);
    
    ghost var inode := I(node);

    ghost var target := Seq.replace1with2(ioldnode.children, inode.children[childidx], iright, childidx as int);
    forall i | 0 <= i < |inode.children|
      ensures inode.children[i] == target[i]
    {
      if i < childidx as int {
        assert old(DisjointSubtrees(node.contents, i as int, childidx as int));
        assert SubtreeUnchanged(node, i, i);
        assert inode.children[i] == ioldnode.children[i] == target[i];
      } else if i == childidx as int {
        assert inode.children[i] == ileft == target[i];
      } else if i == (childidx + 1) as int {
        assert inode.children[i] == iright == target[i];
      } else {
        assert old(DisjointSubtrees(node.contents, childidx as int, (i-1) as int));      
        assert SubtreeUnchanged(node, i-1, i);
        assert inode.children[i] == ioldnode.children[i-1] == target[i];
      }
    }
    assert inode.children == Seq.replace1with2(ioldnode.children, inode.children[childidx], iright, childidx as int);
  }

  method InsertLeaf(node: Node, key: Key, value: Value)
    requires WF(node)
    requires node.contents.Leaf?
    requires !Full(node)
    ensures WFShape(node)
    ensures node.repr == old(node.repr)
    ensures I(node) == BS.InsertLeaf(old(I(node)), key, value)
    ensures BS.WF(I(node))
    ensures BS.Interpretation(I(node)) == BS.Interpretation(old(I(node)))[key := value]
    ensures BS.AllKeys(I(node)) == BS.AllKeys(old(I(node))) + {key}
    modifies node, node.contents.keys, node.contents.values
  {
    var posplus1: uint64 := BS.Keys.ArrayLargestLtePlus1(node.contents.keys, 0, node.contents.nkeys, key);
    if 1 <= posplus1 && node.contents.keys[posplus1-1] == key {
      node.contents.values[posplus1-1] := value;
    } else {
      Arrays.Insert(node.contents.keys, node.contents.nkeys, key, posplus1);
      Arrays.Insert(node.contents.values, node.contents.nkeys, value, posplus1);
      node.contents := node.contents.(nkeys := node.contents.nkeys + 1);
    }
    BS.InsertLeafIsCorrect(old(I(node)), key, value);
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
    requires childidx as int == BS.Keys.LargestLte(node.contents.pivots[..node.contents.nchildren-1], key) + 1
    requires !Full(node.contents.children[childidx])
    ensures WFShape(node)
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures BS.WF(I(node))
    ensures BS.Interpretation(I(node)) == BS.Interpretation(old(I(node)))[key := value]
    ensures BS.AllKeys(I(node)) <= BS.AllKeys(old(I(node))) + {key}
    modifies node, node.contents.children[childidx], node.contents.children[childidx].repr
    decreases node.height, 0
  {
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
      assert old(DisjointSubtrees(node.contents, i as int, childidx as int));
    }
    forall i | childidx as int < i < |inode.children|
      ensures inode.children[i] == oldinode.children[i]
    {
      assert old(DisjointSubtrees(node.contents, childidx as int, i as int));
    }

    BS.RecursiveInsertIsCorrect(oldinode, key, value, childidx as int, inode, inode.children[childidx]);
  }

  method InsertIndexSelectAndPrepareChild(node: Node, key: Key) returns (childidx: uint64)
    requires WF(node)
    requires node.contents.Index?
    requires !Full(node)
    ensures WFShape(node)
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures BS.WF(I(node))
    ensures node.contents.Index?
    ensures childidx as int == BS.Keys.LargestLte(node.contents.pivots[..node.contents.nchildren-1], key) + 1
    ensures !Full(node.contents.children[childidx])
    ensures BS.Interpretation(I(node)) == BS.Interpretation(old(I(node)))
    ensures BS.AllKeys(I(node)) == BS.AllKeys(old(I(node)))
    modifies node, node.repr
  {
    childidx := BS.Keys.ArrayLargestLtePlus1(node.contents.pivots, 0, node.contents.nchildren-1, key);
    if Full(node.contents.children[childidx]) {
      ghost var oldpivots := node.contents.pivots[..node.contents.nchildren-1];
      var wit := SplitChildOfIndex(node, childidx);
      ghost var newpivots := node.contents.pivots[..node.contents.nchildren-1];
      BS.SplitChildOfIndexPreservesWF(old(I(node)), I(node), childidx as int, wit);
      BS.SplitChildOfIndexPreservesInterpretation(old(I(node)), I(node), childidx as int, wit);
      BS.SplitChildOfIndexPreservesAllKeys(old(I(node)), I(node), childidx as int, wit);

      var t: int32 := BS.Keys.cmp(node.contents.pivots[childidx], key);
      if  t <= 0 {
        childidx := childidx + 1;
        forall i | childidx as int - 1 < i < |newpivots|
          ensures BS.Keys.lt(key, newpivots[i])
        {
          assert newpivots[i] == oldpivots[i-1];
        }
      }
      BS.Keys.LargestLteIsUnique(node.contents.pivots[..node.contents.nchildren-1], key, childidx as int - 1);
    }
  }
  
  method InsertIndex(node: Node, key: Key, value: Value)
    requires WF(node)
    requires node.contents.Index?
    requires !Full(node)
    ensures WFShape(node)
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures BS.WF(I(node))
    ensures BS.Interpretation(I(node)) == BS.Interpretation(old(I(node)))[key := value]
    ensures BS.AllKeys(I(node)) <= BS.AllKeys(old(I(node))) + {key}
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
    ensures BS.WF(I(node))
    ensures BS.Interpretation(I(node)) == BS.Interpretation(old(I(node)))[key := value]
    ensures BS.AllKeys(I(node)) <= BS.AllKeys(old(I(node))) + {key}
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
    ensures I(newroot) == BS.Grow(I(root))
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
    assert inewroot.children == [ I(root) ];
  }

  lemma FullImpliesAllKeysNonEmpty(node: Node)
    requires WF(node)
    requires Full(node)
    ensures BS.AllKeys(I(node)) != {}
  {
    var inode := I(node);
    if inode.Leaf? {
      assert inode.keys[0] in BS.AllKeys(inode);
    } else {
      assert inode.pivots[0] in BS.AllKeys(inode);
    }
  }
  
  method Insert(root: Node, key: Key, value: Value) returns (newroot: Node)
    requires WF(root)
    ensures WF(newroot)
    ensures fresh(newroot.repr - old(root.repr))
    ensures BS.Interpretation(I(newroot)) == BS.Interpretation(old(I(root)))[key := value]
    modifies root, root.repr
  {
    if Full(root) {
      FullImpliesAllKeysNonEmpty(root);
      BS.GrowPreservesWF(I(root));
      newroot := Grow(root);
    } else {
      newroot := root;
    }
    assert BS.Interpretation(I(newroot)) == BS.Interpretation(old(I(root)));
    InsertNode(newroot, key, value);
  }

  method EmptyTree() returns (root: Node)
    ensures WF(root)
    ensures fresh(root.repr)
    ensures BS.Interpretation(I(root)) == map[]
  {
    var rootkeys := newArrayFill(MaxKeysPerLeaf(), DefaultKey());
    var rootvalues := newArrayFill(MaxKeysPerLeaf(), DefaultValue());
    root := new Node;
    root.contents := Leaf(0, rootkeys, rootvalues);
    root.repr := {root, rootkeys, rootvalues};
    root.height := 0;
  }

}

module TestBtreeSpec refines BtreeSpec {
  import opened NativeTypes
  import Keys = Uint64_Order
  type Value = uint64
}

module TestMutableBtree refines MutableBtree {
  import BS = TestBtreeSpec
    
  function method MaxKeysPerLeaf() : uint64 { 64 }
  function method MaxChildren() : uint64 { 64 }

  function method DefaultValue() : Value { 0 }
  function method DefaultKey() : Key { 0 }
}

module MainModule {
  import opened NativeTypes
  import TestMutableBtree
  
  method Main()
  {
    // var n: uint64 := 1_000_000;
    // var p: uint64 := 300_007;
    var n: uint64 := 10_000_000;
    var p: uint64 := 3_000_017;
    // var n: uint64 := 100_000_000;
    // var p: uint64 := 1_073_741_827;
    var t := TestMutableBtree.EmptyTree();
    var i: uint64 := 0;
    while i < n
      invariant 0 <= i <= n
      invariant TestMutableBtree.WFShape(t)
      invariant TestMutableBtree.BS.WF(TestMutableBtree.I(t))
      invariant fresh(t)
      invariant fresh(t.repr)
    {
      t := TestMutableBtree.Insert(t, ((i * p) % n), i);
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
