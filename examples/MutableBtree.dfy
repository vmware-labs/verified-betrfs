include "../lib/Base/NativeTypes.s.dfy"
include "../lib/Base/total_order.i.dfy"
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Arrays.i.dfy"
include "../lib/Base/Maps.s.dfy"
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

  lemma IOfChild(node: Node, childidx: int)
    requires WFShape(node)
    requires node.contents.Index?
    requires 0 <= childidx < node.contents.nchildren as int
    ensures I(node).children[childidx] == I(node.contents.children[childidx])
  {
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
    ensures node.repr == old(node.repr)
    ensures fresh(right.repr)
    ensures !Full(node)
    ensures !Full(right)
    ensures BS.SplitLeaf(old(I(node)), I(node), I(right), wit, pivot)
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
  

  method SplitIndex(node: Node) returns (right: Node, ghost wit: Key, pivot: Key)
    requires WFShape(node)
    requires BS.WF(I(node))
    requires node.contents.Index?
    requires Full(node)
    ensures WFShape(node)
    ensures WFShape(right)
    ensures node.repr <= old(node.repr)
    ensures node.repr !! right.repr
    ensures fresh(right.repr - old(node.repr))
    ensures node.height == old(node.height) == right.height
    ensures !Full(node)
    ensures !Full(right)
    ensures BS.SplitIndex(old(I(node)), I(node), I(right), wit, pivot)
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
    ensures node.repr <= old(node.repr)
    ensures fresh(right.repr - old(node.repr))
    ensures node.repr !! right.repr
    ensures !Full(node)
    ensures !Full(right)
    ensures BS.SplitNode(old(I(node)), I(node), I(right), wit, pivot)
    modifies node
  {
    if node.contents.Leaf? {
      right, wit, pivot := SplitLeaf(node);
    } else {
      right, wit, pivot := SplitIndex(node);
    }
  }

  lemma ChildrenAreDistinct(node: Node)
    requires WFShape(node)
    requires node.contents.Index?
    ensures forall i, j :: 0 <= i < j < node.contents.nchildren ==> node.contents.children[i] != node.contents.children[j]
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
    ensures !Full(node.contents.children[childidx])
    ensures !Full(node.contents.children[childidx+1])
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
        //assert node.contents.children[childidx].repr !! right.repr;
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
  }

  method InsertLeaf(node: Node, key: Key, value: Value)
    requires WFShape(node)
    requires BS.WF(I(node))
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

  method InsertIndexChildNotFull(node: Node, childidx: uint64, key: Key, value: Value)
    requires WFShape(node)
    requires BS.WF(I(node))
    requires node.contents.Index?
    requires childidx as int == BS.Keys.LargestLte(node.contents.pivots[..node.contents.nchildren-1], key) + 1
    requires !Full(node.contents.children[childidx])
    ensures WFShape(node)
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures BS.WF(I(node))
    ensures BS.Interpretation(I(node)) == BS.Interpretation(old(I(node)))[key := value]
    ensures BS.AllKeys(I(node)) == BS.AllKeys(old(I(node))) + {key}
    modifies node, node.contents.children[childidx].repr
    decreases node.height, 0
  {
    ChildrenAreDistinct(node);
    
    forall i | 0 <= i < node.contents.nchildren
      ensures old(I(node.contents.children[i])) == old(I(node).children[i])
    {
      IOfChild(node, i as int);
    }
    
    InsertNode(node.contents.children[childidx], key, value);
    node.repr := node.repr + node.contents.children[childidx].repr;

    forall i | 0 <= i < node.contents.nchildren
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
      } else {
        assert old(DisjointSubtrees(node.contents, childidx as int, i as int));
      }
    }

    forall i: uint64, j: uint64 | 0 <= i < j < node.contents.nchildren
      ensures DisjointSubtrees(node.contents, i as int, j as int)
    {
      assert old(DisjointSubtrees(node.contents, i as int, j as int));
      if i < childidx {
        assert old(DisjointSubtrees(node.contents, i as int, childidx as int));
      } else if childidx < i {
        assert old(DisjointSubtrees(node.contents, childidx as int, i as int));
      }

      if j < childidx {
        assert old(DisjointSubtrees(node.contents, j as int, childidx as int));
      } else if childidx < j {
        assert old(DisjointSubtrees(node.contents, childidx as int, j as int));
      }
    }

    ghost var oldinode := old(I(node));
    ghost var inode := I(node);

    forall i | 0 <= i < childidx as int
      ensures inode.children[i] == oldinode.children[i]
    {
      assert old(DisjointSubtrees(node.contents, i as int, childidx as int));
      assert I(node.contents.children[i]) == old(I(node.contents.children[i]));
      IOfChild(node, i);
      assert I(node.contents.children[i]) == I(node).children[i];
      assert old(I(node.contents.children[i])) == old(I(node).children[i]);
    }
    forall i | childidx as int < i < |inode.children|
      ensures inode.children[i] == oldinode.children[i]
    {
      assert old(DisjointSubtrees(node.contents, childidx as int, i as int));
      assert I(node.contents.children[i]) == old(I(node.contents.children[i]));
      IOfChild(node, i);
      assert I(node.contents.children[i]) == I(node).children[i];
      assert old(I(node.contents.children[i])) == old(I(node).children[i]);
    }
    BS.RecursiveInsertIsCorrect(oldinode, key, value, childidx as int, inode, inode.children[childidx]);
  }

  method InsertIndexSelectAndPrepareChild(node: Node, key: Key) returns (childidx: uint64)
    requires WFShape(node)
    requires BS.WF(I(node))
    requires node.contents.Index?
    requires !Full(node)
    ensures WFShape(node)
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures BS.WF(I(node))
    ensures node.contents.Index?
    ensures childidx as int == BS.Keys.LargestLte(node.contents.pivots[..node.contents.nchildren-1], key) + 1
    ensures !Full(node.contents.children[childidx])
    ensures BS.WF(I(node))
    ensures BS.Interpretation(I(node)) == BS.Interpretation(old(I(node)))
    ensures BS.AllKeys(I(node)) == BS.AllKeys(old(I(node)))
    modifies node, node.repr
  {
    childidx := BS.Keys.ArrayLargestLtePlus1(node.contents.pivots, 0, node.contents.nchildren-1, key);
    if Full(node.contents.children[childidx]) {
      ghost var oldpivots := node.contents.pivots[..node.contents.nchildren-1];
      ghost var wit := SplitChildOfIndex(node, childidx);
      ghost var newpivots := node.contents.pivots[..node.contents.nchildren-1];
      BS.SplitChildOfIndexPreservesWF(old(I(node)), I(node), childidx as int, wit);
      BS.SplitChildOfIndexPreservesInterpretation(old(I(node)), I(node), childidx as int, wit);
      BS.SplitChildOfIndexPreservesAllKeys(old(I(node)), I(node), childidx as int, wit);

      var t := BS.Keys.cmp(node.contents.pivots[childidx], key);
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
    requires WFShape(node)
    requires node.contents.Index?
    requires BS.WF(I(node))
    requires !Full(node)
    ensures WFShape(node)
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures BS.WF(I(node))
    ensures BS.Interpretation(I(node)) == BS.Interpretation(old(I(node)))[key := value]
    ensures BS.AllKeys(I(node)) == BS.AllKeys(old(I(node))) + {key}
    modifies node, node.repr
    decreases node.height, 1
  {
    var childidx := InsertIndexSelectAndPrepareChild(node, key);
    InsertIndexChildNotFull(node, childidx, key, value);
  }
  
  method InsertNode(node: Node, key: Key, value: Value)
    requires WFShape(node)
    requires BS.WF(I(node))
    requires !Full(node)
    ensures WFShape(node)
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures BS.WF(I(node))
    ensures BS.Interpretation(I(node)) == BS.Interpretation(old(I(node)))[key := value]
    ensures BS.AllKeys(I(node)) == BS.AllKeys(old(I(node))) + {key}
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
    requires WFShape(root)
    requires BS.WF(I(root))
    requires Full(root)
    ensures WFShape(newroot)
    ensures fresh(newroot.repr - root.repr)
    ensures newroot.height == root.height + 1
    ensures I(newroot) == BS.Grow(I(root))
    ensures !Full(newroot)
  {
    newroot := new Node;
    var newpivots := new Key[MaxChildren()-1](_ => DefaultKey());
    var newchildren := new Node?[MaxChildren()](_ => null);
    newchildren[0] := root;
    newroot.contents := Index(1, newpivots, newchildren);
    newroot.repr := {newroot, newpivots, newchildren} + root.repr;
    newroot.height := root.height + 1;

    ghost var inewroot := I(newroot);
    assert inewroot.children == [ I(root) ];
  }

  lemma FullImpliesAllKeysNonEmpty(node: Node)
    requires WFShape(node)
    requires BS.WF(I(node))
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
    requires WFShape(root)
    requires BS.WF(I(root))
    ensures WFShape(newroot)
    ensures BS.WF(I(newroot))
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
    ensures WFShape(root)
    ensures BS.WF(I(root))
    ensures fresh(root.repr)
    ensures BS.Interpretation(I(root)) == map[]
  {
    var rootkeys := new Key[MaxKeysPerLeaf()](_ => DefaultKey());
    var rootvalues := new Value[MaxKeysPerLeaf()](_ => DefaultValue());
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
