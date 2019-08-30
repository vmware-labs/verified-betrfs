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
      && node.keys != node.values
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
    requires node.Index?
    requires 0 <= from <= to <= node.nchildren as int
    reads node.repr
  {
    set i: int, o | 0 <= from <= i < to && o in node.repr && ObjectIsInSubtree(node, o, i) :: o
  }

  lemma SubReprsDisjoint(node: Node, from1: int, to1: int, from2: int, to2: int)
    requires WFShape(node)
    requires node.Index?
    requires 0 <= from1 <= to1 <= from2 <= to2 <= node.nchildren as int
    ensures SubRepr(node, from1, to1) !! SubRepr(node, from2, to2)
  {
    var subrepr1 := SubRepr(node, from1, to1);
    var subrepr2 := SubRepr(node, from2, to2);

    if o :| o in subrepr1 && o in subrepr2 {
      reveal_SubRepr();
      var i1 :| 0 <= from1 <= i1 < to1 && o in node.repr && ObjectIsInSubtree(node, o, i1);
      var i2 :| 0 <= from2 <= i2 < to2 && o in node.repr && ObjectIsInSubtree(node, o, i2);
      assert i1 < i2;
      assert DisjointSubtrees(node, i1, i2);
    }
  }
  
  lemma SubReprFits(node: Node, from: int, to: int)
    requires WFShape(node)
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
    requires node.Index?
    requires 1 < node.nchildren
    requires 0 <= newnchildren <= node.nchildren as int
    reads node.repr
  {
    Index(SubRepr(node, 0, newnchildren) + {node.pivots, node.children}, newnchildren as uint64, node.pivots, node.children)
  }

  lemma IndexPrefixPreservesWFShape(node: Node, newnchildren: int)
    requires WFShape(node)
    requires node.Index?
    requires 1 < node.nchildren
    requires 0 < newnchildren <= node.nchildren as int
    ensures WFShape(IndexPrefix(node, newnchildren))
    ensures newnchildren < node.nchildren as int ==> IndexPrefix(node, newnchildren).repr < node.repr
  {
    var pnode := IndexPrefix(node, newnchildren);
    forall i: int, j: int | 0 <= i < j < pnode.nchildren as int
      ensures DisjointSubtrees(pnode, i, j)
    {
      assert DisjointSubtrees(node, i, j);
    }
    SubReprFits(node, 0, newnchildren);
  }

  function WFShapeIndexPrefix(node: Node, newnchildren: int) : (result: Node)
    requires WFShape(node)
    requires node.Index?
    requires 1 < node.nchildren
    requires 0 < newnchildren <= node.nchildren as int
    ensures WFShape(result)
    reads node.repr
  {
    IndexPrefixPreservesWFShape(node, newnchildren);
    IndexPrefix(node, newnchildren)
  }
  
  function I(node: Node) : (result: BS.Node)
    requires WFShape(node)
    ensures node.Leaf? ==> result.Leaf?
    ensures node.Leaf? ==> result.keys == node.keys[..node.nkeys];
    ensures node.Leaf? ==> result.values == node.values[..node.nkeys];
    ensures node.Index? ==> result.Index?
    ensures node.Index? ==> result.pivots == node.pivots[..node.nchildren-1]
    ensures node.Index? ==> |result.children| == node.nchildren as int
    ensures node.Index? ==> forall i :: 0 <= i < node.nchildren ==>
           result.children[i] == I(node.children[i])
    reads node.repr
    decreases node.repr
  {
    match node {
      case Leaf(_, nkeys, keys, values) => BS.Leaf(keys[..nkeys], values[..nkeys])
      case Index(repr, nchildren, pivots, children) =>
        if nchildren == 1 then
          BS.Index([], [I(children[0])])
        else
          IndexPrefixPreservesWFShape(node, node.nchildren as int - 1);
          var imprefix := I(IndexPrefix(node, node.nchildren as int - 1));
          var imlastchild := I(children[nchildren-1]);
          BS.Index(imprefix.pivots + [pivots[nchildren-2]], imprefix.children + [imlastchild])
    }
  }

  predicate {:opaque} BSWF(node: BS.Node)
  {
    BS.WF(node)
  }

  lemma BSWFImpliesChildBSWF(node: BS.Node, childidx: int)
    requires BSWF(node)
    requires node.Index?
    requires 0 <= childidx < |node.children|
    ensures BSWF(node.children[childidx])
  {
    reveal_BSWF();
  }
  
  function {:opaque} BSSubIndex(node: BS.Node, from: int, to: int) : BS.Node
    requires BSWF(node)
    requires node.Index?
    requires 0 <= from < to <= |node.children|
  {
    reveal_BSWF();
    BS.SubIndex(node, from, to)
  }

  function {:opaque} BSInterpretation(node: BS.Node) : map<Key, Value>
    requires BSWF(node)
  {
    reveal_BSWF();
    BS.Interpretation(node)
  }
  
  function {:opaque} BSInterpretationOfChild(node: BS.Node, childidx: int) : map<Key, Value>
    requires BSWF(node)
    requires node.Index?
    requires 0 <= childidx < |node.children|
  {
    reveal_BSWF();
    BS.Interpretation(node.children[childidx])
  }

  function {:opaque} BSAllKeys(node: BS.Node) : set<Key>
  {
    BS.AllKeys(node)
  }
  
  function {:opaque} BSAllKeysOfChild(node: BS.Node, childidx: int) : set<Key>
    requires node.Index?
    requires 0 <= childidx < |node.children|
  {
    BS.AllKeys(node.children[childidx])
  }

  predicate {:opaque} BSSplitLeaf(oldleaf: BS.Node, leftleaf: BS.Node, rightleaf: BS.Node, pivot: Key)
  {
    BS.SplitLeaf(oldleaf, leftleaf, rightleaf, pivot)
  }

  predicate {:opaque} BSSplitIndex(oldleaf: BS.Node, leftleaf: BS.Node, rightleaf: BS.Node, pivot: Key)
  {
    BS.SplitIndex(oldleaf, leftleaf, rightleaf, pivot)
  }

  predicate {:opaque} BSSplitNode(oldleaf: BS.Node, leftleaf: BS.Node, rightleaf: BS.Node, pivot: Key)
  {
    BS.SplitNode(oldleaf, leftleaf, rightleaf, pivot)
  }

  predicate {:opaque} BSSplitChildOfIndex(oldindex: BS.Node, newindex: BS.Node, childidx: int)
    requires oldindex.Index?
    requires 0 <= childidx < |oldindex.children|
  {
    BS.SplitChildOfIndex(oldindex, newindex, childidx)
  }

  function {:opaque} BSInsertLeaf(leaf: BS.Node, key: Key, value: Value) : (result: BS.Node)
    requires leaf.Leaf?
    requires BSWF(leaf)
  {
    reveal_BSWF();
    BS.InsertLeaf(leaf, key, value)
  }
  
  lemma IndexPrefixIsSubIndex(node: Node, newnchildren: int)
    requires WFShape(node)
    requires BSWF(I(node))
    requires node.Index?
    requires 1 < node.nchildren
    requires 0 < newnchildren <= node.nchildren as int
    ensures I(WFShapeIndexPrefix(node, newnchildren)) == BSSubIndex(I(node), 0, newnchildren)
  {
    reveal_BSSubIndex();
  }
    
  method QueryLeaf(node: Node, needle: Key) returns (result: BS.QueryResult)
    requires WFShape(node)
    requires BSWF(I(node))
    requires node.Leaf?
    ensures needle in BSInterpretation(I(node)) ==> result == BS.Found(BSInterpretation(I(node))[needle])
    ensures needle !in BSInterpretation(I(node)) ==> result == BS.NotFound
    decreases node.repr, 0
  {
    reveal_BSWF();
    reveal_BSInterpretation();
    var posplus1: uint64 := BS.Keys.ArrayLargestLtePlus1(node.keys, 0, node.nkeys, needle);
    if 1 <= posplus1 && node.keys[posplus1-1] == needle {
      result := BS.Found(node.values[posplus1-1]);
    } else {
      result := BS.NotFound;
    }
  }

  method QueryIndex(node: Node, needle: Key) returns (result: BS.QueryResult)
    requires WFShape(node)
    requires BSWF(I(node))
    requires node.Index?
    ensures needle in BSInterpretation(I(node)) ==> result == BS.Found(BSInterpretation(I(node))[needle])
    ensures needle !in BSInterpretation(I(node)) ==> result == BS.NotFound
    decreases node.repr, 0
  {
    reveal_BSWF();
    reveal_BSInterpretation();
    reveal_BSAllKeys();
    reveal_BSAllKeysOfChild();
    reveal_BSInterpretationOfChild();
    var posplus1 := BS.Keys.ArrayLargestLtePlus1(node.pivots, 0, node.nchildren-1, needle);
    result := Query(node.children[posplus1], needle);

    if needle !in BSInterpretation(I(node)) {
      //assert needle !in BSInterpretation(I(node));
      if needle !in BSAllKeys(I(node)) {
        assert needle !in BSAllKeysOfChild(I(node), posplus1 as int);
      }
      assert needle !in BSInterpretationOfChild(I(node), posplus1 as int);
    }
  }

  method Query(node: Node, needle: Key) returns (result: BS.QueryResult)
    requires WFShape(node)
    requires BSWF(I(node))
    ensures needle in BSInterpretation(I(node)) ==> result == BS.Found(BSInterpretation(I(node))[needle])
    ensures needle !in BSInterpretation(I(node)) ==> result == BS.NotFound
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

  method SplitLeaf(node: Node) returns (left: Node, right: Node, pivot: Key)
    requires WFShape(node)
    requires BSWF(I(node))
    requires node.Leaf?
    requires Full(node)
    ensures WFShape(left)
    ensures WFShape(right)
    ensures BSSplitLeaf(I(node), I(left), I(right), pivot)
    ensures left.Leaf?
    ensures right.Leaf?
    ensures left.keys == node.keys
    ensures left.values == node.values
    ensures fresh(right.keys)
    ensures fresh(right.values)
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
    reveal_BSSplitLeaf();
  }

  method SubIndex(node: Node, from: uint64, to: uint64) returns (subnode: Node)
    requires WFShape(node)
    requires BSWF(I(node))
    requires node.Index?
    requires 1 < node.nchildren
    requires 0 <= from < to <= node.nchildren
    ensures WFShape(subnode)
    ensures subnode.Index?
    ensures I(subnode) == BSSubIndex(I(node), from as int, to as int)
    ensures subnode.repr == SubRepr(node, from as int, to as int) + {subnode.pivots, subnode.children}
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

    ghost var inode := I(node);
    ghost var isubnode := I(subnode);
    assert subnode.pivots[..subnode.nchildren-1] == node.pivots[from..to-1];
    assert isubnode.pivots == inode.pivots[from..to-1];
    assert isubnode.children == inode.children[from..to];
    reveal_BSWF();
    reveal_BSSubIndex();
  }

  
  method SplitIndex(node: Node) returns (left: Node, right: Node, pivot: Key)
    requires WFShape(node)
    requires BSWF(I(node))
    requires node.Index?
    requires Full(node)
    ensures WFShape(left)
    ensures WFShape(right)
    ensures left.Index?
    ensures right.Index?
    ensures BSSplitIndex(I(node), I(left), I(right), pivot)
    ensures left.pivots == node.pivots
    ensures left.children == node.children
    ensures fresh(right.pivots)
    ensures fresh(right.children)
    ensures left.repr !! right.repr
    ensures left.repr <= node.repr
    ensures right.repr <= node.repr + {right.pivots, right.children}
  {
    var boundary := node.nchildren/2;
    left := IndexPrefix(node, boundary as int);
    right := SubIndex(node, boundary, node.nchildren);
    pivot := node.pivots[boundary-1];

    IndexPrefixPreservesWFShape(node, boundary as int);
    IndexPrefixIsSubIndex(node, boundary as int);
    reveal_BSWF();
    BS.SubIndexPreservesWF(I(node), 0, boundary as int);
    BS.SubIndexPreservesWF(I(node), boundary as int, node.nchildren as int);
    SubReprsDisjoint(node, 0, boundary as int, boundary as int, node.nchildren as int);
    SubReprFits(node, 0, boundary as int);
    SubReprFits(node, boundary as int, node.nchildren as int);

    reveal_BSSubIndex();
    reveal_BSSplitIndex();
  }

  method SplitNode(node: Node) returns (left: Node, right: Node, pivot: Key)
    requires WFShape(node)
    requires BSWF(I(node))
    requires Full(node)
    ensures WFShape(left)
    ensures WFShape(right)
    ensures BSSplitNode(I(node), I(left), I(right), pivot)
    ensures left.repr <= node.repr
    ensures fresh(right.repr - node.repr)
    ensures left.repr !! right.repr
  {
    reveal_BSSplitNode();
    reveal_BSSplitLeaf();
    reveal_BSSplitIndex();
    if node.Leaf? {
      left, right, pivot := SplitLeaf(node);
    } else {
      left, right, pivot := SplitIndex(node);
    }
  }

  method SplitChildOfIndexHelper(node: Node, childidx: uint64) returns (newnode: Node)
    requires WFShape(node)
    requires BSWF(I(node))
    requires node.Index?
    requires !Full(node)
    requires 0 <= childidx < node.nchildren
    requires Full(node.children[childidx]);
    ensures WFShape(newnode)
    ensures fresh(newnode.repr - node.repr)
    //ensures newnode.pivots == node.pivots
    //ensures newnode.children == node.children
    //ensures BSSplitChildOfIndex(old(I(node)), newnode, childidx as int)
    ensures newnode.Index?
    ensures newnode.pivots[..newnode.nchildren-1] == Seq.insert(old(node.pivots[..node.nchildren-1]), newnode.pivots[childidx], childidx as int)
    ensures newnode.children[..newnode.nchildren] == Seq.replace1with2(old(node.children[..node.nchildren]), newnode.children[childidx], newnode.children[childidx+1], childidx as int)
    ensures old(WFShape(node.children[childidx]));
    ensures WFShape(newnode.children[childidx]);
    ensures WFShape(newnode.children[childidx+1]);
    ensures BSSplitNode(old(I(node.children[childidx])), I(newnode.children[childidx]), I(newnode.children[childidx+1]), newnode.pivots[childidx])
    modifies node.pivots, node.children
  {
    BSWFImpliesChildBSWF(I(node), childidx as int);
    var left, right, pivot := SplitNode(node.children[childidx]);
    Arrays.replace1with2(node.children, node.nchildren, left, right, childidx);
    Arrays.Insert(node.pivots, node.nchildren-1, pivot, childidx);
    newnode := Index(node.repr + right.repr, node.nchildren + 1, node.pivots, node.children);

    ghost var oldchildren := old(node.children[..node.nchildren]);
    ghost var newchildren := newnode.children[..newnode.nchildren];
    ghost var ichildidx := childidx as int;
    assert newchildren == Seq.replace1with2(oldchildren, left, right, ichildidx);

    forall i | 0 <= i < newnode.nchildren
      ensures !newchildren[i].NotInUse?
      ensures newchildren[i].repr < newnode.repr
      ensures newnode.pivots !in newchildren[i].repr
      ensures newnode.children !in newchildren[i].repr
      ensures WFShape(newchildren[i])
    {
      if i < childidx {
      } else if i == childidx {
      } else if i == childidx + 1 {
      } else {
        assert newchildren[i] == oldchildren[ichildidx := left][i-1];
      }
    }

    forall i: int, j: int | 0 <= i < j < newnode.nchildren as int
      ensures DisjointSubtrees(newnode, i, j)
    {
      if                            j <  ichildidx {
        assert old(DisjointSubtrees(node, i, j));
      } else if                     j == ichildidx {
        assert old(DisjointSubtrees(node, i, j));
      } else if i < ichildidx     && j == ichildidx+1 {
        assert old(DisjointSubtrees(node, i, j-1));
      } else if i == ichildidx    && j == ichildidx+1 {
        assert newnode.children[i] == left;
        assert newnode.children[j] == right;
      } else if i < ichildidx     &&      ichildidx+1 < j {
        assert old(DisjointSubtrees(node, i, j-1));
      } else if i == ichildidx    &&      ichildidx+1 < j {
        assert old(DisjointSubtrees(node, i, j-1));
      } else if i == ichildidx+1  &&      ichildidx+1 < j {
        assert old(DisjointSubtrees(node, i-1, j-1));
      } else {
        assert old(DisjointSubtrees(node, i-1, j-1));
      }
    }
      
    forall o | o in newnode.repr - node.repr
      ensures fresh(o)
    {
      assert o in right.repr - node.repr;
    }
  }
  
  lemma SplitChildOfIndexIsBSSplitChildOfIndex(oldnode: BS.Node, newnode: BS.Node, childidx: int)
    requires BSWF(oldnode)
    requires oldnode.Index?
    requires newnode.Index?
    requires 0 <= childidx < |oldnode.children|
    requires |oldnode.pivots| == |oldnode.children|-1 // redundant, but necessary
    requires |newnode.children| == |oldnode.children| + 1
    requires |newnode.pivots| == |oldnode.pivots| + 1
    requires newnode.pivots == Seq.insert(oldnode.pivots, newnode.pivots[childidx], childidx)
    requires newnode.children == Seq.replace1with2(oldnode.children, newnode.children[childidx], newnode.children[childidx+1], childidx)
    requires BSSplitNode(oldnode.children[childidx], newnode.children[childidx], newnode.children[childidx+1], newnode.pivots[childidx])
    ensures BSSplitChildOfIndex(oldnode, newnode, childidx)
  {
    reveal_BSWF();
    reveal_BSSplitNode();
    reveal_BSSplitChildOfIndex();
  }
    
  method SplitChildOfIndex(node: Node, childidx: uint64) returns (newnode: Node)
    requires WFShape(node)
    requires BSWF(I(node))
    requires node.Index?
    requires !Full(node)
    requires 0 <= childidx < node.nchildren
    requires Full(node.children[childidx]);
    ensures WFShape(newnode)
    ensures fresh(newnode.repr - node.repr)
    ensures BSSplitChildOfIndex(old(I(node)), I(newnode), childidx as int)
    modifies node.pivots, node.children
  {
    newnode := SplitChildOfIndexHelper(node, childidx);
    assert newnode.children[..newnode.nchildren] == Seq.replace1with2(old(node.children[..node.nchildren]), newnode.children[childidx], newnode.children[childidx+1], childidx as int);

    ghost var ioldnode := old(I(node));
    ghost var inewnode := I(newnode);
    ghost var replaced := Seq.replace1with2(ioldnode.children, inewnode.children[childidx], inewnode.children[childidx+1], childidx as int);
    forall i | 0 <= i < |inewnode.children|
      ensures inewnode.children[i] == replaced[i]
    {
      if i < childidx as int {
      } else if i == childidx as int {
      } else if i == childidx as int + 1 {
      } else {
        assert newnode.children[i] == old(node.children[i-1]);
      }
    }
    SplitChildOfIndexIsBSSplitChildOfIndex(old(I(node)), I(newnode), childidx as int);
  }

  method InsertLeaf(node: Node, key: Key, value: Value) returns (result: Node)
    requires WFShape(node)
    requires BSWF(I(node))
    requires node.Leaf?
    requires !Full(node)
    ensures WFShape(result)
    ensures result.repr == node.repr
    ensures result.Leaf?
    ensures I(result) == BSInsertLeaf(old(I(node)), key, value)
    modifies node.keys, node.values
  {
    reveal_BSWF();
    reveal_BSInsertLeaf();

    var posplus1: uint64 := BS.Keys.ArrayLargestLtePlus1(node.keys, 0, node.nkeys, key);
    if 1 <= posplus1 && node.keys[posplus1-1] == key {
      node.values[posplus1-1] := value;
      result := node;
    } else {
      Arrays.Insert(node.keys, node.nkeys, key, posplus1);
      Arrays.Insert(node.values, node.nkeys, value, posplus1);
      result := node.(nkeys := node.nkeys + 1);
    }
  }
  
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
