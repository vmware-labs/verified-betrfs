include "../Lang/NativeTypes.s.dfy"
include "../Base/NativeArrays.s.dfy"
include "../Base/total_order.i.dfy"
include "../Base/sequences.i.dfy"
include "../Base/Arrays.i.dfy"
include "../Base/Maps.s.dfy"
include "../Base/Option.s.dfy"
include "../Base/mathematics.i.dfy"
include "BtreeModel.i.dfy"

abstract module MutableBtree {
  import opened LinearSequence_s
  import opened LinearSequence_i
  import opened NativeTypes
  import opened NativeArrays
  import opened Seq = Sequences
  import opened Options
  import opened Maps
  import Math = Mathematics
  import Arrays
  import Model : BtreeModel

// TODO back turn on after transform complete
//  export API provides WF, Interpretation, EmptyTree, Insert, Query, NativeTypes, Model, Options, Maps reveals Node, Key, Value
//  export All reveals *
    
  type Key = Model.Keys.Element
  type Value = Model.Value
  type Node = Model.Node

  function method MaxKeysPerLeaf() : uint64
    ensures 2 < MaxKeysPerLeaf() as int < Uint64UpperBound() / 4

  function method MaxChildren() : uint64
    ensures 3 < MaxChildren() as int < Uint64UpperBound() / 4

  function method DefaultValue() : Value
  function method DefaultKey() : Key

  // TODO(jonh): A renaming, since now Node == Model.Node. Do it with sed later.
  predicate WF(node: Node)
    decreases node
  {
    && (Model.LseqDecreases(node); true)
    && Model.WF(node) // TODO(jonh) things are a little ackermanny with a recursion in both Model.WF and this WF
    && (node.Index? ==> (
      && 0 < |node.children| <= MaxChildren() as int
      // Recurse on children
      && (forall i :: 0 <= i < |node.children| ==> WF(node.children[i]))
      && lseq_has_all(node.children)
    ))
    && (node.Leaf? ==> (
      && 0 <= |node.keys| <= MaxKeysPerLeaf() as int
    ))
  }

  // TODO(jonh): A renaming, since now Node == Model.Node. Do it with sed later.
  function Interpretation(node: Node) : map<Key, Value>
    requires WF(node)
  {
    assert Model.WF(node);
    Model.Interpretation(node)
  }

  method Route(shared keys: seq<Key>, needle: Key) returns (posplus1: uint64)
    requires |keys| < Uint64UpperBound() / 4;
    requires Model.Keys.IsSorted(keys)
    ensures posplus1 as int == Model.Keys.LargestLte(keys, needle) + 1
  {
    var pos: int64 := Model.Keys.ComputeLargestLte(keys, needle);
    posplus1 := (pos + 1) as uint64;
  }

  method QueryLeaf(shared node: Node, needle: Key) returns (result: Option<Value>)
    requires WF(node)
    requires node.Leaf?
    ensures result == MapLookupOption(Interpretation(node), needle)
  {
    Model.reveal_Interpretation();
    assert Model.Keys.IsStrictlySorted(node.keys);
    assert Model.Keys.IsSorted(node.keys);
    var posplus1 := Route(node.keys, needle);
    if 1 <= posplus1 && seq_get(node.keys, posplus1-1) == needle {
      result := Some(seq_get(node.values, posplus1-1));
    } else {
      result := None;
    }
  }

  method QueryIndex(shared node: Node, needle: Key) returns (result: Option<Value>)
    requires WF(node)
    requires node.Index?
    ensures result == MapLookupOption(Interpretation(node), needle)
    decreases node, 0
  {
    Model.reveal_Interpretation();
    Model.reveal_AllKeys();
    var posplus1:uint64 := Route(node.pivots, needle);
    Model.LseqDecreases(node);
    result := Query(lseq_peek(node.children, posplus1), needle);
    if result.Some? {
      Model.InterpretationDelegation(node, needle);
    }
  }

  method Query(shared node: Node, needle: Key) returns (result: Option<Value>)
    requires WF(node)
    ensures result == MapLookupOption(Interpretation(node), needle)
    decreases node, 1
  {
    shared match node {
      case Leaf(_, _) => result := QueryLeaf(node, needle);
      case Index(_, _) => result := QueryIndex(node, needle);
    }
  }

  method EmptyTree() returns (linear root: Node)
    ensures WF(root)
    ensures Interpretation(root) == map[]
    ensures root.Leaf?
  {
    linear var rootkeys := seq_alloc(0);
    linear var rootvalues := seq_alloc(0);
    root := Model.Leaf(rootkeys, rootvalues);
    Model.reveal_Interpretation();
  }

//  method LeafFromSeqs(keys: seq<Key>, values: seq<Value>)
//    returns (node: Node)
//    requires |keys| == |values| <= MaxKeysPerLeaf() as int
//    ensures WFShape(node)
//    ensures node.contents.Leaf?
//    ensures fresh(node.repr)
//    ensures node.contents.keys[..node.contents.nkeys] == keys
//    ensures node.contents.values[..node.contents.nkeys] == values
//  {
//    node := EmptyTree();
//    CopySeqIntoArray(keys, 0, node.contents.keys, 0, |keys| as uint64);
//    CopySeqIntoArray(values, 0, node.contents.values, 0, |values| as uint64);
//    node.contents := node.contents.(nkeys := |keys| as uint64);
//    assert node.contents.keys[..node.contents.nkeys] == keys;
//  }
//
//  method IndexFromChildren(pivots: seq<Key>, children: seq<Node>, ghost height: nat) returns (node: Node)
//    requires 0 < |children| <= MaxChildren() as int
//    requires |pivots| == |children|-1
//    ensures node.contents.Index?
//    ensures node.contents.pivots.Length == MaxChildren() as int - 1
//    ensures node.contents.children.Length == MaxChildren() as int
//    ensures node.contents.nchildren == |children| as uint64
//    ensures node.contents.pivots[..node.contents.nchildren-1] == pivots
//    ensures node.contents.children[..node.contents.nchildren] == children
//    ensures fresh(node)
//    ensures fresh(node.contents.pivots)
//    ensures fresh(node.contents.children)
//    ensures node.repr == {node, node.contents.pivots, node.contents.children} + SeqRepr(children)
//    ensures node.height == height
//  {
//    var pivotarray := newArrayFill(MaxChildren()-1, DefaultKey());
//    var childarray := newArrayFill(MaxChildren(), null);
//    CopySeqIntoArray(pivots, 0, pivotarray, 0, |pivots| as uint64);
//    CopySeqIntoArray(children, 0, childarray, 0, |children| as uint64);
//    node := new Node;
//    node.contents := Index(|children| as uint64, pivotarray, childarray);
//    node.repr := {node, node.contents.pivots, node.contents.children} + SeqRepr(children);
//    node.height := height;
//  }

  predicate method Full(shared node: Node)
    requires WF(node)
  {
    shared match node {
      case Leaf(keys, _) => seq_length(keys) as uint64 == MaxKeysPerLeaf()
      case Index(_, children) => |children| as uint64 == MaxChildren()
    }
  }

//  method SplitLeaf(node: Node, nleft: uint64, ghost pivot: Key) returns (right: Node)
//    requires WF(node)
//    requires node.contents.Leaf?
//    requires 0 < nleft < node.contents.nkeys
//    requires Model.Keys.lt(node.contents.keys[nleft-1], pivot)
//    requires Model.Keys.lte(pivot, node.contents.keys[nleft])
//    ensures WFShape(node)
//    ensures WFShape(right)
//    ensures node.repr == old(node.repr)
//    ensures fresh(right.repr)
//    ensures Model.SplitLeaf(old(I(node)), I(node), I(right), pivot)
//    ensures node.contents.nkeys == nleft
//    modifies node
//  {
//    reveal_I();
//    Model.Keys.StrictlySortedSubsequence(node.contents.keys[..node.contents.nkeys], nleft as int, node.contents.nkeys as int);
//    assert node.contents.keys[nleft..node.contents.nkeys] == node.contents.keys[..node.contents.nkeys][nleft..node.contents.nkeys];
//    right := LeafFromSeqs(node.contents.keys[nleft..node.contents.nkeys], node.contents.values[nleft..node.contents.nkeys]);
//
//    node.contents := Leaf(nleft, node.contents.keys, node.contents.values);
//    Model.Keys.IsStrictlySortedImpliesLt(old(node.contents.keys[..node.contents.nkeys]), nleft as int - 1, nleft as int);
//  }
//
//  predicate ObjectIsInSubtree(node: Node, o: object, i: int)
//    requires WFShape(node)
//    requires node.contents.Index?
//    requires 0 <= i < node.contents.nchildren as int
//    reads node.repr
//  {
//    assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
//    o in node.contents.children[i].repr
//  }
//
//  function SubRepr(node: Node, from: int, to: int) : (result: set<object>)
//    requires WFShape(node)
//    requires node.contents.Index?
//    requires 0 <= from <= to <= node.contents.nchildren as int
//    reads node.repr
//  {
//    assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
//    assert forall i :: from <= i < to ==> node.contents.children[i] != null;
//    assert forall i :: from <= i < to ==> node.contents.children[i] in node.repr;
//    SeqRepr(node.contents.children[from..to])
//  }
//
//  predicate DisjointSubtrees(contents: NodeContents, i: int, j: int)
//    requires contents.Index?
//    requires 0 <= i < contents.nchildren as int
//    requires 0 <= j < contents.nchildren as int
//    requires contents.nchildren as int <= contents.children.Length
//    requires forall l :: 0 <= l < contents.nchildren ==> contents.children[l] != null
//    requires contents.children[j] != null
//    reads contents.children, contents.children[i], contents.children[j]
//  {
//    DisjointReprs(contents.children[..contents.nchildren], i, j)
//  }
//  
//  lemma SubReprsDisjoint(node: Node, from1: int, to1: int, from2: int, to2: int)
//    requires WFShape(node)
//    requires node.contents.Index?
//    requires 0 <= from1 <= to1 <= from2 <= to2 <= node.contents.nchildren as int
//    ensures SubRepr(node, from1, to1) !! SubRepr(node, from2, to2)
//  {
//    assert node.contents.children[..node.contents.nchildren][from1..to1]
//      == node.contents.children[from1..to1];
//    assert node.contents.children[..node.contents.nchildren][from2..to2]
//      == node.contents.children[from2..to2];
//    assert WFShapeSiblings(node.contents.children[..node.contents.nchildren]);
//    // assert forall i, j :: 0 <= i < j < node.contents.nchildren ==>
//    //     DisjointReprs(node.contents.children[..node.contents.nchildren], i as int, j as int);
//    DisjointSubSeqReprsAreDisjoint(node.contents.children[..node.contents.nchildren], from1, to1, from2, to2);
//  }
//
//  lemma SubReprUpperBound(node: Node, from: int, to: int)
//    requires WFShape(node)
//    requires node.contents.Index?
//    requires 1 < node.contents.nchildren
//    requires 0 <= from <= to <= node.contents.nchildren as int
//    ensures SubRepr(node, from, to) <= node.repr - {node, node.contents.pivots, node.contents.children}
//    ensures to - from < node.contents.nchildren as int ==> SubRepr(node, from, to) < node.repr - {node, node.contents.pivots, node.contents.children}
//  {
//    reveal_SeqRepr();
//    
//    var subrepr := SubRepr(node, from, to);
//    var nchildren := node.contents.nchildren;
//    var pivots := node.contents.pivots;
//    var children := node.contents.children;
//
//    forall o | o in subrepr
//      ensures o in node.repr
//    {
//      var i :| from <= i < to && o in node.contents.children[i].repr;
//    }
//    assert subrepr <= node.repr;
//    assert pivots !in subrepr;
//    assert children !in subrepr;
//    assert subrepr <= node.repr - {node, pivots, children};
//    
//    if to - from < nchildren as int {
//      assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
//      assert WFShape(children[0]);
//      assert WFShape(children[nchildren-1]);
//      assert children[0].repr < node.repr;
//      assert children[0].repr != {};
//      assert children[nchildren-1].repr < node.repr;
//      assert children[nchildren-1].repr != {};
//      if 0 < from {
//        forall o | o in subrepr
//          ensures o !in children[0].repr
//        {
//          if o == pivots {
//          } else if o == children {
//          } else {
//            var i :| from <= i < to && o in node.repr && o in node.contents.children[i].repr; 
//            assert DisjointSubtrees(node.contents, 0, i);
//          }
//        }
//        assert subrepr < node.repr - {node, pivots, children};
//      } else {
//        assert to < nchildren as int;
//        forall o | o in subrepr
//          ensures o !in children[nchildren - 1].repr
//        {
//          if o == pivots {
//          } else if o == children {
//          } else {
//            var i :| from <= i < to && o in node.repr && o in node.contents.children[i].repr; 
//            assert DisjointSubtrees(node.contents, i, nchildren as int - 1);
//          }
//        }
//        var wit :| wit in children[nchildren-1].repr;
//        assert wit !in subrepr;
//        assert subrepr < node.repr - {node, pivots, children};
//      }
//    }
//  }
//
//  lemma SubReprLowerBound(node: Node, from: int, to: int)
//    requires WFShape(node)
//    requires node.contents.Index?
//    requires 1 <= node.contents.nchildren
//    requires 0 <= from <= to <= node.contents.nchildren as int
//    ensures forall i :: from <= i < to ==> node.contents.children[i] != null
//    ensures forall i :: from <= i < to ==> node.contents.children[i].repr <= SubRepr(node, from, to)
//  {
//    reveal_SeqRepr();
//    
//    var subrepr := SubRepr(node, from, to);
//    var nchildren := node.contents.nchildren;
//    var pivots := node.contents.pivots;
//    var children := node.contents.children;
//    
//    forall o | o in subrepr
//      ensures o in node.repr
//    {
//      var i :| from <= i < to && o in node.contents.children[i].repr;
//    }
//    assert subrepr <= node.repr;
//    assert pivots !in subrepr;
//    assert children !in subrepr;
//    assert subrepr <= node.repr - {node, pivots, children};
//    
//    forall i | from <= i < to
//      ensures children[i].repr <= subrepr
//    {
//      forall o | o in children[i].repr
//        ensures o in subrepr
//      {
//        assert ObjectIsInSubtree(node, o, i);
//      }
//    }
//  }
//
//  
//  method IndexPrefix(node: Node, newnchildren: uint64)
//    requires WF(node)
//    requires node.contents.Index?
//    requires 1 <= newnchildren
//    requires 0 <= newnchildren <= node.contents.nchildren
//    ensures WFShape(node)
//    ensures node.repr == old({node, node.contents.pivots, node.contents.children} + SubRepr(node, 0, newnchildren as int))
//    ensures node.height == old(node.height)
//    ensures I(node) == Model.SubIndex(old(I(node)), 0, newnchildren as int)
//    modifies node
//  {
//    assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
//    ghost var oldinode := I(node);
//    SubReprLowerBound(node, 0, newnchildren as int);
//
//    node.repr := {node, node.contents.pivots, node.contents.children} + SubRepr(node, 0, newnchildren as int);
//    node.contents := node.contents.(nchildren := newnchildren);
//
//    ghost var newchildren := node.contents.children[..newnchildren];
//    assert forall i :: 0 <= i < newnchildren ==> WFShape(newchildren[i]);
//    assert newchildren == old(node.contents.children[..node.contents.nchildren])[..newnchildren];
//    forall i, j | 0 <= i < j < |newchildren|
//      ensures DisjointReprs(newchildren, i, j)
//    {
//      assert old(DisjointReprs(node.contents.children[..node.contents.nchildren], i, j));
//    }
//    assert WFShape(node);
//    ghost var newinode := I(node);
//    reveal_I();
//    assert newinode == Model.SubIndex(oldinode, 0, newnchildren as int);
//  }
//
//  method SubIndex(node: Node, from: uint64, to: uint64) returns (subnode: Node)
//    requires WF(node)
//    requires node.contents.Index?
//    requires 1 < node.contents.nchildren
//    requires 0 <= from < to <= node.contents.nchildren
//    ensures WFShape(subnode)
//    ensures subnode.contents.Index?
//    ensures subnode.repr == SubRepr(node, from as int, to as int) + {subnode, subnode.contents.pivots, subnode.contents.children}
//    ensures subnode.height == node.height
//    ensures I(subnode) == Model.SubIndex(I(node), from as int, to as int)
//    ensures fresh(subnode)
//    ensures fresh(subnode.contents.pivots)
//    ensures fresh(subnode.contents.children)
//  {
//    assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
//
//    subnode := IndexFromChildren(node.contents.pivots[from..to-1], node.contents.children[from..to], node.height);
//
//    ghost var newchildren := subnode.contents.children[..subnode.contents.nchildren];
//    assert forall i :: 0 <= i < |newchildren| ==> WFShape(newchildren[i]);
//    forall i, j | 0 <= i < j < |newchildren|
//      ensures DisjointReprs(newchildren, i, j)
//    {
//      assert DisjointSubtrees(node.contents, from as int + i, from as int + j);
//    }
//    assert WFShapeSiblings(newchildren);
//    assert WFShapeChildren(newchildren, subnode.repr, subnode.height);
//
//    reveal_I();
//    assert node.contents.pivots[from..to-1] == I(node).pivots[from..to-1];
//    assume I(subnode) == Model.SubIndex(I(node), from as int, to as int);
//  }
//
//  method SplitIndex(node: Node, nleft: uint64) returns (right: Node, pivot: Key)
//    requires WF(node)
//    requires node.contents.Index?
//    requires 2 <= node.contents.nchildren
//    requires 0 < nleft < node.contents.nchildren
//    ensures WFShape(node)
//    ensures WFShape(right)
//    ensures node.repr <= old(node.repr)
//    ensures node.repr !! right.repr
//    ensures fresh(right.repr - old(node.repr))
//    ensures node.height == old(node.height) == right.height
//    ensures Model.SplitIndex(old(I(node)), I(node), I(right), pivot)
//    ensures node.contents.nchildren == nleft
//    ensures pivot == old(node.contents.pivots[nleft-1])
//    modifies node
//  {
//    SubReprsDisjoint(node, 0, nleft as int, nleft as int, node.contents.nchildren as int);
//    SubReprUpperBound(node, 0, nleft as int);
//    SubReprUpperBound(node, nleft as int, node.contents.nchildren as int);
//    assert Model.AllKeysBelowBound(I(node), nleft as int - 1);
//    assert Model.AllKeysAboveBound(I(node), nleft as int);
//    right := SubIndex(node, nleft, node.contents.nchildren);
//    pivot := node.contents.pivots[nleft-1];
//    IOfChild(node, 0);
//    IndexPrefix(node, nleft);
//    ghost var inode := old(I(node));
//    ghost var iright := I(right);
//    assert Model.AllKeysBelowBound(inode, 0);
//    assert iright.children[0] == inode.children[nleft];
//    Model.Keys.IsStrictlySortedImpliesLte(old(I(node)).pivots, 0, (nleft - 1) as int);
//    reveal_I();
//  }
//
//  method SplitNode(node: Node) returns (right: Node, pivot: Key)
//    requires WF(node)
//    requires Full(node)
//    ensures WFShape(node)
//    ensures WFShape(right)
//    ensures node.height == old(node.height)
//    ensures right.height == old(node.height)
//    ensures node.repr <= old(node.repr)
//    ensures fresh(right.repr - old(node.repr))
//    ensures node.repr !! right.repr
//    ensures !Full(node)
//    ensures !Full(right)
//    ensures Model.SplitNode(old(I(node)), I(node), I(right), pivot)
//    ensures pivot in Model.AllKeys(old(I(node)))
//    modifies node
//  {
//    if node.contents.Leaf? {
//      var boundary := node.contents.nkeys/2;
//      pivot := node.contents.keys[boundary];
//      Model.Keys.IsStrictlySortedImpliesLt(node.contents.keys[..node.contents.nkeys], boundary as int - 1, boundary as int);
//      right := SplitLeaf(node, node.contents.nkeys / 2, pivot);
//    } else {
//      var boundary := node.contents.nchildren/2;
//      right, pivot := SplitIndex(node, boundary);
//    }
//    Model.reveal_AllKeys();
//  }
//
//  // twostate lemma SplitChildOfIndexPreservesDisjointSubtrees(node: Node, childidx: int)
//  //   requires old(WFShape(node))
//  //   requires old(node.contents).Index?
//  //   requires old(!Full(node))
//  //   requires 0 <= childidx < old(node.contents).nchildren as int
//  //   requires node.contents.Index?
//  //   requires node.contents.nchildren == old(node.contents).nchildren + 1
//  //   requires node.contents.children.Length == old(node.contents.children.Length)
//  //   requires forall i :: 0 <= i < node.contents.nchildren ==> node.contents.children[i] != null
//  //   requires forall i :: 0 <= i < childidx ==> node.contents.children[i].repr == old(node.contents.children[i].repr)
//  //   requires node.contents.children[childidx].repr <= old(node.contents.children[childidx].repr)
//  //   requires fresh(node.contents.children[childidx+1].repr - old(node.contents.children[childidx].repr))
//  //   requires forall i :: childidx+1 < i < node.contents.nchildren as int ==> node.contents.children[i].repr == old(node.contents.children[i-1].repr)
//  //   requires DisjointSubtrees(node.contents, childidx, (childidx + 1));
//  //   ensures forall i, j :: 0 <= i < j < node.contents.nchildren ==> DisjointSubtrees(node.contents, i as int, j as int)
//  // {
//  //   forall i, j | 0 <= i < j < node.contents.nchildren as int
//  //     ensures DisjointSubtrees(node.contents, i, j)
//  //   {
//  //     if                           j <  childidx       {
//  //       assert old(DisjointSubtrees(node.contents, i, j));
//  //     } else if                    j == childidx       {
//  //       assert old(DisjointSubtrees(node.contents, i, j));
//  //     } else if i < childidx     && j == childidx+1     {
//  //       assert old(DisjointSubtrees(node.contents, i, j - 1));
//  //     } else if i == childidx    && j == childidx+1     {
//  //       assert DisjointSubtrees(node.contents, childidx, (childidx + 1));
//  //     } else if i < childidx     &&      childidx+1 < j {
//  //       assert old(DisjointSubtrees(node.contents, i, (j-1)));
//  //     } else if i == childidx    &&      childidx+1 < j {
//  //       assert old(DisjointSubtrees(node.contents, i, (j-1)));
//  //     } else if i == childidx+1  &&      childidx+1 < j {
//  //       assert old(DisjointSubtrees(node.contents, (i-1), (j-1)));
//  //     } else {
//  //       assert old(DisjointSubtrees(node.contents, (i-1), (j-1)));
//  //     }
//  //   }
//  // }
//
//  twostate lemma SplitChildOfIndexPreservesWFShape(node: Node, childidx: int)
//    requires old(WFShape(node))
//    requires old(node.contents).Index?
//    requires old(!Full(node))
//    requires 0 <= childidx < old(node.contents).nchildren as int
//    requires node.contents.Index?
//    requires node.contents.nchildren == old(node.contents).nchildren + 1
//    requires node.contents.children == old(node.contents.children)
//    requires node.contents.pivots == old(node.contents.pivots)
//    requires node.height == old(node.height)
//    requires unchanged(old(node.repr) - {node, node.contents.pivots, node.contents.children, node.contents.children[childidx]})
//    requires forall i :: 0 <= i < childidx ==> node.contents.children[i] == old(node.contents.children[i])
//    requires forall i :: childidx + 1 < i < node.contents.nchildren as int ==> node.contents.children[i] == old(node.contents.children[i-1])
//    requires old(node.contents.children[childidx]) != null
//    requires node.contents.children[childidx] != null
//    requires WFShape(node.contents.children[childidx])
//    requires node.contents.children[childidx].repr <= old(node.contents.children[childidx].repr)
//    requires node.contents.children[childidx].height == old(node.contents.children[childidx].height)
//    requires node.contents.children[childidx+1] != null
//    requires WFShape(node.contents.children[childidx+1])
//    requires fresh(node.contents.children[childidx+1].repr - old(node.contents.children[childidx].repr))
//    requires node.contents.children[childidx+1].height == old(node.contents.children[childidx].height)
//    requires DisjointSubtrees(node.contents, childidx, (childidx + 1))
//    requires node.repr == old(node.repr) + node.contents.children[childidx+1].repr
//    ensures WFShape(node)
//  {
//    assert old(WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height));
//
//    var newchildren := node.contents.children[..node.contents.nchildren];
//    
//    forall i | 0 <= i < node.contents.nchildren as int
//      ensures newchildren[i] != null
//      ensures newchildren[i] in node.repr
//      ensures newchildren[i].repr < node.repr
//      ensures node !in newchildren[i].repr
//      ensures node.contents.pivots !in newchildren[i].repr
//      ensures node.contents.children !in newchildren[i].repr
//      ensures newchildren[i].height < node.height
//      ensures WFShape(newchildren[i])
//    {
//      if i < childidx {
//        assert old(DisjointSubtrees(node.contents, i, childidx));
//      } else if i == childidx {
//      } else if i == childidx + 1 {
//      } else {
//        assert old(DisjointSubtrees(node.contents, childidx, i-1));
//      }
//    }
//    SeqReprSubsetExtensionality(newchildren, node.repr);
//      
//    forall i, j | 0 <= i < j < node.contents.nchildren as int
//      ensures DisjointReprs(newchildren, i, j)
//    {
//      if                           j <  childidx       {
//        assert old(DisjointSubtrees(node.contents, i, childidx));
//        assert old(DisjointSubtrees(node.contents, j, childidx));
//        assert old(DisjointSubtrees(node.contents, i, j));
//        assert old(WFShape(node.contents.children[i]));
//        assert old(WFShape(node.contents.children[j]));
//      } else if                    j == childidx       {
//        assert old(DisjointSubtrees(node.contents, i, childidx));
//        assert old(DisjointSubtrees(node.contents, i, j));
//        assert old(WFShape(node.contents.children[i]));
//      } else if i < childidx     && j == childidx+1     {
//        assert old(DisjointSubtrees(node.contents, i, childidx));
//        assert old(DisjointSubtrees(node.contents, i, j - 1));
//        assert old(WFShape(node.contents.children[i]));
//      } else if i == childidx    && j == childidx+1     {
//      } else if i < childidx     &&      childidx+1 < j {
//        assert old(DisjointSubtrees(node.contents, i, childidx));
//        assert old(DisjointSubtrees(node.contents, childidx, (j-1)));
//        assert old(DisjointSubtrees(node.contents, i, (j-1)));
//        assert old(WFShape(node.contents.children[i]));
//        assert old(WFShape(node.contents.children[j-1]));
//      } else if i == childidx    &&      childidx+1 < j {
//        assert old(DisjointSubtrees(node.contents, childidx, (j-1)));
//        assert old(DisjointSubtrees(node.contents, i, (j-1)));
//        assert old(WFShape(node.contents.children[j-1]));
//      } else if i == childidx+1  &&      childidx+1 < j {
//        assert old(DisjointSubtrees(node.contents, childidx, (j-1)));
//        assert old(DisjointSubtrees(node.contents, (i-1), (j-1)));
//        assert old(WFShape(node.contents.children[j-1]));
//      } else {
//        assert old(DisjointSubtrees(node.contents, childidx, (i-1)));
//        assert old(DisjointSubtrees(node.contents, childidx, (j-1)));
//        assert old(DisjointSubtrees(node.contents, (i-1), (j-1)));
//        assert old(WFShape(node.contents.children[i-1]));
//        assert old(WFShape(node.contents.children[j-1]));
//      }
//    }
//
//    assert WFShapeChildren(newchildren, node.repr, node.height);
//  }
//  
//  method SplitChildOfIndex(node: Node, childidx: uint64)
//    requires WF(node)
//    requires node.contents.Index?
//    requires !Full(node)
//    requires 0 <= childidx < node.contents.nchildren
//    requires node.contents.children[childidx] != null
//    requires Full(node.contents.children[childidx]);
//    ensures WFShape(node)
//    ensures node.contents.Index?
//    ensures fresh(node.repr - old(node.repr))
//    ensures node.height == old(node.height)
//    ensures Model.SplitChildOfIndex(old(I(node)), I(node), childidx as int)
//    ensures node.contents.children[childidx] != null
//    ensures node.contents.children[childidx+1] != null
//    ensures !Full(node.contents.children[childidx])
//    ensures !Full(node.contents.children[childidx+1])
//    ensures node.contents.pivots[childidx] in Model.AllKeys(old(I(node)).children[childidx])
//    modifies node, node.contents.pivots, node.contents.children, node.contents.children[childidx]
//  {
//    assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
//    
//    forall i | 0 <= i < node.contents.nchildren
//      ensures I(node).children[i] == I(node.contents.children[i])
//    {
//      IOfChild(node, i as int);
//    }
//    
//    var right, pivot := SplitNode(node.contents.children[childidx]);
//    Arrays.Insert(node.contents.pivots, node.contents.nchildren-1, pivot, childidx);
//    Arrays.Insert(node.contents.children, node.contents.nchildren, right, childidx + 1);
//    node.contents := node.contents.(nchildren := node.contents.nchildren + 1);
//    node.repr := node.repr + right.repr;
//
//    SplitChildOfIndexPreservesWFShape(node, childidx as int);
//    
//    ghost var ioldnode := old(I(node));
//    ghost var inode := I(node);
//    ghost var iright := I(right);
//    ghost var target := Seq.replace1with2(ioldnode.children, inode.children[childidx], iright, childidx as int);
//    forall i | 0 <= i < |inode.children|
//      ensures inode.children[i] == target[i]
//    {
//      IOfChild(node, i);
//      if i < childidx as int {
//        assert old(DisjointSubtrees(node.contents, i as int, childidx as int));
//      } else if i == childidx as int {
//      } else if i == (childidx + 1) as int {
//      } else {
//        assert old(DisjointSubtrees(node.contents, childidx as int, (i-1) as int));      
//      }
//    }
//
//    IOfChild(node, childidx as int);
//    IOfChild(node, childidx as int + 1);
//  }
//
//  method InsertLeaf(node: Node, key: Key, value: Value) returns (oldvalue: Option<Value>)
//    requires WF(node)
//    requires node.contents.Leaf?
//    requires !Full(node)
//    ensures WFShape(node)
//    ensures node.repr == old(node.repr)
//    ensures I(node) == Model.InsertLeaf(old(I(node)), key, value)
//    ensures Model.WF(I(node))
//    ensures Model.Interpretation(I(node)) == Model.Interpretation(old(I(node)))[key := value]
//    ensures Model.AllKeys(I(node)) == Model.AllKeys(old(I(node))) + {key}
//    ensures oldvalue == MapLookupOption(old(Interpretation(node)), key);
//    modifies node, node.contents.keys, node.contents.values
//  {
//    reveal_I();
//    Model.reveal_Interpretation();
//    Model.reveal_AllKeys();
//    var posplus1: uint64 := Model.Keys.ArrayLargestLtePlus1(node.contents.keys, 0, node.contents.nkeys, key);
//    if 1 <= posplus1 && node.contents.keys[posplus1-1] == key {
//      oldvalue := Some(node.contents.values[posplus1-1]);
//      node.contents.values[posplus1-1] := value;
//    } else {
//      oldvalue := None;
//      Arrays.Insert(node.contents.keys, node.contents.nkeys, key, posplus1);
//      Arrays.Insert(node.contents.values, node.contents.nkeys, value, posplus1);
//      node.contents := node.contents.(nkeys := node.contents.nkeys + 1);
//    }
//    Model.InsertLeafIsCorrect(old(I(node)), key, value);
//  }
//
//  twostate lemma InsertIndexChildNotFullPreservesWFShape(node: Node, childidx: int)
//    requires old(WFShape(node))
//    requires old(node.contents).Index?
//    requires 0 <= childidx < old(node.contents).nchildren as int
//    requires node.contents.Index?
//    requires node.contents.nchildren == old(node.contents).nchildren
//    requires node.contents.children == old(node.contents.children)
//    requires node.contents.pivots == old(node.contents.pivots)
//    requires node.height == old(node.height)
//    requires old(node.contents.children[childidx]) != null
//    requires node.contents.children[childidx] != null
//    requires unchanged(old(node.repr) - ({node} + old(node.contents.children[childidx].repr)))
//    requires forall i :: 0 <= i < childidx ==> node.contents.children[i] == old(node.contents.children[i])
//    requires forall i :: childidx < i < node.contents.nchildren as int ==> node.contents.children[i] == old(node.contents.children[i])
//    requires WFShape(node.contents.children[childidx])
//    requires node.contents.children[childidx].height == old(node.contents.children[childidx].height)
//    requires fresh(node.contents.children[childidx].repr - old(node.contents.children[childidx].repr))
//    requires node.repr == old(node.repr) + node.contents.children[childidx].repr
//    ensures WFShape(node)
//  {
//    assert old(WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height));
//    assert forall i :: 0 <= i < node.contents.nchildren ==> old(WFShape(node.contents.children[i]));
//    
//    forall i | 0 <= i < node.contents.nchildren as int
//      ensures node.contents.children[i] != null
//      ensures node.contents.children[i] in node.repr
//      ensures node.contents.children[i].repr < node.repr
//      ensures node !in node.contents.children[i].repr
//      ensures node.contents.pivots !in node.contents.children[i].repr
//      ensures node.contents.children !in node.contents.children[i].repr
//      ensures node.contents.children[i].height < node.height
//      ensures WFShape(node.contents.children[i])
//    {
//      if i < childidx {
//        assert old(DisjointSubtrees(node.contents, i, childidx));
//      } else if i == childidx {
//      } else {
//        assert old(DisjointSubtrees(node.contents, childidx, i));
//      }
//    }
//    SeqReprSubsetExtensionality(node.contents.children[..node.contents.nchildren], node.repr);
//      
//    forall i, j | 0 <= i < j < node.contents.nchildren as int
//      ensures DisjointReprs(node.contents.children[..node.contents.nchildren], i,j)
//    {
//      assert old(DisjointSubtrees(node.contents, i, j));
//      if                           j <  childidx       {
//        assert old(DisjointSubtrees(node.contents, i, childidx));
//        assert old(DisjointSubtrees(node.contents, j, childidx));
//      } else if                    j == childidx       {
//        assert old(DisjointSubtrees(node.contents, i, childidx));
//      } else if i < childidx     &&      childidx < j {
//        assert old(DisjointSubtrees(node.contents, i, childidx));
//        assert old(DisjointSubtrees(node.contents, childidx, j));
//      } else if i == childidx    &&      childidx < j {
//        assert old(DisjointSubtrees(node.contents, childidx, j));
//      } else {
//        assert old(DisjointSubtrees(node.contents, childidx, i));
//        assert old(DisjointSubtrees(node.contents, childidx, j));
//      }
//    }
//  }
//
//  method InsertIndexChildNotFull(node: Node, childidx: uint64, key: Key, value: Value)
//    returns (oldvalue: Option<Value>)
//    requires WF(node)
//    requires node.contents.Index?
//    requires childidx as int == Model.Keys.LargestLte(node.contents.pivots[..node.contents.nchildren-1], key) + 1
//    requires node.contents.children[childidx] != null
//    requires !Full(node.contents.children[childidx])
//    ensures WFShape(node)
//    ensures fresh(node.repr - old(node.repr))
//    ensures node.height == old(node.height)
//    ensures Model.WF(I(node))
//    ensures Model.Interpretation(I(node)) == Model.Interpretation(old(I(node)))[key := value]
//    ensures Model.AllKeys(I(node)) <= Model.AllKeys(old(I(node))) + {key}
//    ensures oldvalue == MapLookupOption(old(Interpretation(node)), key)
//    modifies node, node.contents.children[childidx], node.contents.children[childidx].repr
//    decreases node.height, 0
//  {
//    assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
//
//    forall i | 0 <= i < node.contents.nchildren
//      ensures I(node.contents.children[i]) == I(node).children[i]
//    {
//      IOfChild(node, i as int);
//    }
//    
//    oldvalue := InsertNode(node.contents.children[childidx], key, value);
//    assert oldvalue == MapLookupOption(old(Interpretation(node)), key) by {
//      reveal_I();
//      Model.reveal_Interpretation();
//      Model.reveal_AllKeys();
//    }
//    node.repr := node.repr + node.contents.children[childidx].repr;
//    
//    InsertIndexChildNotFullPreservesWFShape(node, childidx as int);
//    
//    ghost var oldinode := old(I(node));
//    ghost var inode := I(node);
//    ghost var oldchild := oldinode.children[childidx];
//    ghost var newchild := inode.children[childidx];
//
//    forall i | 0 <= i < childidx as int
//      ensures inode.children[i] == oldinode.children[i]
//    {
//      IOfChild(node, i);
//      assert old(DisjointSubtrees(node.contents, i, childidx as int));
//    }
//    forall i | childidx as int < i < |inode.children|
//      ensures inode.children[i] == oldinode.children[i]
//    {
//      IOfChild(node, i);
//      assert old(DisjointSubtrees(node.contents, childidx as int, i));
//    }
//
//    IOfChild(node, childidx as int);
//    Model.RecursiveInsertIsCorrect(oldinode, key, value, childidx as int, inode, inode.children[childidx]);
//  }
//
//  method InsertIndexSelectAndPrepareChild(node: Node, key: Key) returns (childidx: uint64)
//    requires WF(node)
//    requires node.contents.Index?
//    requires !Full(node)
//    ensures WFShape(node)
//    ensures fresh(node.repr - old(node.repr))
//    ensures node.height == old(node.height)
//    ensures Model.WF(I(node))
//    ensures node.contents.Index?
//    ensures childidx as int == Model.Keys.LargestLte(node.contents.pivots[..node.contents.nchildren-1], key) + 1
//    ensures node.contents.children[childidx] != null
//    ensures !Full(node.contents.children[childidx])
//    ensures Model.Interpretation(I(node)) == Model.Interpretation(old(I(node)))
//    ensures Model.AllKeys(I(node)) == Model.AllKeys(old(I(node)))
//    modifies node, node.repr
//  {
//    Model.reveal_AllKeys();
//    assert WFShapeChildren(node.contents.children[..node.contents.nchildren], node.repr, node.height);
//
//    childidx := Model.Keys.ArrayLargestLtePlus1(node.contents.pivots, 0, node.contents.nchildren-1, key);
//    if Full(node.contents.children[childidx]) {
//      ghost var oldpivots := node.contents.pivots[..node.contents.nchildren-1];
//      SplitChildOfIndex(node, childidx);
//      ghost var newpivots := node.contents.pivots[..node.contents.nchildren-1];
//      Model.SplitChildOfIndexPreservesWF(old(I(node)), I(node), childidx as int);
//      Model.SplitChildOfIndexPreservesInterpretation(old(I(node)), I(node), childidx as int);
//      Model.SplitChildOfIndexPreservesAllKeys(old(I(node)), I(node), childidx as int);
//
//      var t: int32 := Model.Keys.cmp(node.contents.pivots[childidx], key);
//      if  t <= 0 {
//        childidx := childidx + 1;
//        forall i | childidx as int - 1 < i < |newpivots|
//          ensures Model.Keys.lt(key, newpivots[i])
//        {
//          assert newpivots[i] == oldpivots[i-1];
//        }
//      }
//      Model.Keys.LargestLteIsUnique(node.contents.pivots[..node.contents.nchildren-1], key, childidx as int - 1);
//    }
//  }
//  
//  method InsertIndex(node: Node, key: Key, value: Value) returns (oldvalue: Option<Value>)
//    requires WF(node)
//    requires node.contents.Index?
//    requires !Full(node)
//    ensures WFShape(node)
//    ensures fresh(node.repr - old(node.repr))
//    ensures node.height == old(node.height)
//    ensures Model.WF(I(node))
//    ensures Model.Interpretation(I(node)) == Model.Interpretation(old(I(node)))[key := value]
//    ensures Model.AllKeys(I(node)) <= Model.AllKeys(old(I(node))) + {key}
//    ensures oldvalue == MapLookupOption(old(Interpretation(node)), key)
//    modifies node, node.repr
//    decreases node.height, 1
//  {
//    var childidx: uint64 := InsertIndexSelectAndPrepareChild(node, key);
//    oldvalue := InsertIndexChildNotFull(node, childidx, key, value);
//  }
//  
//  method InsertNode(node: Node, key: Key, value: Value) returns (oldvalue: Option<Value>)
//    requires WF(node)
//    requires !Full(node)
//    ensures WFShape(node)
//    ensures fresh(node.repr - old(node.repr))
//    ensures node.height == old(node.height)
//    ensures Model.WF(I(node))
//    ensures Model.Interpretation(I(node)) == Model.Interpretation(old(I(node)))[key := value]
//    ensures Model.AllKeys(I(node)) <= Model.AllKeys(old(I(node))) + {key}
//    ensures oldvalue == MapLookupOption(old(Interpretation(node)), key)
//    modifies node, node.repr
//    decreases node.height, 2
//  {
//    if node.contents.Leaf? {
//      oldvalue := InsertLeaf(node, key, value);
//    } else {
//      oldvalue := InsertIndex(node, key, value);
//    }
//  }
//
//  method Grow(root: Node) returns (newroot: Node)
//    requires WF(root)
//    requires Full(root)
//    ensures WFShape(newroot)
//    ensures fresh(newroot.repr - root.repr)
//    ensures newroot.height == root.height + 1
//    ensures I(newroot) == Model.Grow(I(root))
//    ensures !Full(newroot)
//  {
//    newroot := new Node;
//    var newpivots := newArrayFill(MaxChildren()-1, DefaultKey());
//    var newchildren := newArrayFill(MaxChildren(), null);
//    newchildren[0] := root;
//    newroot.contents := Index(1, newpivots, newchildren);
//    newroot.repr := {newroot, newpivots, newchildren} + root.repr;
//    newroot.height := root.height + 1;
//
//    assert WFShapeChildren(newroot.contents.children[..1], newroot.repr, newroot.height) by { reveal_SeqRepr(); }
//    
//    ghost var inewroot := I(newroot);
//    IOfChild(newroot, 0);
//    assert inewroot.children == [ I(root) ];
//  }
//
//  lemma FullImpliesAllKeysNonEmpty(node: Node)
//    requires WF(node)
//    requires Full(node)
//    ensures Model.AllKeys(I(node)) != {}
//  {
//    var inode := I(node);
//    if inode.Leaf? {
//      assert inode.keys[0] in Model.AllKeys(inode) by { Model.reveal_AllKeys(); }
//    } else {
//      assert inode.pivots[0] in Model.AllKeys(inode) by { Model.reveal_AllKeys(); }
//    }
//  }
//  
//  method Insert(root: Node, key: Key, value: Value) returns (newroot: Node, oldvalue: Option<Value>)
//    requires WF(root)
//    ensures WF(newroot)
//    ensures fresh(newroot.repr - old(root.repr))
//    ensures Interpretation(newroot) == old(Interpretation(root))[key := value]
//    ensures oldvalue == MapLookupOption(old(Interpretation(root)), key)
//    modifies root.repr
//  {
//    if Full(root) {
//      FullImpliesAllKeysNonEmpty(root);
//      Model.GrowPreservesWF(I(root));
//      newroot := Grow(root);
//      Model.GrowPreservesInterpretation(I(root));
//    } else {
//      newroot := root;
//    }
//    assert Model.Interpretation(I(newroot)) == Model.Interpretation(old(I(root)));
//    oldvalue := InsertNode(newroot, key, value);
//  }
}

// module TestBtreeModel refines BtreeModel {
//   import opened NativeTypes
//   import Keys = Uint64_Order
//   type Value = uint64
// }

// module TestMutableBtree refines MutableBtree {
//   import Model = TestBtreeModel
    
//   function method MaxKeysPerLeaf() : uint64 { 64 }
//   function method MaxChildren() : uint64 { 64 }

//   function method DefaultValue() : Value { 0 }
//   function method DefaultKey() : Key { 0 }
// }

// module MainModule {
//   import opened NativeTypes
//   import TMB = TestMutableBtree`API
  
//   method Test()
//   {
//     // var n: uint64 := 1_000_000;
//     // var p: uint64 := 300_007;
//     var n: uint64 := 10_000_000;
//     var p: uint64 := 3_000_017;
//     // var n: uint64 := 100_000_000;
//     // var p: uint64 := 1_073_741_827;
//     var t := TMB.EmptyTree();
//     var i: uint64 := 0;
//     while i < n
//       invariant 0 <= i <= n
//       invariant TMB.WF(t)
//       invariant fresh(t.repr)
//     {
//       var oldvalue;
//       t, oldvalue := TMB.Insert(t, ((i * p) % n), i);
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
