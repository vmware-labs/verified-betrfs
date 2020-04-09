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

  // TODO(robj): someday, if perf demands it: switch to a linear version of
  // MutableVec as the underlying storage to save some sequence copies?

  method SplitLeaf(linear node: Node, nleft: uint64, ghost pivot: Key)
    returns (linear left: Node, linear right: Node)
    requires WF(node)
    requires node.Leaf?
    requires 0 < nleft as int < |node.keys|
    requires Model.Keys.lt(node.keys[nleft-1], pivot)
    requires Model.Keys.lte(pivot, node.keys[nleft])
    ensures WF(left)
    ensures WF(right)
    ensures Model.SplitLeaf(old(node), left, right, pivot)
    ensures |left.keys| == nleft as int
  {
    ghost var nkeys := |node.keys|;
    Model.Keys.StrictlySortedSubsequence(node.keys, nleft as int, nkeys);
    Model.Keys.StrictlySortedSubsequence(node.keys, 0, nleft as int);
    Model.Keys.IsStrictlySortedImpliesLt(node.keys, nleft as int - 1, nleft as int);
    assert node.keys[nleft..nkeys] == node.keys[..nkeys][nleft..nkeys];

    var nright:uint64 := seq_length(node.keys) as uint64 - nleft;
    linear var Leaf(keys, values) := node;

    // TODO(robj): perf-pportunity: recycle node as left, rather than copy-and-free.
    linear var leftKeys := AllocAndCopy(keys, 0, nleft);
    linear var rightKeys := AllocAndCopy(keys, nleft, nleft + nright);
    linear var leftValues := AllocAndCopy(values, 0, nleft);
    linear var rightValues := AllocAndCopy(values, nleft, nleft + nright);
    left := Model.Leaf(leftKeys, leftValues);
    right := Model.Leaf(rightKeys, rightValues);
    var _ := seq_free(keys);
    var _ := seq_free(values);
  }

  method SplitIndex(linear node: Node, nleft: uint64)
    returns (linear left: Node, linear right: Node, pivot: Key)
    requires WF(node)
    requires node.Index?
    requires 2 <= |node.children|
    requires 0 < nleft as nat < |node.children|
    ensures WF(left)
    ensures WF(right)
    ensures Model.SplitIndex(old(node), left, right, pivot)
    ensures |left.children| == nleft as nat
    ensures pivot == old(node.pivots[nleft-1])
  {
    var nright:uint64 := |node.children| as uint64 - nleft;
    linear var Index(pivots, children) := node;
    pivot := seq_get(pivots, nleft-1);

    // TODO(robj): perf-pportunity: recycle node as left, rather than copy-and-free.
    linear var leftPivots := AllocAndCopy(pivots, 0, nleft-1);
    linear var rightPivots := AllocAndCopy(pivots, nleft, nleft + nright - 1);

    linear var leftChildren, rightChildren;
    children, leftChildren := AllocAndMoveLseq(children, 0, nleft);
    children, rightChildren := AllocAndMoveLseq(children, nleft, nleft + nright);
    left := Model.Index(leftPivots, leftChildren);
    right := Model.Index(rightPivots, rightChildren);

    ImagineInverse(left.children);
    assert lseqs(right.children) == lseqs(old(node.children))[|left.children|..|node.children|];  // observe trigger
    ImagineInverse(right.children);

    assert Model.AllKeysBelowBound(node, nleft as int - 1); // trigger
    assert Model.AllKeysAboveBound(node, nleft as int); // trigger
    Model.SplitIndexPreservesWF(node, left, right, pivot);
    var _ := seq_free(pivots);
    lseq_free(children);
  }

  method SplitNode(linear node: Node) returns (linear left: Node, linear right: Node, pivot: Key)
    requires WF(node)
    requires Full(node)
    ensures WF(left)
    ensures WF(right)
    ensures !Full(left)
    ensures !Full(right)
    ensures Model.SplitNode(old(node), left, right, pivot)
    ensures pivot in Model.AllKeys(old(node))
  {
    if node.Leaf? {
      var boundary := seq_length(node.keys) as uint64 / 2;
      pivot := seq_get(node.keys, boundary);
      Model.Keys.IsStrictlySortedImpliesLt(node.keys, boundary as int - 1, boundary as int);
      left, right := SplitLeaf(node, boundary, pivot);
    } else {
      var boundary := |node.children| as uint64 / 2;
      left, right, pivot := SplitIndex(node, boundary);
    }
    Model.reveal_AllKeys();
  }


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
