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

  export API provides WF, Interpretation, EmptyTree, Insert, Query, Free, NativeTypes, Model, Options, Maps reveals Node, Key, Value
  export All reveals *
    
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
      case Leaf(keys, _) => seq_length(keys) == MaxKeysPerLeaf()
      case Index(_, children) => lseq_length_uint64(children) == MaxChildren()
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
    ensures Model.SplitLeaf(node, left, right, pivot)
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

  // We need to measure the height of Nodes to manage termination in the mutual
  // recursion between InsertNode and InsertIndex. You'd think that we wouldn't
  // need to, since datatypes are well-founded. But when we SplitChildOfIndex,
  // we replace some children with other children. The new children are of no
  // greater height, but they don't order in Dafny's internal datatype lattice.
  // Hence this machinery for explicitly measuring height.
  function IndexHeights(node: Node): seq<int>
    requires Model.WF(node)
    requires node.Index?
    decreases node, 0
  {
      seq(|node.children|, i requires 0<=i<|node.children| => Height(node.children[i]))
  }

  function {:opaque} Height(node: Node): nat
    requires Model.WF(node)
    ensures node.Leaf? ==> Height(node) == 0
    decreases node, 1
  {
    if node.Leaf?
    then 0
    else
      var heights := IndexHeights(node); seqMax(heights) + 1
  }

  lemma SubIndexHeight(node: Node, from: nat, to: nat)
    requires Model.WF(node)
    requires node.Index?
    requires 0 <= from < to <= |node.children|
    ensures Model.WF(Model.SubIndex(node, from, to))
    ensures Height(Model.SubIndex(node, from, to)) <= Height(node)
  {
    Model.SubIndexPreservesWF(node, from, to);
    var heights := IndexHeights(node);
    reveal_Height();
    assert IndexHeights(Model.SubIndex(node, from, to)) == heights[from .. to]; // trigger
    SubseqMax(heights, from, to);
  }

  method SplitIndex(linear node: Node, nleft: uint64)
    returns (linear left: Node, linear right: Node, pivot: Key)
    requires WF(node)
    requires node.Index?
    requires 2 <= |node.children|
    requires 0 < nleft as nat < |node.children|
    ensures WF(left)
    ensures WF(right)
    ensures Model.SplitIndex(node, left, right, pivot)
    ensures |left.children| == nleft as nat
    ensures pivot == node.pivots[nleft-1]
    ensures Height(left) <= Height(node)
    ensures Height(right) <= Height(node)
  {
    assert nleft as nat < |node.children| == lseq_length_uint64(node.children) as nat;
    var nright:uint64 := lseq_length_uint64(node.children) - nleft;
    linear var Index(pivots, children) := node;
    pivot := seq_get(pivots, nleft-1);

    // TODO(robj): perf-pportunity: recycle node as left, rather than copy-and-free.
    assert 0 <= nleft - 1;
    linear var leftPivots := AllocAndCopy(pivots, 0, nleft-1);
    linear var rightPivots := AllocAndCopy(pivots, nleft, nleft + nright - 1);

    linear var leftChildren, rightChildren;
    children, leftChildren := AllocAndMoveLseq(children, 0, nleft);
    children, rightChildren := AllocAndMoveLseq(children, nleft, nleft + nright);
    left := Model.Index(leftPivots, leftChildren);
    right := Model.Index(rightPivots, rightChildren);

    ImagineInverse(left.children);
    assert lseqs(right.children) == lseqs(node.children)[|left.children|..|node.children|];  // observe trigger
    ImagineInverse(right.children);

    assert Model.AllKeysBelowBound(node, nleft as int - 1); // trigger
    assert Model.AllKeysAboveBound(node, nleft as int); // trigger
    Model.SplitIndexPreservesWF(node, left, right, pivot);
    var _ := seq_free(pivots);
    lseq_free(children);
    SubIndexHeight(node, 0, nleft as nat);
    SubIndexHeight(node, nleft as nat, nleft as nat + nright as nat);
  }

  method SplitNode(linear node: Node) returns (linear left: Node, linear right: Node, pivot: Key)
    requires WF(node)
    requires Full(node)
    ensures WF(left)
    ensures WF(right)
    ensures !Full(left)
    ensures !Full(right)
    ensures Model.SplitNode(node, left, right, pivot)
    ensures pivot in Model.AllKeys(node)
    ensures Height(left) <= Height(node)
    ensures Height(right) <= Height(node)
  {
    if node.Leaf? {
      var boundary := seq_length(node.keys) / 2;
      pivot := seq_get(node.keys, boundary);
      Model.Keys.IsStrictlySortedImpliesLt(node.keys, boundary as int - 1, boundary as int);
      left, right := SplitLeaf(node, boundary, pivot);
    } else {
      var boundary := lseq_length_uint64(node.children) / 2;
//      assert 2 <= |node.children|;
//      assert 0 < boundary as nat < |node.children|;
      left, right, pivot := SplitIndex(node, boundary);
    }
    Model.reveal_AllKeys();
//    assert !Full(left);
//    assert !Full(right);
  }

  method SplitChildOfIndex(linear node: Node, childidx: uint64)
    returns (linear splitNode: Node)
    requires WF(node)
    requires node.Index?
    requires !Full(node)
    requires 0 <= childidx as nat < |node.children|
    requires Full(node.children[childidx as nat]);
    ensures splitNode.Index?
    ensures Model.SplitChildOfIndex(node, splitNode, childidx as int)
    ensures WF(splitNode)
    ensures !Full(splitNode.children[childidx as nat])
    ensures !Full(splitNode.children[childidx as nat + 1])
    ensures splitNode.pivots[childidx] in Model.AllKeys(node.children[childidx as nat])
    ensures Height(splitNode) <= Height(node)
  {
    linear var Index(pivots, children) := node;

    linear var origChild;
    children, origChild := lseq_take(children, childidx);

    linear var left, right;
    var pivot;
    left, right, pivot := SplitNode(origChild);
    pivots := InsertSeq(pivots, pivot, childidx);
    children := lseq_give(children, childidx, left);
    children := InsertLSeq(children, right, childidx + 1);
    splitNode := Model.Index(pivots, children);
    Model.SplitChildOfIndexPreservesWF(node, splitNode, childidx as int);

    // Every new child is shorter than some old child.
    ghost var wit := seq(|splitNode.children|, i requires 0<=i<|splitNode.children| =>
      if i <= childidx as nat then i else i-1);
    SeqMaxCorrespondence(IndexHeights(node), IndexHeights(splitNode), wit);
    assert Height(splitNode) <= Height(node) by { reveal_Height(); }
  }

  method InsertLeaf(linear node: Node, key: Key, value: Value)
    returns (linear n2: Node, oldvalue: Option<Value>)
    requires WF(node)
    requires node.Leaf?
    requires !Full(node)
    ensures n2 == Model.InsertLeaf(node, key, value)
    ensures WF(n2)
    ensures Model.Interpretation(n2) == Model.Interpretation(node)[key := value]
    ensures Model.AllKeys(n2) == Model.AllKeys(node) + {key}
    ensures oldvalue == MapLookupOption(Interpretation(node), key);
  {
    linear var Leaf(keys, values) := node;
    var pos: int64 := Model.Keys.ComputeLargestLte(keys, key);
    if 0 <= pos && seq_get(keys, pos as uint64) == key {
      oldvalue := Some(seq_get(values, pos as uint64));
      values := seq_set(values, pos as uint64, value);
    } else {
      oldvalue := None;
      keys := InsertSeq(keys, key, (pos + 1) as uint64);
      //assume Model.Keys.IsStrictlySorted(keys); // TODO(robj): I need a lemma call here.
      values := InsertSeq(values, value, (pos + 1) as uint64);
    }
    n2 := Model.Leaf(keys, values);
    Model.InsertLeafIsCorrect(node, key, value);
    Model.reveal_Interpretation();
  }
  
  lemma ChildrenAreShorter(parent: Node, childidx: nat)
    requires WF(parent)
    requires parent.Index?
    requires 0 <= childidx < |parent.children|
    ensures Height(parent.children[childidx]) < Height(parent)
  {
    var child := parent.children[childidx];
    assert IndexHeights(parent)[childidx] == Height(child); // trigger
    assert Height(child) in IndexHeights(parent);  // trigger *harder*
    reveal_Height();
  }

  method InsertIndex(linear node: Node, key: Key, value: Value)
    returns (linear n2: Node, oldvalue: Option<Value>)
    requires WF(node)
    requires node.Index?
    requires !Full(node)
    ensures WF(n2)
    ensures Model.Interpretation(n2) == Model.Interpretation(node)[key := value]
    ensures Model.AllKeys(n2) <= Model.AllKeys(node) + {key}  // shouldn't this be ==?
    ensures oldvalue == MapLookupOption(Interpretation(node), key)
    decreases Height(node), 1
  {
    n2 := node;
    var childidx := Route(n2.pivots, key);
    if Full(lseq_peek(n2.children, childidx)) {
      n2 := SplitChildOfIndex(n2, childidx);

      Model.SplitChildOfIndexPreservesWF(node, n2, childidx as nat);
      Model.SplitChildOfIndexPreservesInterpretation(node, n2, childidx as nat);
      Model.SplitChildOfIndexPreservesAllKeys(node, n2, childidx as nat);
      assert n2.pivots[childidx] in Model.AllKeys(node) by { Model.reveal_AllKeys(); }

      var t: int32 := Model.Keys.cmp(seq_get(n2.pivots, childidx), key);
      if  t <= 0 {
        childidx := childidx + 1;
        forall i | childidx as int - 1 < i < |n2.pivots|
          ensures Model.Keys.lt(key, n2.pivots[i])
        {
          assert n2.pivots[i] == node.pivots[i-1];
        }
      }
      Model.Keys.LargestLteIsUnique(n2.pivots, key, childidx as int - 1);
      assert Interpretation(n2) == Interpretation(node);
    }
    ghost var preparedNode := n2;
    assert Height(preparedNode) <= Height(node);
    assert Interpretation(preparedNode) == Interpretation(node);

    linear var Index(pivots, children) := n2;
    linear var childNode;
    // Note(Andrea): In Rust, childNode would be a mutable borrow from
    // children, and InsertNode would borrow it.
    children, childNode := lseq_take(children, childidx);
    ghost var childNodeSnapshot := childNode;
    assert Height(childNode) < Height(preparedNode) by { ChildrenAreShorter(preparedNode, childidx as nat); }
    assert Height(childNode) < Height(node);
    childNode, oldvalue := InsertNode(childNode, key, value);
    children := lseq_give(children, childidx, childNode);
    n2 := Model.Index(pivots, children);
    Model.RecursiveInsertIsCorrect(preparedNode, key, value, childidx as int, n2, n2.children[childidx as int]);
    if oldvalue.Some? {
      Model.InterpretationDelegation(preparedNode, key);
    } else {
      Model.reveal_Interpretation();
    }
  }

  method InsertNode(linear node: Node, key: Key, value: Value)
    returns (linear n2: Node, oldvalue: Option<Value>)
    requires WF(node)
    requires !Full(node)
    ensures WF(n2)
    ensures Model.Interpretation(n2) == Model.Interpretation(node)[key := value]
    ensures Model.AllKeys(n2) <= Model.AllKeys(node) + {key}  // shouldn't this be ==?
    ensures oldvalue == MapLookupOption(Interpretation(node), key)
    decreases Height(node), 2
  {
    if node.Leaf? {
      n2, oldvalue := InsertLeaf(node, key, value);
    } else {
      n2, oldvalue := InsertIndex(node, key, value);
    }
  }

  method Grow(linear root: Node) returns (linear newroot: Node)
    requires WF(root)
    requires Full(root)
    ensures WF(newroot)
    ensures newroot == Model.Grow(root)
    ensures !Full(newroot)
  {
    linear var pivots := seq_alloc_init(0, DefaultKey());
    linear var children := lseq_alloc(1);
    children := lseq_give(children, 0, root);
    newroot := Model.Index(pivots, children);
    assert lseqs(children) == [root]; // trigger
    ImagineInverse(children);
  }

  lemma FullImpliesAllKeysNonEmpty(node: Node)
    requires WF(node)
    requires Full(node)
    ensures Model.AllKeys(node) != {}
  {
    if node.Leaf? {
      assert node.keys[0] in Model.AllKeys(node) by { Model.reveal_AllKeys(); }
    } else {
      assert node.pivots[0] in Model.AllKeys(node) by { Model.reveal_AllKeys(); }
    }
  }
  
  method Insert(linear root: Node, key: Key, value: Value)
    returns (linear newroot: Node, oldvalue: Option<Value>)
    requires WF(root)
    ensures WF(newroot)
    ensures Interpretation(newroot) == Interpretation(root)[key := value]
    ensures oldvalue == MapLookupOption(Interpretation(root), key)
  {
    if Full(root) {
      FullImpliesAllKeysNonEmpty(root);
      Model.GrowPreservesWF(root);
      newroot := Grow(root);
      Model.GrowPreservesInterpretation(root);
    } else {
      newroot := root;
    }
    assert Model.Interpretation(newroot) == Model.Interpretation(root);
    newroot, oldvalue := InsertNode(newroot, key, value);
  }

  method Free(linear node: Node)
    requires WF(node)
  {
    linear match node {
      case Leaf(keys, values) => {
        var _ := seq_free(keys);
        var _ := seq_free(values);
      }
      case Index(pivots, children) => {
        var _ := seq_free(pivots);
        var i:uint64 := 0;
        linear var arr := children;
        while (i < lseq_length_uint64(arr))
          invariant 0 <= i as int <= |arr|
          invariant |arr| == |children|
          invariant forall j | 0 <= j < |arr| :: j in arr <==> j >= i as int
          invariant forall j | i as int <= j < |arr| :: arr[j] == children[j]
        {
          linear var child;
          arr, child := lseq_take(arr, i);
          Free(child);
          i := i + 1;
        }
        lseq_free(arr);
      }
    }
  }
}

module TestBtreeModel refines BtreeModel {
  import opened NativeTypes
//  import Keys = Uint64_Order
  type Value = uint64
}

module TestMutableBtree refines MutableBtree {
  import Model = TestBtreeModel
 
  function method MaxKeysPerLeaf() : uint64 { 64 }
  function method MaxChildren() : uint64 { 64 }

  function method DefaultValue() : Value { 0 }
  function method DefaultKey() : Key { [0] }
}

module MainModule {
  import opened LinearSequence_i
  import opened NativeTypes
  import TMB = TestMutableBtree`API

  method SeqFor(i: uint64)
  returns (result:TMB.Key)
  requires i < 256*256*256;
  {
    var b0:byte := (i / 65536) as byte;
    var r := i - (b0 as uint64 * 65536);
    var b1:byte := (r / 256) as byte;
    var b2:byte := (r - (b1 as uint64)*256) as byte;

    result := [b0, b1, b2];
  }

  method Main()
  {
    // var n: uint64 := 1_000_000;
    // var p: uint64 := 300_007;
    var n: uint64 := 10_000;
    var p: uint64 := 3_000_017;
    // var n: uint64 := 100_000_000;
    // var p: uint64 := 1_073_741_827;
    linear var t := TMB.EmptyTree();
    var i: uint64 := 0;
    while i < n
      invariant 0 <= i <= n
      invariant TMB.WF(t)
//      invariant fresh(t.repr)
    {
      var oldvalue;
      var keyv := ((i * p) % n);
      var key := SeqFor(keyv);
      t, oldvalue := TMB.Insert(t, key, i);
      if (i%100)==0 {
        print "i", i, "\n";
      }
      i := i + 1;
    }

    print "PASSED\n";
    TMB.Free(t);
  }
} 
