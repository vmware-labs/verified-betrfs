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
    assert lseqs(right.children) == lseqs(node.children)[|left.children|..|node.children|];  // observe trigger
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
    ensures Model.SplitNode(node, left, right, pivot)
    ensures pivot in Model.AllKeys(node)
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
    Model.reveal_Interpretation();
    Model.reveal_AllKeys();

    linear var Leaf(keys, values) := node;
    var pos: int64 := Model.Keys.ComputeLargestLte(keys, key);
    if 0 <= pos && seq_get(keys, pos as uint64) == key {
      oldvalue := Some(seq_get(values, pos as uint64));
      values := seq_set(values, pos as uint64, value);
    } else {
      oldvalue := None;
      keys := InsertSeq(keys, key, (pos + 1) as uint64);
      values := InsertSeq(values, value, (pos + 1) as uint64);
    }
    n2 := Model.Leaf(keys, values);
    Model.InsertLeafIsCorrect(node, key, value);
  }

/*
  method InsertIndexSelectAndPrepareChild(linear node: Node, key: Key) returns (linear n2: Node, childidx: uint64)
    requires WF(node)
    requires node.Index?
    requires !Full(node)
    ensures WF(n2)
    ensures n2.Index?
    ensures childidx as int == Model.Keys.LargestLte(n2.pivots[..n2.nchildren-1], key) + 1
    ensures node.children[childidx] != null
    ensures !Full(node.children[childidx])
    ensures Model.Interpretation(I(node)) == Model.Interpretation(old(I(node)))
    ensures Model.AllKeys(I(node)) == Model.AllKeys(old(I(node)))
    modifies node, node.repr
  {
    Model.reveal_AllKeys();
    assert WFShapeChildren(node.children[..node.nchildren], node.repr, node.height);

    childidx := Model.Keys.ArrayLargestLtePlus1(node.pivots, 0, node.nchildren-1, key);
    if Full(node.children[childidx]) {
      ghost var oldpivots := node.pivots[..node.nchildren-1];
      SplitChildOfIndex(node, childidx);
      ghost var newpivots := node.pivots[..node.nchildren-1];
      Model.SplitChildOfIndexPreservesWF(old(I(node)), I(node), childidx as int);
      Model.SplitChildOfIndexPreservesInterpretation(old(I(node)), I(node), childidx as int);
      Model.SplitChildOfIndexPreservesAllKeys(old(I(node)), I(node), childidx as int);

      var t: int32 := Model.Keys.cmp(node.pivots[childidx], key);
      if  t <= 0 {
        childidx := childidx + 1;
        forall i | childidx as int - 1 < i < |newpivots|
          ensures Model.Keys.lt(key, newpivots[i])
        {
          assert newpivots[i] == oldpivots[i-1];
        }
      }
      Model.Keys.LargestLteIsUnique(node.pivots[..node.nchildren-1], key, childidx as int - 1);
    }
  }
*/
  
  /*
  method InsertIndex(node: Node, key: Key, value: Value) returns (oldvalue: Option<Value>)
    requires WF(node)
    requires node.contents.Index?
    requires !Full(node)
    ensures WFShape(node)
    ensures fresh(node.repr - old(node.repr))
    ensures node.height == old(node.height)
    ensures Model.WF(I(node))
    ensures Model.Interpretation(I(node)) == Model.Interpretation(old(I(node)))[key := value]
    ensures Model.AllKeys(I(node)) <= Model.AllKeys(old(I(node))) + {key}
    ensures oldvalue == MapLookupOption(old(Interpretation(node)), key)
    modifies node, node.repr
    decreases node.height, 1
  {
    var childidx: uint64 := InsertIndexSelectAndPrepareChild(node, key);
    oldvalue := InsertIndexChildNotFull(node, childidx, key, value);
  }
  
  method InsertNode(linear node: Node, key: Key, value: Value)
    returns (linear n2: Node, oldvalue: Option<Value>)
    requires WF(node)
    requires !Full(node)
    ensures WF(n2)
    // TODO(jonh) clean up all the old-iness
    ensures Model.Interpretation(n2) == Model.Interpretation(node)[key := value]
    ensures Model.AllKeys(I(node)) <= Model.AllKeys(old(I(node))) + {key}
    ensures oldvalue == MapLookupOption(old(Interpretation(node)), key)
    modifies node, node.repr
    decreases node.height, 2
  {
    if node.contents.Leaf? {
      oldvalue := InsertLeaf(node, key, value);
    } else {
      oldvalue := InsertIndex(node, key, value);
    }
  }
  */

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
