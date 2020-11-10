include "StateModel.i.dfy"
include "../lib/Buckets/BucketImpl.i.dfy"
include "../lib/Lang/LinearBox.i.dfy"

//
// Implements PivotBetree/PivotBetreeSpec.Node. (There's no Model file
// because Node is already a precise functional model of this code.)
//

module NodeImpl {
  import opened Options
  import opened Sequences
  import opened NativeTypes
  import opened LinearSequence_s
  import opened LinearSequence_i
  import opened LinearOption
  import opened KeyType
  import opened ValueMessage

  import BT = PivotBetreeSpec`Internal
  import Pivots = BoundedPivotsLib
  import PKV = PackedKV
  import opened Bounds
  import opened BucketImpl
  import opened BucketsLib
  import opened BucketWeights

  import MM = MutableMap
  import ReferenceType`Internal

  linear datatype Node = Node(pivotTable: Pivots.PivotTable, children: Option<seq<BT.G.Reference>>, linear buckets: lseq<BucketImpl.MutBucket>)
  {
    static method Alloc(pivotTable: Pivots.PivotTable, children: Option<seq<BT.G.Reference>>, linear buckets: lseq<BucketImpl.MutBucket>) returns (linear node: Node)
    requires MutBucket.InvLseq(buckets)
    ensures node.pivotTable == pivotTable;
    ensures node.children == children;
    ensures node.buckets == buckets;
    ensures node.Inv();
    {
      node := Node(pivotTable, children, buckets);
    }

    predicate Inv()
    {
      MutBucket.InvLseq(buckets)
    }

    function I() : BT.G.Node
    requires Inv()
    {
      BT.G.Node(pivotTable, children,
        BucketImpl.MutBucket.ILseq(buckets))
    }

    static method GetBucketsLen(shared node: Node) returns (len: uint64)
    requires node.Inv()
    ensures len as nat == |node.buckets|
    {
      len := lseq_length_raw(node.buckets);
    }

    static method GetChildren(shared node: Node) returns (children: Option<seq<BT.G.Reference>>)
    requires node.Inv()
    ensures children == node.children
    {
      children := node.children;
    }

    static method GetPivots(shared node: Node) returns (pivots: Pivots.PivotTable)
    requires node.Inv()
    ensures pivots == node.pivotTable
    {
      pivots := node.pivotTable;
    }

    static method BoundedBucket(shared node: Node, pivots: Pivots.PivotTable, slot: uint64) returns (result: bool)
    requires node.Inv()
    requires |pivots| < 0x4000_0000_0000_0000
    requires Pivots.WFPivots(pivots)
    requires slot as nat < |node.buckets|
    ensures result == Pivots.BoundedKeySeq(pivots, node.buckets[slot as nat].I().keys)
    {
      var pkv := lseq_peek(node.buckets, slot).GetPkv();
      ghost var keys := PKV.IKeys(pkv.keys);
      assert node.buckets[slot as nat].I().keys == keys;

      var bounded := true;
      var i := 0 as uint64;
      var len := PKV.NumKVPairs(pkv);

      while i < len && bounded
      invariant 0 <= i <= len
      invariant bounded == Pivots.BoundedKeySeq(pivots, keys[..i])
      {
        var key := PKV.GetKey(pkv, i);
        assert key == keys[i];
        bounded := Pivots.ComputeBoundedKey(pivots, key);
        i := i + 1;
      }
      return bounded;
    }

    shared method BucketWellMarshalled(slot: uint64) returns (result: bool)
    requires Inv()
    requires slot as nat < |buckets|
    ensures result == BucketsLib.BucketWellMarshalled(buckets[slot as nat].I())
    {
      result := lseq_peek(buckets, slot).WellMarshalled();
    }

    static method BucketsWellMarshalled(shared node: Node) returns (result: bool)
    requires node.Inv()
    requires |node.buckets| < Uint64UpperBound()
    ensures result == BucketsLib.BucketListWellMarshalled(MutBucket.ILseq(node.buckets))
    {
      var i: uint64 := 0;

      while i < lseq_length_raw(node.buckets)
        invariant i as nat <= |node.buckets|
        invariant BucketListWellMarshalled(MutBucket.ISeq(lseqs(node.buckets)[..i]))
      {
        var bwm := lseq_peek(node.buckets, i).WellMarshalled();
        
        if !bwm {
          return false;
        }
        assert lseqs(node.buckets)[..i+1] == lseqs(node.buckets)[..i] + [ node.buckets[i as nat] ];
        i := i + 1;
      }
      assert lseqs(node.buckets) == lseqs(node.buckets)[..i];
      return true;  
    }

    linear inout method UpdateSlot(slot: uint64, linear bucket: BucketImpl.MutBucket, childref: BT.G.Reference)
    requires old_self.Inv()
    requires bucket.Inv()
    requires old_self.children.Some?
    requires 0 <= slot as int < |old_self.children.value|
    requires 0 <= slot as int < |old_self.buckets|
    requires slot as int + 1 < 0x1_0000_0000_0000_0000
    ensures self.Inv() // mark all with self.
    ensures self.I() == BT.G.Node(
        old_self.I().pivotTable,
        Some(old_self.I().children.value[slot as int := childref]),
        old_self.I().buckets[slot as int := bucket.bucket]
      )
    {
      linear var replaced := lseq_swap_inout(inout self.buckets, slot, bucket);
      inout self.children := Some(SeqIndexUpdate(self.children.value, slot, childref));
      var _ := FreeMutBucket(replaced);
      assert self.Inv();
    }

    linear inout method SplitParent(slot: uint64, pivot: Key, left_childref: BT.G.Reference, right_childref: BT.G.Reference)
    requires old_self.Inv()
    requires BT.WFNode(old_self.I())
    requires old_self.children.Some?
    requires 0 <= slot as int < |old_self.children.value|
    requires 0 <= slot as int < |old_self.buckets|
    ensures self.Inv()
    ensures self.I() == (BT.SplitParent(old_self.I(), pivot, slot as int, left_childref, right_childref))
    {
      ghost var b := BT.SplitParent(self.I(), pivot, slot as int, left_childref, right_childref);

      inout self.pivotTable := Sequences.Insert(self.pivotTable, Pivots.Keyspace.Element(pivot), slot+1);
      MutBucket.SplitOneInList(inout self.buckets, slot, pivot);
      assert MutBucket.ILseq(self.buckets) == SplitBucketInList(old_self.I().buckets, slot as int, pivot);
      
      var childrenReplaced := Replace1with2(self.children.value, left_childref, right_childref, slot);
      inout self.children := Some(childrenReplaced);

      ghost var a := self.I();
      assert a == b;
    }

    shared method CutoffNodeAndKeepLeft(pivot: Key) returns (linear node': Node)
    requires Inv()
    requires BT.WFNode(I())
    requires Pivots.ValidLeftCutOffKey(pivotTable, pivot)
    ensures node'.Inv()
    ensures node'.I() == BT.CutoffNodeAndKeepLeft(I(), pivot);
    {
      BT.reveal_CutoffNodeAndKeepLeft();
      var cLeft := Pivots.ComputeCutoffForLeft(this.pivotTable, pivot);
      var leftPivots := Pivots.ComputeSplitLeft(this.pivotTable, pivot, cLeft);
      var leftChildren := if this.children.Some? then Some(this.children.value[.. cLeft + 1]) else None;

      WeightBucketLeBucketList(MutBucket.ILseq(this.buckets), cLeft as int);  
      linear var splitBucket := lseq_peek(buckets, cLeft).SplitLeft(pivot);
      linear var slice := MutBucket.CloneSeq(this.buckets, 0, cLeft); // TODO clone not necessary?
      linear var leftBuckets := InsertLSeq(slice, splitBucket, cLeft);
      node' := Node(leftPivots, leftChildren, leftBuckets);
    }

    shared method CutoffNodeAndKeepRight(pivot: Key) returns (linear node': Node)
    requires Inv()
    requires BT.WFNode(I())
    requires Pivots.BoundedKey(pivotTable, pivot)
    ensures node'.Inv()
    ensures node'.I() == BT.CutoffNodeAndKeepRight(I(), pivot);
    {
      BT.reveal_CutoffNodeAndKeepRight();
      var cRight := Pivots.ComputeCutoffForRight(this.pivotTable, pivot);
      var rightPivots := Pivots.ComputeSplitRight(this.pivotTable, pivot, cRight);
      var rightChildren := if this.children.Some? then Some(this.children.value[cRight ..]) else None;

      WeightBucketLeBucketList(MutBucket.ILseq(this.buckets), cRight as int);
      linear var splitBucket := lseq_peek(buckets, cRight).SplitRight(pivot);
      linear var slice := MutBucket.CloneSeq(buckets, cRight + 1, lseq_length_raw(buckets));
      linear var rightBuckets := InsertLSeq(slice, splitBucket, 0);
      node' := Node(rightPivots, rightChildren, rightBuckets);
      assert node'.I().buckets == BT.CutoffNodeAndKeepRight(I(), pivot).buckets;
      assert node'.I().children == BT.CutoffNodeAndKeepRight(I(), pivot).children;
      assert node'.I().pivotTable == BT.CutoffNodeAndKeepRight(I(), pivot).pivotTable;
    }

    static method CutoffNode(shared node: Node, lbound: Key, rbound: Option<Key>)
    returns (linear node' : Node)
    requires node.Inv()
    requires BT.WFNode(node.I())
    requires BT.ValidSplitKey(node.I(), lbound, rbound)
    ensures node'.Inv()
    ensures node'.I() == BT.CutoffNode(node.I(), lbound, rbound)
    {
      BT.reveal_CutoffNode();
      match rbound {
        case None => {
          node' := node.CutoffNodeAndKeepRight(lbound);
        }
        case Some(rbound) => {
          linear var node1 := node.CutoffNodeAndKeepLeft(rbound);
          node' := node1.CutoffNodeAndKeepRight(lbound);
          var _ := FreeNode(node1);
        }
      }
    }

    static method SplitChildLeft(shared node: Node, num_children_left: uint64)
    returns (linear node': Node)
    requires node.Inv()
    requires |node.pivotTable| < Uint64UpperBound()
    requires 0 <= num_children_left as int - 1 <= |node.pivotTable| - 2
    requires node.children.Some? ==> 0 <= num_children_left as int <= |node.children.value|
    requires 0 <= num_children_left as int <= |node.buckets|
    ensures node'.Inv()
    ensures node'.I() == BT.SplitChildLeft(node.I(), num_children_left as int)
    {
      linear var slice := MutBucket.CloneSeq(node.buckets, 0, num_children_left);
      node' := Node(
        node.pivotTable[ .. num_children_left + 1 ],
        if node.children.Some? then Some(node.children.value[ .. num_children_left ]) else None,
        slice
      );
    }

    static method SplitChildRight(shared node: Node, num_children_left: uint64)
    returns (linear node': Node)
    requires node.Inv()
    requires 0 <= num_children_left as int <= |node.pivotTable| - 1
    requires node.children.Some? ==> 0 <= num_children_left as int <= |node.children.value|
    requires 0 <= num_children_left as int <= |node.buckets|
    ensures node'.Inv()
    ensures node'.I() == BT.SplitChildRight(node.I(), num_children_left as int)
    {
      linear var slice := MutBucket.CloneSeq(node.buckets, num_children_left, lseq_length_raw(node.buckets));
      node' := Node(
        node.pivotTable[ num_children_left .. ],
        if node.children.Some? then Some(node.children.value[ num_children_left .. ]) else None,
        slice
      );
    }

    linear inout method InsertKeyValue(key: Key, msg: Message)
    requires old_self.Inv();
    requires BT.WFNode(old_self.I())
    requires Pivots.BoundedKey(old_self.pivotTable, key)
    requires WeightBucketList(MutBucket.ILseq(buckets)) + WeightKey(key) + WeightMessage(msg) < 0x1_0000_0000_0000_0000
    ensures self.Inv();
    ensures self.I() == BT.NodeInsertKeyValue(old_self.I(), key, msg)
    {
      BT.reveal_NodeInsertKeyValue();

      var r := Pivots.ComputeRoute(self.pivotTable, key);

      WeightBucketLeBucketList(MutBucket.ILseq(self.buckets), r as int);
      linear var b := lseq_take_inout(inout self.buckets, r);
      inout b.Insert(key, msg);
      lseq_give_inout(inout self.buckets, r, b);

      forall i | 0 <= i < |self.buckets|
      ensures self.buckets[i].Inv()
      ensures i != r as int ==> self.buckets[i].bucket == old_self.buckets[i].bucket
      {
      }

      assert self.Inv();
      assert self.I().buckets == BT.NodeInsertKeyValue(old_self.I(), key, msg).buckets;
    }
  }

  function method FreeNode(linear node: Node) : ()
  requires node.Inv()
  {
    linear var Node(_, _, buckets) := node;
    FreeMutBucketSeq(buckets)
  }
}

// boxed linear node, use till we have linear mutable map with linear items
module BoxNodeImpl {
  import opened LinearSequence_s
  import opened LinearSequence_i
  import opened LinearBox_s
  import opened LinearBox
  import opened KeyType
  import opened ValueMessage
  import opened NativeTypes
  import opened BucketImpl
  import opened BucketWeights
  import opened Options

  import IM = StateModel
  import MM = MutableMap
  import BT = PivotBetreeSpec`Internal

  import L : NodeImpl

  class Node {
    var box: BoxedLinearOption<L.Node>;
    ghost var Repr: set<object>

    function Read() : L.Node
    requires box.Inv()
    reads this, box, box.Repr
    {
      box.Read()
    }

    constructor(pivotTable: Pivots.PivotTable, children: Option<seq<BT.G.Reference>>, linear buckets: lseq<MutBucket>)
    requires MutBucket.InvLseq(buckets)
    ensures Inv()
    ensures Read().pivotTable == pivotTable
    ensures Read().children == children
    ensures Read().buckets == buckets
    ensures fresh(this.Repr)
    {
      linear var node := L.Node.Alloc(pivotTable, children, buckets);
      box := new BoxedLinearOption(node, ToDestructor(L.FreeNode));
      new;
      Repr := {this} + box.Repr;
    }

    constructor InitFromNode(linear node: L.Node)
    requires node.Inv()
    ensures Inv()
    ensures Read() == node
    ensures fresh(this.Repr)
    {
      box := new BoxedLinearOption(node, ToDestructor(L.FreeNode));
      new;
      Repr := {this} + box.Repr;
    }

    function I() : (result: L.BT.G.Node)
    reads this, this.box.Repr
    requires Inv()
    {
      this.Read().I()
    }

    predicate Inv()
    ensures Inv() ==> this in this.Repr
    reads this, this.Repr
    {
      && this.box in this.Repr
      && this.Repr == {this} + this.box.Repr
      && this.box.Inv()
      && this.box.Has()
      && this.box.DataInv == L.FreeNode.requires
      && this.Read().Inv()
    }

    method SplitParent(slot: uint64, pivot: Key, left_childref: L.BT.G.Reference, right_childref: L.BT.G.Reference)
    requires Inv()
    requires L.BT.WFNode(I())
    requires Read().children.Some?
    requires 0 <= slot as int < |Read().children.value|
    requires 0 <= slot as int < |Read().buckets|
    ensures Inv()
    ensures I() == (L.BT.SplitParent(old(I()), pivot, slot as int, left_childref, right_childref))
    ensures Repr == old(Repr)
    modifies this.Repr
    {
      linear var n := this.box.Take();
      inout n.SplitParent(slot, pivot, left_childref, right_childref);
      this.box.Give(n);
    }

    method InsertKeyValue(key: Key, msg: Message)
    requires Inv()
    requires L.BT.WFNode(I())
    requires L.Pivots.BoundedKey(Read().pivotTable, key)
    requires WeightBucketList(MutBucket.ILseq(Read().buckets)) + WeightKey(key) + WeightMessage(msg) < 0x1_0000_0000_0000_0000
    ensures Inv();
    ensures I() == old(L.BT.NodeInsertKeyValue(I(), key, msg))
    ensures Repr == old(Repr)
    modifies this.Repr
    {
      linear var n := this.box.Take();
      inout n.InsertKeyValue(key, msg);
      this.box.Give(n);
    }

    method UpdateSlot(slot: uint64, linear bucket: MutBucket, childref: BT.G.Reference) 
    requires Inv()
    requires bucket.Inv()
    requires Read().children.Some?
    requires 0 <= slot as int < |Read().children.value|
    requires 0 <= slot as int < |Read().buckets|
    requires slot as int + 1 < 0x1_0000_0000_0000_0000
    ensures Inv()
    ensures I() == L.BT.G.Node(
        old(I()).pivotTable,
        Some(old(I()).children.value[slot as int := childref]),
        old(I()).buckets[slot as int := bucket.bucket]
      )
    ensures Repr == old(Repr)
    modifies this.Repr
    {
      linear var n := this.box.Take();  
      inout n.UpdateSlot(slot, bucket, childref);
      this.box.Give(n);
    }

    method BucketsWellMarshalled() returns (result: bool)
    requires Inv()
    requires |Read().buckets| < Uint64UpperBound()
    ensures result == BucketsLib.BucketListWellMarshalled(MutBucket.ILseq(Read().buckets))
    {
      result := L.Node.BucketsWellMarshalled(this.box.Borrow());
    }

    method SplitChildLeft(num_children_left: uint64)
    returns (node': Node)
    requires Inv()
    requires |Read().pivotTable| < Uint64UpperBound()
    requires 0 <= num_children_left as int - 1 <= |Read().pivotTable| - 2
    requires Read().children.Some? ==> 0 <= num_children_left as int <= |Read().children.value|
    requires 0 <= num_children_left as int <= |Read().buckets|
    ensures node'.Inv()
    ensures node'.I() == L.BT.SplitChildLeft(I(), num_children_left as int)
    ensures fresh(node'.Repr)
    {
      linear var lnode' := L.Node.SplitChildLeft(this.box.Borrow(), num_children_left);
      node' := new Node.InitFromNode(lnode');
    }

    method SplitChildRight(num_children_left: uint64)
    returns (node': Node)
    requires Inv()
    requires 0 <= num_children_left as int <= |Read().pivotTable| - 1
    requires Read().children.Some? ==> 0 <= num_children_left as int <= |Read().children.value|
    requires 0 <= num_children_left as int <= |Read().buckets|
    ensures node'.Inv()
    ensures node'.I() == L.BT.SplitChildRight(I(), num_children_left as int)
    ensures fresh(node'.Repr)
    {
      linear var lnode' := L.Node.SplitChildRight(this.box.Borrow(), num_children_left);
      node' := new Node.InitFromNode(lnode');
    }

    method CutoffNode(lbound: Key, rbound: Option<Key>)
    returns (node' : Node)
    requires Inv()
    requires BT.WFNode(I())
    requires BT.ValidSplitKey(I(), lbound, rbound)
    ensures node'.Inv()
    ensures node'.I() == L.BT.CutoffNode(I(), lbound, rbound)
    ensures fresh(node'.Repr)
    {
      linear var lnode' := L.Node.CutoffNode(this.box.Borrow(), lbound, rbound);
      node' := new Node.InitFromNode(lnode');
    }

    method GetBucketsLen() returns (len: uint64)
    requires Inv()
    ensures len as nat == |Read().buckets|
    {
      len := L.Node.GetBucketsLen(this.box.Borrow());
    }

    method GetChildren() returns (children: Option<seq<BT.G.Reference>>)
    requires Inv()
    ensures children == Read().children
    {
      children := L.Node.GetChildren(this.box.Borrow());
    }

    method GetPivots() returns (pivots: Pivots.PivotTable)
    requires Inv()
    ensures pivots == Read().pivotTable
    {
      pivots := L.Node.GetPivots(this.box.Borrow());
    }

    method BoundedBucket(pivots: Pivots.PivotTable, slot: uint64) returns (result: bool)
    requires Inv()
    requires |pivots| < 0x4000_0000_0000_0000
    requires Pivots.WFPivots(pivots)
    requires slot as nat < |Read().buckets|
    ensures result == Pivots.BoundedKeySeq(pivots, Read().buckets[slot as nat].I().keys)
    {
      result := L.Node.BoundedBucket(this.box.Borrow(), pivots, slot);
    }
  }
}
