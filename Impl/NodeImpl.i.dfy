// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Buckets/BucketImpl.i.dfy"
include "../lib/Lang/LinearBox.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "../PivotBetree/PivotBetree.i.dfy"

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
  import PivotBetree
  import Pivots = BoundedPivotsLib
  import PKV = PackedKV
  import opened Bounds
  import opened BucketImpl
  import opened BucketsLib
  import opened BucketWeights

  import ReferenceType`Internal

  linear datatype Node = Node(
      pivotTable: Pivots.PivotTable, 
      children: Option<seq<BT.G.Reference>>,
      linear buckets: lseq<BucketImpl.MutBucket>)
  {
    static method Alloc(pivotTable: Pivots.PivotTable, 
      children: Option<seq<BT.G.Reference>>, 
      linear buckets: lseq<BucketImpl.MutBucket>)
    returns (linear node: Node)
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

    static method EmptyNode() returns (linear node: Node)
    ensures node.Inv()
    ensures node.I() == PivotBetree.EmptyNode()
    ensures BT.WFNode(node.I())
    {
      linear var mutbucket := MutBucket.Alloc();
      linear var buckets := lseq_alloc(1);
      lseq_give_inout(inout buckets, 0, mutbucket);
      
      node := Node(Pivots.InitPivotTable(), None, buckets);
      assert node.I().buckets == [EmptyBucket()];
      WeightBucketListOneEmpty();
    }

    shared method BoundedBucket(pivots: Pivots.PivotTable, slot: uint64)
    returns (result: bool)
    requires Inv()
    requires |pivots| < 0x4000_0000_0000_0000
    requires Pivots.WFPivots(pivots)
    requires slot as nat < |buckets|
    ensures result == Pivots.BoundedKeySeq(pivots, buckets[slot as nat].I().keys)
    {
      var pkv := lseq_peek(buckets, slot).GetPkv();
      ghost var keys := PKV.IKeys(pkv.keys);
      assert buckets[slot as nat].I().keys == keys;

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

    shared method BucketsWellMarshalled() returns (result: bool)
    requires Inv()
    requires |buckets| < Uint64UpperBound()
    ensures result == BucketsLib.BucketListWellMarshalled(MutBucket.ILseq(buckets))
    {
      var i: uint64 := 0;

      while i < lseq_length_raw(buckets)
        invariant i as nat <= |buckets|
        invariant BucketListWellMarshalled(MutBucket.ISeq(lseqs(buckets)[..i]))
      {
        var bwm := lseq_peek(buckets, i).WellMarshalled();
        
        if !bwm {
          return false;
        }
        assert lseqs(buckets)[..i+1] == lseqs(buckets)[..i] + [ buckets[i as nat] ];
        i := i + 1;
      }
      assert lseqs(buckets) == lseqs(buckets)[..i];
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

    shared method CutoffNodeAndKeepLeft(pivot: Key) returns (linear node: Node)
    requires Inv()
    requires BT.WFNode(I())
    requires Pivots.ValidLeftCutOffKey(pivotTable, pivot)
    ensures node.Inv()
    ensures node.I() == BT.CutoffNodeAndKeepLeft(I(), pivot);
    {
      BT.reveal_CutoffNodeAndKeepLeft();
      var cLeft := Pivots.ComputeCutoffForLeft(this.pivotTable, pivot);
      var leftPivots := Pivots.ComputeSplitLeft(this.pivotTable, pivot, cLeft);
      var leftChildren := if this.children.Some? then Some(this.children.value[.. cLeft + 1]) else None;

      WeightBucketLeBucketList(MutBucket.ILseq(this.buckets), cLeft as int);  
      linear var splitBucket := lseq_peek(buckets, cLeft).SplitLeft(pivot);
      linear var slice := MutBucket.CloneSeq(this.buckets, 0, cLeft); // TODO clone not necessary?
      linear var leftBuckets := InsertLSeq(slice, splitBucket, cLeft);
      node := Node(leftPivots, leftChildren, leftBuckets);
    }

    shared method CutoffNodeAndKeepRight(pivot: Key) returns (linear node: Node)
    requires Inv()
    requires BT.WFNode(I())
    requires Pivots.BoundedKey(pivotTable, pivot)
    ensures node.Inv()
    ensures node.I() == BT.CutoffNodeAndKeepRight(I(), pivot);
    {
      BT.reveal_CutoffNodeAndKeepRight();
      var cRight := Pivots.ComputeCutoffForRight(this.pivotTable, pivot);
      var rightPivots := Pivots.ComputeSplitRight(this.pivotTable, pivot, cRight);
      var rightChildren := if this.children.Some? then Some(this.children.value[cRight ..]) else None;

      WeightBucketLeBucketList(MutBucket.ILseq(this.buckets), cRight as int);
      linear var splitBucket := lseq_peek(buckets, cRight).SplitRight(pivot);
      linear var slice := MutBucket.CloneSeq(buckets, cRight + 1, lseq_length_raw(buckets));
      linear var rightBuckets := InsertLSeq(slice, splitBucket, 0);
      node := Node(rightPivots, rightChildren, rightBuckets);
      assert node.I().buckets == BT.CutoffNodeAndKeepRight(I(), pivot).buckets;
      assert node.I().children == BT.CutoffNodeAndKeepRight(I(), pivot).children;
      assert node.I().pivotTable == BT.CutoffNodeAndKeepRight(I(), pivot).pivotTable;
    }

    shared method CutoffNode(lbound: Key, rbound: Option<Key>)
    returns (linear node : Node)
    requires Inv()
    requires BT.WFNode(I())
    requires BT.ValidSplitKey(I(), lbound, rbound)
    ensures node.Inv()
    ensures node.I() == BT.CutoffNode(I(), lbound, rbound)
    {
      BT.reveal_CutoffNode();
      match rbound {
        case None => {
          node := CutoffNodeAndKeepRight(lbound);
        }
        case Some(rbound) => {
          linear var node1 := CutoffNodeAndKeepLeft(rbound);
          node := node1.CutoffNodeAndKeepRight(lbound);
          var _ := FreeNode(node1);
        }
      }
    }

    shared method SplitChildLeft(num_children_left: uint64)
    returns (linear node: Node)
    requires Inv()
    requires |pivotTable| < Uint64UpperBound()
    requires 0 <= num_children_left as int - 1 <= |pivotTable| - 2
    requires children.Some? ==> 0 <= num_children_left as int <= |children.value|
    requires 0 <= num_children_left as int <= |buckets|
    ensures node.Inv()
    ensures node.I() == BT.SplitChildLeft(I(), num_children_left as int)
    {
      linear var slice := MutBucket.CloneSeq(buckets, 0, num_children_left);
      node := Node(
        pivotTable[ .. num_children_left + 1 ],
        if children.Some? then Some(children.value[ .. num_children_left ]) else None,
        slice
      );
    }

    shared method SplitChildRight(num_children_left: uint64)
    returns (linear node: Node)
    requires Inv()
    requires 0 <= num_children_left as int <= |pivotTable| - 1
    requires children.Some? ==> 0 <= num_children_left as int <= |children.value|
    requires 0 <= num_children_left as int <= |buckets|
    ensures node.Inv()
    ensures node.I() == BT.SplitChildRight(I(), num_children_left as int)
    {
      linear var slice := MutBucket.CloneSeq(buckets, num_children_left, lseq_length_raw(buckets));
      node := Node(
        pivotTable[ num_children_left .. ],
        if children.Some? then Some(children.value[ num_children_left .. ]) else None,
        slice
      );
    }

    linear inout method InsertKeyValue(key: Key, msg: Message)
    requires old_self.Inv();
    requires BT.WFNode(old_self.I())
    requires Pivots.BoundedKey(old_self.pivotTable, key)
    requires WeightBucketList(MutBucket.ILseq(buckets)) + WeightKey(key) + WeightMessage(msg) 
      < 0x1_0000_0000_0000_0000
    ensures self.Inv()
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
