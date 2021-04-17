// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Buckets/BucketImpl.i.dfy"
include "../lib/Buckets/TranslationImpl.i.dfy"
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
  import opened TranslationImpl

  import ReferenceType`Internal

  linear datatype Node = Node(
      pivotTable: Pivots.PivotTable,
      edgeTable: Translations.EdgeTable,
      children: Option<seq<BT.G.Reference>>,
      linear buckets: lseq<BucketImpl.MutBucket>)
  {
    static method Alloc(pivotTable: Pivots.PivotTable,
      edgeTable: Translations.EdgeTable, 
      children: Option<seq<BT.G.Reference>>, 
      linear buckets: lseq<BucketImpl.MutBucket>)
    returns (linear node: Node)
    requires MutBucket.InvLseq(buckets)
    ensures node.pivotTable == pivotTable
    ensures node.edgeTable == edgeTable
    ensures node.children == children
    ensures node.buckets == buckets
    ensures node.Inv()
    {
      node := Node(pivotTable, edgeTable, children, buckets);
    }

    predicate Inv()
    {
      MutBucket.InvLseq(buckets)
    }

    function I() : BT.G.Node
    requires Inv()
    {
      BT.G.Node(pivotTable, edgeTable, children,
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

      node := Node(Pivots.InitPivotTable(), [None], None, buckets);
      assert node.I().buckets == [EmptyBucket()];
      WeightBucketListOneEmpty();
    }

    // shared method BoundedBucket(pivots: Pivots.PivotTable, slot: uint64)
    // returns (result: bool)
    // requires Inv()
    // requires |pivots| < 0x4000_0000_0000_0000
    // requires Pivots.WFPivots(pivots)
    // requires slot as nat < |buckets|
    // ensures result == Pivots.BoundedKeySeq(pivots, buckets[slot as nat].I().keys)
    // {
    //   shared var bucket := lseq_peek(buckets, slot);
    //   var pkv := bucket.GetPkv();
      
    //   ghost var keys := PKV.IKeys(pkv.keys);
    //   assert buckets[slot as nat].I().keys == keys;

    //   var bounded := true;
    //   var len := PKV.NumKVPairs(pkv);

    //   if bucket.sorted {
    //     if len > 0 {
    //       var key := PKV.GetKey(pkv, 0);
    //       assert key == keys[0];
    //       bounded := Pivots.ComputeBoundedKey(pivots, key);
    //       if bounded {
    //         key := PKV.GetKey(pkv, len-1);
    //         assert key == keys[|keys|-1];
    //         bounded := Pivots.ComputeBoundedKey(pivots, key);
    //       }
    //       assert bounded == Pivots.BoundedSortedKeySeq(pivots, keys);
    //       Pivots.BoundedSortedKeySeqIsBoundedKeySeq(pivots, keys);
    //     }
    //   } else {
    //     var i := 0 as uint64;
    //     while i < len && bounded
    //     invariant 0 <= i <= len
    //     invariant bounded == Pivots.BoundedKeySeq(pivots, keys[..i])
    //     {
    //       var key := PKV.GetKey(pkv, i);
    //       assert key == keys[i];
    //       bounded := Pivots.ComputeBoundedKey(pivots, key);
    //       i := i + 1;
    //     }
    //   }
    //   return bounded;
    // }

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
    ensures self.Inv()
    ensures self.I() == BT.G.Node(
        old_self.I().pivotTable,
        old_self.I().edgeTable,
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
      inout self.edgeTable := Replace1with2(self.edgeTable, None, None, slot);

      MutBucket.SplitOneInList(inout self.buckets, slot, pivot);
      assert MutBucket.ILseq(self.buckets) == SplitBucketInList(old_self.I().buckets, slot as int, pivot);
      
      var childrenReplaced := Replace1with2(self.children.value, left_childref, right_childref, slot);
      inout self.children := Some(childrenReplaced);

      ghost var a := self.I();
      assert a == b;
    }

    shared method cutoffNodeAndKeepLeftInternal(pivot: Key) 
    returns (cLeft: uint64, pivots: Pivots.PivotTable, edges: Translations.EdgeTable, children: Option<seq<BT.G.Reference>>)
    requires Inv()
    requires BT.WFNode(I())
    requires Pivots.ValidLeftCutOffKey(pivotTable, pivot)
    ensures cLeft as int == Pivots.CutoffForLeft(pivotTable, pivot)
    ensures pivots == BT.CutoffNodeAndKeepLeft(I(), pivot).pivotTable
    ensures edges ==  BT.CutoffNodeAndKeepLeft(I(), pivot).edgeTable
    ensures children ==  BT.CutoffNodeAndKeepLeft(I(), pivot).children
    {
      BT.reveal_CutoffNodeAndKeepLeft();
      cLeft := Pivots.ComputeCutoffForLeft(this.pivotTable, pivot);
      pivots := Pivots.ComputeSplitLeft(this.pivotTable, pivot, cLeft);
      edges := ComputeSplitLeftEdges(this.edgeTable, this.pivotTable, pivots, pivot, cLeft);
      children := if this.children.Some? then Some(this.children.value[.. cLeft + 1]) else None;
    }

    shared method CutoffNodeAndKeepLeft(pivot: Key) returns (linear node: Node)
    requires Inv()
    requires BT.WFNode(I())
    requires Pivots.ValidLeftCutOffKey(pivotTable, pivot)
    ensures node.Inv()
    ensures node.I() == BT.CutoffNodeAndKeepLeft(I(), pivot);
    {
      var cLeft, leftPivots, leftEdges, leftChildren := this.cutoffNodeAndKeepLeftInternal(pivot);
      BT.reveal_CutoffNodeAndKeepLeft();

      WeightBucketLeBucketList(MutBucket.ILseq(this.buckets), cLeft as int);  
      linear var splitBucket := lseq_peek(buckets, cLeft).SplitLeft(pivot);
      linear var slice := MutBucket.CloneSeq(this.buckets, 0, cLeft); // TODO clone not necessary?
      linear var leftBuckets := InsertLSeq(slice, splitBucket, cLeft);
      node := Node(leftPivots, leftEdges, leftChildren, leftBuckets);
    }

    shared method cutoffNodeAndKeepRightInternal(pivot: Key) 
    returns (cRight: uint64, pivots: Pivots.PivotTable, edges: Translations.EdgeTable, children: Option<seq<BT.G.Reference>>)
    requires Inv()
    requires BT.WFNode(I())
    requires Pivots.BoundedKey(pivotTable, pivot)
    ensures cRight as int == Pivots.CutoffForRight(pivotTable, pivot)
    ensures pivots == BT.CutoffNodeAndKeepRight(I(), pivot).pivotTable
    ensures edges ==  BT.CutoffNodeAndKeepRight(I(), pivot).edgeTable
    ensures children ==  BT.CutoffNodeAndKeepRight(I(), pivot).children
    {
      BT.reveal_CutoffNodeAndKeepRight();
      cRight := Pivots.ComputeCutoffForRight(this.pivotTable, pivot);
      pivots := Pivots.ComputeSplitRight(this.pivotTable, pivot, cRight);
      edges := ComputeSplitRightEdges(this.edgeTable, this.pivotTable, pivots, pivot, cRight);
      children := if this.children.Some? then Some(this.children.value[cRight ..]) else None;
    }

    shared method CutoffNodeAndKeepRight(pivot: Key) returns (linear node: Node)
    requires Inv()
    requires BT.WFNode(I())
    requires Pivots.BoundedKey(pivotTable, pivot)
    ensures node.Inv()
    ensures node.I() == BT.CutoffNodeAndKeepRight(I(), pivot);
    {
      var cRight, rightPivots, rightEdges, rightChildren := this.cutoffNodeAndKeepRightInternal(pivot);
      BT.reveal_CutoffNodeAndKeepRight();

      WeightBucketLeBucketList(MutBucket.ILseq(this.buckets), cRight as int);
      linear var splitBucket := lseq_peek(buckets, cRight).SplitRight(pivot);
      linear var slice := MutBucket.CloneSeq(buckets, cRight + 1, lseq_length_raw(buckets));
      linear var rightBuckets := InsertLSeq(slice, splitBucket, 0);
      node := Node(rightPivots, rightEdges, rightChildren, rightBuckets);
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

    linear method SplitChild(num_children_left: uint64) returns (linear left: Node, linear right: Node)
    requires Inv()
    requires |pivotTable| < Uint64UpperBound()
    requires 0 <= num_children_left as int - 1 <= |pivotTable| - 2
    requires 0 <= num_children_left as int <= |edgeTable|
    requires children.Some? ==> 0 <= num_children_left as int <= |children.value|
    requires 0 <= num_children_left as int <= |buckets|
    ensures left.Inv()
    ensures right.Inv()
    ensures left.I() == BT.SplitChildLeft(I(), num_children_left as int)
    ensures right.I() == BT.SplitChildRight(I(), num_children_left as int)
    {
      linear var Node(pivots, edges, children, buckets) := this;
      linear var leftbuckets, rightbuckets := MutBucket.SplitSeq(buckets, num_children_left);

      left := Node(
        pivots[ .. num_children_left + 1 ],
        edges[ .. num_children_left ],
        if children.Some? then Some(children.value[ .. num_children_left ]) else None,
        leftbuckets
      );

      right := Node(
        pivots[ num_children_left .. ],
        edges[ num_children_left .. ],
        if children.Some? then Some(children.value[ num_children_left .. ]) else None,
        rightbuckets
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

    static method RestrictAndTranslateChildBuckets(shared parent: Node, shared child: Node, slot: uint64, 
      parentprefix: Key, childprefix: Key, lbound: Key, ubound: Pivots.Element, 
      cLeft: uint64, cRight: uint64) returns (linear buckets: lseq<MutBucket>)
    requires parent.Inv()
    requires child.Inv()
    requires BT.WFNode(parent.I())
    requires BT.WFNode(child.I())
    requires 0 <= slot as int < Pivots.NumBuckets(parent.pivotTable)
    requires Translations.ParentKeysInChildRange(parent.pivotTable, parent.edgeTable, child.pivotTable, slot as int)
    requires parent.edgeTable[slot].Some?
    requires parentprefix == Translations.PivotLcp(parent.pivotTable[slot], parent.pivotTable[slot+1])
    requires childprefix == parent.edgeTable[slot].value;
    requires (Pivots.KeyToElement(lbound), ubound) == Translations.TranslatePivotPairInternal(parent.pivotTable[slot], 
        parent.pivotTable[slot+1], parentprefix, childprefix)
    requires ubound.Element?
    requires cLeft as int == Pivots.CutoffForLeft(child.I().pivotTable, ubound.e)
    requires cRight as int == Pivots.CutoffForRight(child.I().pivotTable, lbound)
    requires 0 <= cRight as int <= cLeft as int < |child.buckets|
    ensures MutBucket.InvLseq(buckets)
    ensures MutBucket.ILseq(buckets) == BT.RestrictAndTranslateChild(parent.I(), child.I(), slot as int).buckets
    {
      BT.reveal_CutoffNode();
      BT.reveal_CutoffNodeAndKeepLeft();
      BT.reveal_CutoffNodeAndKeepRight();

      ghost var node1 := BT.CutoffNodeAndKeepLeft(child.I(), ubound.e);
      ghost var node2 := BT.CutoffNodeAndKeepRight(node1, lbound);
      ghost var node := BT.CutoffNode(child.I(), lbound, Some(ubound.e));
      assert node2 == node;

      if cRight == cLeft {
        linear var leftbucket := lseq_peek(child.buckets, cLeft).SplitLeft(ubound.e);
        linear var bucket := leftbucket.SplitRight(lbound);

        assert |node.buckets| == 1;
        assert node.buckets[0] == bucket.I();
 
        buckets := ComputeTranslateSingleBucketList(bucket, childprefix, parentprefix);
        var _ := FreeMutBucket(leftbucket);
      } else {
        linear var upperbucket := lseq_peek(child.buckets, cLeft).SplitLeft(ubound.e); 
        linear var lowerbucket := lseq_peek(child.buckets, cRight).SplitRight(lbound);

        assert 0 <= cRight+1 <= cLeft;
        assert node1.buckets == child.I().buckets[..cLeft] + [upperbucket.I()];
        assert node1.buckets[cLeft] == upperbucket.I();
        assert node2.buckets == [lowerbucket.I()] + node1.buckets[cRight+1..];

        if cRight+1 == cLeft {
          assert |node1.buckets[cRight+1..]| == 1;
          assert node1.buckets[cRight+1] == node1.buckets[cLeft] == upperbucket.I();
        }
        assert node1.buckets[cRight+1..] == child.I().buckets[cRight+1..cLeft] + [upperbucket.I()];
        assert node.buckets == [lowerbucket.I()] + child.I().buckets[cRight+1..cLeft] + [upperbucket.I()];

        buckets := ComputeTranslateCutOffNodeBuckets(child.buckets, lowerbucket,
            upperbucket, childprefix, parentprefix, cLeft, cRight);
      }
    }

    static method RestrictAndTranslateChild(shared parent: Node, shared child: Node, slot: uint64)
    returns (linear newchild: Node)
    requires parent.Inv()
    requires child.Inv()
    requires BT.WFNode(parent.I())
    requires BT.WFNode(child.I())
    requires 0 <= slot as int < Pivots.NumBuckets(parent.pivotTable)
    requires Translations.ParentKeysInChildRange(parent.pivotTable, parent.edgeTable, child.pivotTable, slot as int)
    ensures newchild.Inv()
    ensures newchild.I() == BT.RestrictAndTranslateChild(parent.I(), child.I(), slot as int)
    {
      if parent.edgeTable[slot].None? {
        var lbound := Pivots.ComputeGetKey(parent.pivotTable, slot);
        if parent.pivotTable[slot+1].Max_Element? {
          newchild := child.CutoffNode(lbound, None);
        } else {
          newchild := child.CutoffNode(lbound, Some(parent.pivotTable[slot+1].e));
        }
      } else {
        var parentprefix := ComputePivotLcp(parent.pivotTable[slot], parent.pivotTable[slot+1]);
        var childprefix := parent.edgeTable[slot].value;

        var lbound, ubound := ComputeTranslatePivotPair(parent.pivotTable[slot].e, 
            parent.pivotTable[slot+1], parentprefix, childprefix);

        if ubound.Max_Element? {
          BT.reveal_CutoffNodeAndKeepRight();
          var cRight, rightPivots, rightEdges, rightChildren := child.cutoffNodeAndKeepRightInternal(lbound);

          Translations.TranslatePivotPairRangeProperty(parent.pivotTable[slot], parent.pivotTable[slot+1], parentprefix, childprefix);
          var newpivots := ComputeTranslatePivots(rightPivots, childprefix, parentprefix, parent.pivotTable[slot+1]);
          var newedges := ComputeTranslateEdges(rightEdges, rightPivots);

          linear var splitBucket := lseq_peek(child.buckets, cRight).SplitRight(lbound);
          linear var translatedbuckets := ComputeTranslateCutOffKeepRightBuckets(child.buckets, splitBucket, childprefix, parentprefix, cRight);
          BT.reveal_CutoffNode();

          newchild := Node.Alloc(newpivots, newedges, rightChildren, translatedbuckets);
        } else {
          var cLeft, leftPivots, leftEdges, leftChildren := child.cutoffNodeAndKeepLeftInternal(ubound.e);

          var cRight := Pivots.ComputeCutoffForRight(leftPivots, lbound);
          var pivots := Pivots.ComputeSplitRight(leftPivots, lbound, cRight);
          var edges := ComputeSplitRightEdges(leftEdges, leftPivots, pivots, lbound, cRight);
          var children := if leftChildren.Some? then Some(leftChildren.value[cRight ..]) else None;

          BT.reveal_CutoffNode();
          BT.reveal_CutoffNodeAndKeepLeft();
          BT.reveal_CutoffNodeAndKeepRight();

          assert 0 <= cRight as int < |leftPivots|-1;
          assert cLeft as int == |leftPivots| - 2;
          assert 0 <= cRight <= cLeft;

          Translations.TranslatePivotPairRangeProperty(parent.pivotTable[slot], parent.pivotTable[slot+1], parentprefix, childprefix);
          var newpivots := ComputeTranslatePivots(pivots, childprefix, parentprefix, parent.pivotTable[slot+1]);
          var newedges := ComputeTranslateEdges(edges, pivots);

          linear var translatedbuckets := RestrictAndTranslateChildBuckets(parent, child, slot, parentprefix, childprefix, lbound, ubound, cLeft, cRight);
          newchild := Node(newpivots, newedges, children, translatedbuckets);

          assert MutBucket.ILseq(translatedbuckets) == BT.RestrictAndTranslateChild(parent.I(), child.I(), slot as int).buckets;
          assert newchild.Inv();
          assert newchild.I() == BT.RestrictAndTranslateChild(parent.I(), child.I(), slot as int);
        }
      }
    }

    static method RestrictAndTranslateNode(shared node: Node, from: Key, to: Key, fromend: Pivots.Element)
    returns (pivots: Pivots.PivotTable, edges: Translations.EdgeTable, children: Option<seq<BT.G.Reference>>, linear buckets: lseq<MutBucket>)
    requires node.Inv()
    requires BT.WFNode(node.I())
    requires Pivots.ContainsAllKeys(node.pivotTable)
    requires node.children.Some?
    requires to != []
    requires fromend == Translations.ShortestUncommonPrefix(from, |from|)
    ensures MutBucket.InvLseq(buckets)
    ensures pivots == BT.RestrictAndTranslateNode(node.I(), from, to).pivotTable
    ensures edges == BT.RestrictAndTranslateNode(node.I(), from, to).edgeTable
    ensures children == BT.RestrictAndTranslateNode(node.I(), from, to).children
    ensures MutBucket.ILseq(buckets) == BT.RestrictAndTranslateNode(node.I(), from, to).buckets
    {
      var toend := ComputeShortestUncommonPrefix(to);

      BT.reveal_CutoffNode();
      BT.reveal_CutoffNodeAndKeepLeft();
      BT.reveal_CutoffNodeAndKeepRight();

      var cRight, rightPivots, rightEdges, rightChildren;
      Pivots.ContainsAllKeysImpliesBoundedKey(node.pivotTable, from);

      if fromend.Max_Element? {
        cRight, rightPivots, rightEdges, rightChildren := node.cutoffNodeAndKeepRightInternal(from);        
      } else {
        var cLeft, leftPivots, leftEdges, leftChildren := node.cutoffNodeAndKeepLeftInternal(fromend.e);
        cRight := Pivots.ComputeCutoffForRight(leftPivots, from);
        rightPivots := Pivots.ComputeSplitRight(leftPivots, from, cRight);
        rightEdges := ComputeSplitRightEdges(leftEdges, leftPivots, rightPivots, from, cRight);
        rightChildren := if leftChildren.Some? then Some(leftChildren.value[cRight ..]) else None;
      }

      Translations.PrefixOfLcpIsPrefixOfKeys(Pivots.KeyToElement(from), fromend, from);
      Pivots.Keyspace.reveal_IsStrictlySorted();

      ghost var e := Translations.TranslateElement(rightPivots[|rightPivots|-2], from, to);
      assert Pivots.Keyspace.lt(e, toend) by {
        if toend.Element? {
          Translations.KeyWithPrefixLt(to, toend.e, e.e);
        }
      }

      pivots := ComputeTranslatePivots(rightPivots, from, to, toend);
      edges := ComputeTranslateEdges(rightEdges, rightPivots);
      children := rightChildren;
      buckets := MutBucket.EmptySeq((|pivots|-1) as uint64);
    }

    static method CloneNewRoot(shared node: Node, from: Key, to: Key)
    returns (linear rootopt: lOption<Node>)
    requires to != []
    requires node.Inv()
    requires BT.WFNode(node.I())
    requires node.children.Some?
    requires Pivots.ContainsAllKeys(node.pivotTable)
    ensures rootopt.lNone? ==> (
        !BT.ValidCloneBucketList(node.I(), from)
       || |BT.CloneNewRoot(node.I(), from, to).children.value| > MaxNumChildren())
    ensures rootopt.lSome? ==> (
      && BT.ValidCloneBucketList(node.I(), from)
      && rootopt.value.Inv()
      && rootopt.value.I() == BT.CloneNewRoot(node.I(), from, to)
      && |rootopt.value.I().children.value| <= MaxNumChildren())
    {
      var fromend := ComputeShortestUncommonPrefix(from);
      Pivots.ContainsAllKeysImpliesBoundedKey(node.pivotTable, from);
      var start := Pivots.ComputeRoute(node.pivotTable, from);
      var end;
      if fromend.Max_Element? {
        end := lseq_length_as_uint64(node.buckets);
      } else {
        end := Pivots.ComputeRoute(node.pivotTable, fromend.e);
        end := end + 1;
      }

      var validbucketlist := MutBucket.BucketsNoKeyWithPrefix(node.buckets, from, start, end);
      if !validbucketlist {
        rootopt := lNone;
      } else {
        var toPivots, toEdges, toChildren;
        linear var toBuckets;

        toPivots, toEdges, toChildren, toBuckets := RestrictAndTranslateNode(node, from, to, fromend);
        Pivots.ContainsAllKeysImpliesBoundedKey(node.pivotTable, to);
        var cLeft, leftPivots, leftEdges, leftChildren := node.cutoffNodeAndKeepLeftInternal(to);

        var toend := toPivots[|toPivots|-1];
        if toend.Max_Element? {
          if |leftChildren.value + toChildren.value| as uint64 <= MaxNumChildrenUint64() {
            var newpivots := leftPivots[..|leftPivots|-1] + toPivots;
            var newedges := leftEdges + toEdges;
            var newchildren := Some(leftChildren.value + toChildren.value);

            linear var splitBucket := lseq_peek(node.buckets, cLeft).SplitLeft(to);
            linear var lbuckets := MutBucket.CloneSeq(node.buckets, 0, cLeft);
            BT.reveal_CutoffNodeAndKeepLeft();

            linear var newbuckets := MutBucket.BucketListConcat(lbuckets, splitBucket, toBuckets);
            linear var node := Alloc(newpivots, newedges, newchildren, newbuckets);
            rootopt := lSome(node);
          } else {
            var _ := FreeMutBucketSeq(toBuckets);
            rootopt := lNone;
          }
        } else {
          var cRight, rightPivots, rightEdges, rightChildren := node.cutoffNodeAndKeepRightInternal(toend.e);
          if |leftChildren.value + toChildren.value + rightChildren.value| as uint64 <= MaxNumChildrenUint64() {
            var newpivots := leftPivots[..|leftPivots|-1] + toPivots + rightPivots[1..];
            var newedges := leftEdges + toEdges + rightEdges;
            var newchildren := Some(leftChildren.value + toChildren.value + rightChildren.value);

            ghost var lnode := BT.CutoffNodeAndKeepLeft(node.I(), to);
            ghost var rnode := BT.CutoffNodeAndKeepRight(node.I(), toend.e);

            linear var leftbucket := lseq_peek(node.buckets, cLeft).SplitLeft(to);
            linear var lbuckets := MutBucket.CloneSeq(node.buckets, 0, cLeft);
            BT.reveal_CutoffNodeAndKeepLeft(); 
            assert lnode.buckets == MutBucket.ILseq(lbuckets) + [leftbucket.I()];

            linear var rightbucket := lseq_peek(node.buckets, cRight).SplitRight(toend.e);
            linear var rbuckets := MutBucket.CloneSeq(node.buckets, cRight + 1, lseq_length_raw(node.buckets));
            BT.reveal_CutoffNodeAndKeepRight(); 

            assert MutBucket.ILseq(node.buckets)[cRight+1..|node.buckets|] == MutBucket.ILseq(node.buckets)[cRight+1..];
            assert BT.CloneNewRoot(node.I(), from, to).buckets == 
              MutBucket.ILseq(lbuckets) + [leftbucket.I()] + MutBucket.ILseq(toBuckets) + [rightbucket.I()] + MutBucket.ILseq(rbuckets);
            
            linear var newbuckets := MutBucket.BucketListConcat3(lbuckets, leftbucket, toBuckets, rightbucket, rbuckets);
            linear var node := Alloc(newpivots, newedges, newchildren, newbuckets);
            rootopt := lSome(node);
          } else {
            var _ := FreeMutBucketSeq(toBuckets);
            rootopt := lNone;
          }
        }
      }
    }
  }

  function method FreeNode(linear node: Node) : ()
  requires node.Inv()
  {
    linear var Node(_, _, _, buckets) := node;
    FreeMutBucketSeq(buckets)
  }
}
