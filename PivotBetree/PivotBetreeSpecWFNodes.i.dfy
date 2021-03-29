// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PivotBetreeSpec.i.dfy"

module PivotBetreeSpecWFNodes {
  import opened Options
  import opened PivotBetreeSpec`Internal
  import opened Maps
  import opened Sequences
  import opened BucketWeights
  import opened BucketsLib
  import opened BucketMaps
  import opened Bounds
  import opened ValueMessage
  import opened KeyType
  import opened BoundedPivotsLib
  import opened TranslationLib

  import BucketFlushModel
  import MapSeqs

  import MS = MapSpec
  import Lexicographic_Byte_Order

  lemma ValidFlushWritesWFNodes(f: NodeFlush)
  requires PivotBetreeSpec.ValidFlush(f)
  requires forall i | 0 <= i < |FlushReads(f)| :: WFNode(FlushReads(f)[i].node)
  ensures forall i | 0 <= i < |FlushOps(f)| :: WFNode(FlushOps(f)[i].node)
  ensures WFNode(FlushOps(f)[0].node)
  ensures WFNode(FlushOps(f)[1].node)
  {
    assert WFNode(FlushReads(f)[0].node);
    assert WFNode(FlushReads(f)[1].node);
    assert WFNode(FlushOps(f)[0].node);

    var child' := RestrictAndTranslateChild(f.parent, f.child, f.slot_idx);
    BucketFlushModel.partialFlushWeightBound(
        f.parent.buckets[f.slot_idx], child'.pivotTable, child'.buckets);
    WeightBucketListShrinkEntry(f.parent.buckets, f.slot_idx, f.newparent.buckets[f.slot_idx]);
    assert WFNode(FlushOps(f)[1].node);
  }

  lemma ValidFlushWritesInvNodes(f: NodeFlush)
  requires PivotBetreeSpec.ValidFlush(f)
  requires forall i | 0 <= i < |FlushReads(f)| :: InvNode(FlushReads(f)[i].node)
  ensures forall i | 0 <= i < |FlushOps(f)| :: InvNode(FlushOps(f)[i].node)
  ensures InvNode(FlushOps(f)[0].node)
  ensures InvNode(FlushOps(f)[1].node)
  {
    assert InvNode(FlushReads(f)[0].node);
    assert InvNode(FlushReads(f)[1].node);

    ValidFlushWritesWFNodes(f);

    var child' := RestrictAndTranslateChild(f.parent, f.child, f.slot_idx);
    RestrictAndTranslateWFProperWellMarshalled(f.parent, f.child, f.slot_idx);
    assert child'.pivotTable[0] == f.parent.pivotTable[f.slot_idx];
    assert Last(child'.pivotTable) == f.parent.pivotTable[f.slot_idx+1];

    var _ := BucketFlushModel.partialFlushCorrect(
        f.parent.buckets[f.slot_idx], child'.pivotTable, child'.buckets);
    BucketFlushModel.partialFlushPreservesSorted(
        f.parent.buckets[f.slot_idx], child'.pivotTable, child'.buckets);

    reveal_BucketIntersect();
    forall i | 0 <= i < |f.newparent.buckets|
    ensures WFBucketAt(f.newparent.buckets[i], f.newparent.pivotTable, i)
    {
      assert WFBucketAt(f.parent.buckets[i], f.parent.pivotTable, i);
      if i == f.slot_idx {
        forall j | 0 <= j < |f.newparent.buckets[i].keys|
        ensures BoundedKey(f.newparent.pivotTable, f.newparent.buckets[i].keys[j])
        ensures Route(f.newparent.pivotTable, f.newparent.buckets[i].keys[j]) == i
        {
          MapSeqs.MapMapsIndex(f.newparent.buckets[i].keys, f.newparent.buckets[i].msgs, j);
          reveal_BucketComplement();
          var t := MapSeqs.GetIndex(f.parent.buckets[i].keys, f.parent.buckets[i].msgs, 
              f.newparent.buckets[i].keys[j]);
        }
        assert WFBucketAt(f.newparent.buckets[i], f.newparent.pivotTable, i);
      } else {
        assert f.parent.buckets[i] == f.newparent.buckets[i];
        assert f.parent.pivotTable == f.newparent.pivotTable;
        assert WFBucketAt(f.newparent.buckets[i], f.newparent.pivotTable, i);
      }
      //assert (set k | k in f.parent.buckets[i].keys) == f.parent.buckets[i].as_map().Keys;
      //assert (set k | k in f.newparent.buckets[i].keys) == f.newparent.buckets[i].as_map().Keys;
    }

    forall i | 0 <= i < |f.newchild.buckets|
    ensures WFBucketAt(f.newchild.buckets[i], f.newchild.pivotTable, i)
    {
      assert WFBucketAt(child'.buckets[i], child'.pivotTable, i);
      forall j | 0 <= j < |f.newchild.buckets[i].keys|
      ensures BoundedKey(f.newchild.pivotTable, f.newchild.buckets[i].keys[j])
      ensures Route(f.newchild.pivotTable, f.newchild.buckets[i].keys[j]) == i
      {
        MapSeqs.MapMapsIndex(f.newchild.buckets[i].keys, f.newchild.buckets[i].msgs, j);
        reveal_BucketIntersect();
        //var t := MapSeqs.GetIndex(f.child.buckets[i].keys, f.child.buckets[i].msgs, 
        //    newchild.buckets[i].keys[j]);
      }
    }

    assert InvNode(f.newparent);
    assert InvNode(f.newchild);
  }

  lemma RestrictAndTranslateWFProperWellMarshalled(parent: G.Node, child: G.Node, slot: int)
  requires 0 <= slot < NumBuckets(parent.pivotTable)
  requires InvNode(parent)
  requires InvNode(child)
  requires ParentKeysInChildRange(parent, child, slot)
  ensures var child' := RestrictAndTranslateChild(parent, child, slot);
    && WFBucketListProper(child'.buckets, child'.pivotTable)
    && BucketListWellMarshalled(child'.buckets)
  {
    if parent.edgeTable[slot].None? {
      var lbound := getlbound(parent, slot);
      var ubound := getubound(parent, slot);

      ContainsRangeImpliesBoundedKey(child.pivotTable, parent.pivotTable[slot], parent.pivotTable[slot+1]);
      assert BoundedKey(child.pivotTable, lbound);
      var child' := CutoffNode(child, lbound, ubound);
      CutoffNodeWFProperWellMarshalled(child, lbound, ubound);
    } else {
      var (lbound, ubound) := TranslatePivotPair(parent.pivotTable, parent.edgeTable, slot);
      var lboundkey : Key := lbound.e;
      var uboundkey := if ubound.Element? then (var k: Key := ubound.e; Some(k)) else None;
      var child1 := CutoffNode(child, lboundkey, uboundkey);
      CutoffNodeWFProperWellMarshalled(child, lboundkey, uboundkey);

      var parentprefix := PivotLcp(parent.pivotTable[slot], parent.pivotTable[slot+1]);
      var childprefix := parent.edgeTable[slot].value;

      var child' := RestrictAndTranslateChild(parent, child, slot);
      assert forall i | 0 <= i < |child1.buckets| :: 
        (forall k | k in child1.buckets[i].keys :: InBetween(lbound, ubound, k));
      SortedBucketListStaysSorted(child1.buckets, childprefix, parentprefix);
      assert BucketListWellMarshalled(child'.buckets);

      forall i | 0 <= i < |child'.buckets|
      ensures WFBucketAt(child'.buckets[i], child'.pivotTable, i)
      {
        forall j | 0 <= j < |child'.buckets[i].keys|
        ensures BoundedKey(child'.pivotTable, child'.buckets[i].keys[j])
        ensures Route(child'.pivotTable, child'.buckets[i].keys[j]) == i
        {
          var key : Key := child'.buckets[i].keys[j];
          var oldkey : Key := child1.buckets[i].keys[j];
          assert Route(child1.pivotTable, oldkey) == i;

          var lpivot := child'.pivotTable[i].e;
          var oldlpivot := child1.pivotTable[i].e;

          PrefixLteProperties(childprefix, oldlpivot, oldkey);
          PrefixLteProperties(parentprefix, lpivot, key);

          assert Keyspace.lte(child'.pivotTable[i], KeyToElement(key));
          Keyspace.transitivity(child'.pivotTable[0], child'.pivotTable[i], KeyToElement(key));
          assert Keyspace.lte(child'.pivotTable[0], KeyToElement(key));

          if i+1 == NumBuckets(child'.pivotTable) {
            assert InBetween(child1.pivotTable[0], Last(child1.pivotTable), oldkey);
            if child'.pivotTable[i+1].Element? {
              assert key == parentprefix + oldkey[|childprefix|..];
              assert Keyspace.lt(Keyspace.Element(key), Last(child'.pivotTable)) by {
                TranslatePivotPairRangeProperty(parent.pivotTable[slot], 
                    parent.pivotTable[slot+1], parentprefix, childprefix);
              }
            }
          } else {
            var rpivot := child'.pivotTable[i+1].e;
            var oldrpivot := child1.pivotTable[i+1].e;

            PrefixLteProperties(childprefix, oldrpivot, oldkey);
            PrefixLteProperties(parentprefix, rpivot, key);
            assert Keyspace.lt(KeyToElement(key), child'.pivotTable[i+1]);
          }
          assert BoundedKey(child'.pivotTable, key);
        }
      }
    }
  }

  lemma KeepLeftWFProperWellMarshalled(
      node: G.Node,
      pivot: Key)
  requires InvNode(node)
  requires ValidLeftCutOffKey(node.pivotTable, pivot)
  ensures
    var node' := CutoffNodeAndKeepLeft(node, pivot);
    && WFBucketListProper(node'.buckets, node'.pivotTable)
    && BucketListWellMarshalled(node'.buckets)
  {
    reveal_CutoffNodeAndKeepLeft();
    var cLeft := CutoffForLeft(node.pivotTable, pivot);
    WFProperSplitBucketListLeft(node.buckets, node.pivotTable, cLeft, pivot);

    var node' := CutoffNodeAndKeepLeft(node, pivot);
    assert BucketListWellMarshalled(node'.buckets) by {
      reveal_SplitBucketLeft();
      Lexicographic_Byte_Order.reveal_IsStrictlySorted();
    }
  }

  lemma KeepRightWFProperWellMarshalled(
      node: G.Node,
      pivot: Key)
  requires WFNode(node)
  requires BoundedKey(node.pivotTable, pivot)
  requires WFBucketListProper(node.buckets, node.pivotTable);
  requires BucketListWellMarshalled(node.buckets)
  ensures
    var node' := CutoffNodeAndKeepRight(node, pivot);
    && WFBucketListProper(node'.buckets, node'.pivotTable)
    && BucketListWellMarshalled(node'.buckets)
  {
    reveal_SplitBucketRight();
    reveal_CutoffNodeAndKeepRight();
    Lexicographic_Byte_Order.reveal_IsStrictlySorted();

    var cRight := CutoffForRight(node.pivotTable, pivot);
    assert BucketWellMarshalled(node.buckets[cRight]);
    WFProperSplitBucketListRight(node.buckets, node.pivotTable, cRight, pivot);
  }

  lemma CutoffNodeWFProperWellMarshalled(
      node: G.Node,
      lpivot: Key,
      rpivot: Option<Key>)
  requires InvNode(node)
  requires ValidSplitKey(node, lpivot, rpivot)
  ensures
    var node' := CutoffNode(node, lpivot, rpivot);
    && WFBucketListProper(node'.buckets, node'.pivotTable)
    && BucketListWellMarshalled(node'.buckets)
  {
    reveal_CutoffNode();
    var node' := CutoffNode(node, lpivot, rpivot);

    assert WFBucketListProper(node.buckets, node.pivotTable);
    match rpivot {
      case None => {
        KeepRightWFProperWellMarshalled(node, lpivot);
      }
      case Some(rpivot) => {
        var node1 := CutoffNodeAndKeepLeft(node, rpivot);
        var node' := CutoffNodeAndKeepRight(node1, lpivot);
      
        KeepLeftWFProperWellMarshalled(node, rpivot);
        KeepRightWFProperWellMarshalled(node1, lpivot);
      }
    }
  }

  lemma ValidSplitWritesWFNodes(f: NodeFusion)
  requires ValidSplit(f)
  requires forall i | 0 <= i < |SplitReads(f)| :: WFNode(SplitReads(f)[i].node)
  ensures WFNode(f.split_parent);
  ensures WFNode(f.left_child);
  ensures WFNode(f.right_child);
  ensures forall i | 0 <= i < |SplitOps(f)| :: WFNode(SplitOps(f)[i].node)
  {
    assert WFNode(SplitReads(f)[0].node);
    assert WFNode(SplitReads(f)[1].node);

    var child := RestrictAndTranslateChild(f.fused_parent, f.fused_child, f.slot_idx);

    WFPivotsInsert(f.fused_parent.pivotTable, f.slot_idx+1, f.pivot);
    WeightSplitBucketInList(f.fused_parent.buckets, f.slot_idx, f.pivot);
    WFSplitBucketInList(f.fused_parent.buckets, f.slot_idx+1, f.pivot, f.fused_parent.pivotTable);

    WFSlice(child.pivotTable, 0, f.num_children_left+1);
    WFSuffix(child.pivotTable, f.num_children_left);

    WeightBucketListSlice(child.buckets, 0, f.num_children_left);
    WeightBucketListSuffix(child.buckets, f.num_children_left);

    assert WFEdges(f.split_parent.edgeTable, f.split_parent.pivotTable) by {
      assert WFEdges(f.fused_parent.edgeTable, f.fused_parent.pivotTable);
      assert forall i | f.slot_idx+1 < i < |f.split_parent.pivotTable| :: f.split_parent.pivotTable[i] == f.fused_parent.pivotTable[i-1];
      assert forall i | f.slot_idx+1 < i < |f.split_parent.edgeTable| :: f.split_parent.edgeTable[i] == f.fused_parent.edgeTable[i-1];
    }
  
    assert WFNode(f.split_parent);
    assert WFNode(f.left_child);
    assert WFNode(f.right_child);
  }

  lemma ValidSplitWritesInvNodes(f: NodeFusion)
  requires ValidSplit(f)
  requires forall i | 0 <= i < |SplitReads(f)| :: InvNode(SplitReads(f)[i].node)
  ensures InvNode(f.split_parent);
  ensures InvNode(f.left_child);
  ensures InvNode(f.right_child);
  ensures forall i | 0 <= i < |SplitOps(f)| :: InvNode(SplitOps(f)[i].node)
  {
    assert InvNode(SplitReads(f)[0].node);
    assert InvNode(SplitReads(f)[1].node);

    ValidSplitWritesWFNodes(f);

    var child := RestrictAndTranslateChild(f.fused_parent, f.fused_child, f.slot_idx);
    RestrictAndTranslateWFProperWellMarshalled(f.fused_parent, f.fused_child, f.slot_idx);

    WFPivotsInsert(f.fused_parent.pivotTable, f.slot_idx+1, f.pivot);
    WFProperSplitBucketInList(f.fused_parent.buckets, f.slot_idx+1, f.pivot, f.fused_parent.pivotTable);

    assert BucketListWellMarshalled(f.split_parent.buckets) by {
      WellMarshalledSplitBucketInList(
          f.fused_parent.buckets, f.slot_idx, f.pivot);
    }
    assert InvNode(f.split_parent);

    WFSlice(child.pivotTable, 0, f.num_children_left+1);
    WFSuffix(child.pivotTable, f.num_children_left);

    BucketListHasWFBucketAtIdenticalSlice(child.buckets, child.pivotTable, f.left_child.buckets, f.left_child.pivotTable, 0, |f.left_child.buckets| - 1, 0);
    assert child.buckets[f.num_children_left..] == f.right_child.buckets;
    BucketListHasWFBucketAtIdenticalSlice(child.buckets, child.pivotTable, f.right_child.buckets, f.right_child.pivotTable, 0, |f.right_child.buckets| - 1, -f.num_children_left);

    WeightBucketListSlice(child.buckets, 0, f.num_children_left);
    WeightBucketListSuffix(child.buckets, f.num_children_left);

    assert BucketListWellMarshalled(f.left_child.buckets) by {
      BucketListWellMarshalledSlice(child.buckets, 0, f.num_children_left);
    }
    assert BucketListWellMarshalled(f.right_child.buckets) by {
      BucketListWellMarshalledSlice(child.buckets, f.num_children_left, |child.buckets|);
    }
    assert InvNode(f.left_child);
    assert InvNode(f.right_child);
  }

  lemma ValidMergeWritesWFNodes(f: NodeFusion)
  requires ValidMerge(f)
  requires forall i | 0 <= i < |MergeReads(f)| :: WFNode(MergeReads(f)[i].node)
  ensures WFNode(f.fused_parent);
  ensures WFNode(f.fused_child);
  ensures forall i | 0 <= i < |MergeOps(f)| :: WFNode(MergeOps(f)[i].node)
  {
    assert WFNode(MergeReads(f)[0].node);
    assert WFNode(MergeReads(f)[1].node);
    assert WFNode(MergeReads(f)[2].node);

    var left_child := RestrictAndTranslateChild(f.split_parent, f.left_child, f.slot_idx);
    var right_child := RestrictAndTranslateChild(f.split_parent, f.right_child, f.slot_idx+1);

    WeightBucketListConcat(left_child.buckets, right_child.buckets);
    WeightMergeBucketsInListLe(f.split_parent.buckets, f.slot_idx);
    WFMergeBucketsInList(f.split_parent.buckets, f.slot_idx, f.split_parent.pivotTable);

    WFConcat3(left_child.pivotTable, f.pivot, right_child.pivotTable);
    WFConcatEdges(left_child.pivotTable, left_child.edgeTable, 
      right_child.pivotTable, right_child.edgeTable, f.fused_child.pivotTable);

    assert WFNode(f.fused_parent);
    assert WFNode(f.fused_child);
  }

  lemma ValidMergeInvNodeParent(f:NodeFusion)
  requires ValidMerge(f)
  requires InvNode(f.split_parent)
  requires WFNode(f.fused_parent)
  ensures InvNode(f.fused_parent);
  {
    WFPivotsRemoved(f.split_parent.pivotTable, f.slot_idx+1);
    assert forall i | 0 <= i <= f.slot_idx-1 :: f.fused_parent.buckets[i] == f.split_parent.buckets[i]
      by { reveal_MergeBucketsInList(); }
    assert forall i | f.slot_idx + 1 <= i <= |f.fused_parent.buckets| - 1 :: f.fused_parent.buckets[i] == f.split_parent.buckets[i+1]
      by { reveal_MergeBucketsInList(); }
    
    BucketListHasWFBucketAtIdenticalSlice(f.split_parent.buckets, f.split_parent.pivotTable, f.fused_parent.buckets, f.fused_parent.pivotTable, 0, f.slot_idx-1, 0);
    BucketListHasWFBucketAtIdenticalSlice(f.split_parent.buckets, f.split_parent.pivotTable, f.fused_parent.buckets, f.fused_parent.pivotTable, f.slot_idx + 1, |f.fused_parent.buckets| - 1, -1);

    WFProperMergeBucketsInList(f.split_parent.buckets, f.slot_idx, f.split_parent.pivotTable);
    WellMarshalledMergeBucketsInList(f.split_parent.buckets, f.slot_idx, f.split_parent.pivotTable);
  }

  lemma ValidMergeWritesInvNodes(f: NodeFusion)
  requires ValidMerge(f)
  requires forall i | 0 <= i < |MergeReads(f)| :: InvNode(MergeReads(f)[i].node)
  ensures InvNode(f.fused_parent);
  ensures InvNode(f.fused_child);
  ensures forall i | 0 <= i < |MergeOps(f)| :: InvNode(MergeOps(f)[i].node)
  {
    assert InvNode(MergeReads(f)[0].node);
    assert InvNode(MergeReads(f)[1].node);
    assert InvNode(MergeReads(f)[2].node);

    ValidMergeWritesWFNodes(f);

    var left_child := RestrictAndTranslateChild(f.split_parent, f.left_child, f.slot_idx);
    var right_child := RestrictAndTranslateChild(f.split_parent, f.right_child, f.slot_idx+1);

    RestrictAndTranslateWFProperWellMarshalled(f.split_parent, f.left_child, f.slot_idx);
    assert BucketListWellMarshalled(left_child.buckets) && WFBucketListProper(left_child.buckets, left_child.pivotTable); // reduce time
    RestrictAndTranslateWFProperWellMarshalled(f.split_parent, f.right_child, f.slot_idx+1);
    assert BucketListWellMarshalled(right_child.buckets) && WFBucketListProper(right_child.buckets, right_child.pivotTable); // reduce time

    WeightBucketListConcat(left_child.buckets, right_child.buckets);
    assert WFPivots(f.fused_child.pivotTable); // This fixes a time-out somehow. -- robj

    BucketListHasWFBucketAtIdenticalSlice(left_child.buckets, left_child.pivotTable, f.fused_child.buckets, f.fused_child.pivotTable, 0, |left_child.buckets| - 1, 0);
    BucketListHasWFBucketAtIdenticalSlice(right_child.buckets, right_child.pivotTable, f.fused_child.buckets, f.fused_child.pivotTable, |left_child.buckets|, |f.fused_child.buckets| - 1, |left_child.buckets|);

    ValidMergeInvNodeParent(f);
    assert InvNode(f.fused_parent);
    assert InvNode(f.fused_child);
  }

  lemma WFApplyRepivot(r: Repivot)
  requires ValidRepivot(r)
  ensures WFNode(ApplyRepivot(r))
  {
    PivotsHasAllKeys(r.pivots);
    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();
    WeightSplitBucketAdditive(r.leaf.buckets[0], r.pivot);
    var leaf'_buckets :=
        [
          SplitBucketLeft(r.leaf.buckets[0], r.pivot),
          SplitBucketRight(r.leaf.buckets[0], r.pivot)
        ];
    reveal_WeightBucketList();
    calc {
      WeightBucketList(leaf'_buckets);
      WeightBucketList([ SplitBucketLeft(r.leaf.buckets[0], r.pivot) ])
          + WeightBucket(SplitBucketRight(r.leaf.buckets[0], r.pivot));
      WeightBucketList([])
          + WeightBucket(SplitBucketLeft(r.leaf.buckets[0], r.pivot))
          + WeightBucket(SplitBucketRight(r.leaf.buckets[0], r.pivot));
      WeightBucket(SplitBucketLeft(r.leaf.buckets[0], r.pivot))
          + WeightBucket(SplitBucketRight(r.leaf.buckets[0], r.pivot));
    }
  }

  lemma bucket_msgs_in_seq(b: Bucket)
  requires PreWFBucket(b)
  ensures forall m :: m in b.as_map().Values ==> m in b.msgs
  {
    forall m | m in b.as_map().Values
    ensures m in b.msgs
    {
      var k :| k in b.as_map() && b.as_map()[k] == m;
      var i := MapSeqs.GetIndexOfVal(b.keys, b.msgs, k, m);
    }
  }

  lemma bucket_msgs_equiv(b: Bucket)
  requires PreWFBucket(b)
  requires Lexicographic_Byte_Order.IsStrictlySorted(b.keys)
  ensures forall k :: k in b.msgs <==> k in b.as_map().Values
  {
    forall i | 0 <= i < |b.msgs|
    ensures b.msgs[i] in b.as_map().Values
    {
      MapSeqs.MapMapsIndex(b.keys, b.msgs, i);
    }
    bucket_msgs_in_seq(b);
  }

  lemma bucket_keys_in_seq(b: Bucket)
  requires PreWFBucket(b)
  ensures forall k :: k in b.as_map() ==> k in b.keys
  {
    forall k | k in b.as_map()
    ensures k in b.keys
    {
      var i := MapSeqs.GetIndex(b.keys, b.msgs, k);
    }
  }

  lemma bucket_keys_equiv(b: Bucket)
  requires PreWFBucket(b)
  requires Lexicographic_Byte_Order.IsStrictlySorted(b.keys)
  ensures forall k :: k in b.keys <==> k in b.as_map()
  {
    forall i | 0 <= i < |b.keys|
    ensures b.keys[i] in b.as_map()
    {
      MapSeqs.MapMapsIndex(b.keys, b.msgs, i);
    }
    bucket_keys_in_seq(b);
  }

  lemma SplitMaps(b: Bucket, key: Key)
  requires PreWFBucket(b)
  requires Lexicographic_Byte_Order.IsStrictlySorted(b.keys)
  ensures
    var l := SplitBucketLeft(b, key);
    var r := SplitBucketRight(b, key);
    && (forall k | k in l.as_map() :: Lexicographic_Byte_Order.lt(k, key))
    && (forall k | k in r.as_map() :: Lexicographic_Byte_Order.lte(key, k))
    && MapDisjointUnion(l.as_map(), r.as_map()) == b.as_map()
  {
    var l := SplitBucketLeft(b, key);
    var r := SplitBucketRight(b, key);
    //var i := Lexicographic_Byte_Order.binarySearchIndexOfFirstKeyGte(b.keys, key);

    Lexicographic_Byte_Order.reveal_IsStrictlySorted();
    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();

    bucket_keys_equiv(b);
    bucket_keys_equiv(l);
    bucket_keys_equiv(r);

    /*forall k | k in l.as_map()
    ensures Keyspace.lt(k, b.keys[i])
    {
      var j :| 0 <= j < |l.keys| && l.keys[j] == k;
      assert Keyspace.lt(b.keys[j], b.keys[i]);
      assert l.keys[j] == b.keys[j];
    }*/

    MapSeqs.map_union_of_seq_concat(l.keys, l.msgs, r.keys, r.msgs);
    assert l.keys + r.keys == b.keys;
    assert l.msgs + r.msgs == b.msgs;
  }

  lemma InvApplyRepivot(r: Repivot)
  requires ValidRepivot(r)
  requires forall i | 0 <= i < |RepivotReads(r)| :: InvNode(RepivotReads(r)[i].node)
  ensures InvNode(ApplyRepivot(r))
  {
    assert InvNode(RepivotReads(r)[0].node);
    PivotsHasAllKeys(r.pivots);
    WFApplyRepivot(r);

    var leaf'_buckets := [
          SplitBucketLeft(r.leaf.buckets[0], r.pivot),
          SplitBucketRight(r.leaf.buckets[0], r.pivot)
        ];

    assert WFBucketAt(r.leaf.buckets[0], r.leaf.pivotTable, 0);
    SplitMaps(r.leaf.buckets[0], r.pivot);

    assert BucketWellMarshalled(leaf'_buckets[0]) by {
      Lexicographic_Byte_Order.reveal_IsStrictlySorted();
      reveal_SplitBucketLeft();
    }
    assert BucketWellMarshalled(leaf'_buckets[1]) by {
      Lexicographic_Byte_Order.reveal_IsStrictlySorted();
      reveal_SplitBucketRight();
    }

    bucket_keys_equiv(r.leaf.buckets[0]);
    bucket_keys_equiv(leaf'_buckets[0]);
    bucket_keys_equiv(leaf'_buckets[1]);
    
    assert WFBucketAt(leaf'_buckets[0], r.pivots, 0);
    assert WFBucketAt(leaf'_buckets[1], r.pivots, 1);
  }

  lemma ValidRepivotWFNodes(r: Repivot)
  requires ValidRepivot(r)
  requires forall i | 0 <= i < |RepivotReads(r)| :: WFNode(RepivotReads(r)[i].node)
  ensures forall i | 0 <= i < |RepivotOps(r)| :: WFNode(RepivotOps(r)[i].node)
  {
    assert WFNode(RepivotReads(r)[0].node);
    WFApplyRepivot(r);
  }

  lemma BucketInsertMaps(b: Bucket, key: Key, msg: Message)
  requires PreWFBucket(b)
  ensures
    var b' := BucketInsert(b, key, msg);
    var mergedMsg := Merge(msg, BucketGet(b.as_map(), key));
    && (mergedMsg == IdentityMessage() ==> b'.as_map() == MapRemove1(b.as_map(), key))
    && (mergedMsg != IdentityMessage() ==> b'.as_map() == b.as_map()[key := mergedMsg])
  {
  }

  lemma ValidInsertWritesWFNodes(ins: MessageInsertion)
  requires ValidInsertion(ins)
  requires forall i | 0 <= i < |InsertionReads(ins)| :: WFNode(InsertionReads(ins)[i].node)
  ensures forall i | 0 <= i < |InsertionOps(ins)| :: WFNode(InsertionOps(ins)[i].node)
  {
    assert WFNode(InsertionReads(ins)[0].node);
    var newroot := AddMessageToNode(ins.oldroot, ins.key, ins.msg);
    var i := Route(ins.oldroot.pivotTable, ins.key);
    var b := ins.oldroot.buckets[i];
    var b' := newroot.buckets[i];
    bucket_msgs_equiv(newroot.buckets[i]);
    bucket_msgs_in_seq(ins.oldroot.buckets[i]);
    BucketInsertMaps(ins.oldroot.buckets[i], ins.key, ins.msg);
    WeightBucketListInsert(ins.oldroot.buckets, ins.oldroot.pivotTable, ins.key, ins.msg);
    assert WFBucket(ins.oldroot.buckets[i]);
    forall j | 0 <= j < |newroot.buckets[i].msgs|
    ensures newroot.buckets[i].msgs[j] != IdentityMessage()
    {
      var m := newroot.buckets[i].msgs[j];
      assert m in b'.as_map().Values;
      var mergedMsg := Merge(ins.msg, BucketGet(b.as_map(), ins.key));
      if mergedMsg == IdentityMessage() {
        assert m in b.as_map().Values;
        assert m in b.msgs;
      } else {
        if m == IdentityMessage() {
          assert m in b.as_map().Values;
          assert m in b.msgs;
          assert false;
        }
      }
    }
    assert WFBucket(newroot.buckets[i]);
    assert WFNode(newroot);
  }

  lemma ValidInsertWritesInvNodes(ins: MessageInsertion)
  requires ValidInsertion(ins)
  requires forall i | 0 <= i < |InsertionReads(ins)| :: InvNode(InsertionReads(ins)[i].node)
  ensures forall i | 0 <= i < |InsertionOps(ins)| :: InvNode(InsertionOps(ins)[i].node)
  {
    assert InvNode(InsertionReads(ins)[0].node);

    ValidInsertWritesWFNodes(ins);
    assert WFNode(InsertionOps(ins)[0].node);

    var newroot := AddMessageToNode(ins.oldroot, ins.key, ins.msg);
    var i := Route(ins.oldroot.pivotTable, ins.key);
    var b := ins.oldroot.buckets[i];
    var b' := newroot.buckets[i];

    BucketInsertMaps(ins.oldroot.buckets[i], ins.key, ins.msg);

    //forall k | k in newroot.buckets[i].keys
    //ensures BoundedKey(pivots, k)
    //ensures Rou
    bucket_keys_in_seq(b);
    bucket_keys_equiv(b');
    assert WFBucketAt(newroot.buckets[i], newroot.pivotTable, i);

    assert InvNode(newroot);
  }

  lemma ValidGrowWritesWFNodes(g: RootGrowth)
  requires ValidGrow(g)
  requires forall i | 0 <= i < |GrowReads(g)| :: WFNode(GrowReads(g)[i].node)
  ensures forall i | 0 <= i < |GrowOps(g)| :: WFNode(GrowOps(g)[i].node)
  ensures WFNode(GrowOps(g)[0].node)
  ensures WFNode(GrowOps(g)[1].node)
  {
    assert WFNode(GrowReads(g)[0].node);
    var newroot := G.Node(InitPivotTable(), [None], Some([g.newchildref]), [EmptyBucket()]);
    WeightBucketListOneEmpty();
    assert WFBucket(newroot.buckets[0]);
    assert WFNode(newroot);
  }

  lemma ValidGrowWritesInvNodes(g: RootGrowth)
  requires ValidGrow(g)
  requires forall i | 0 <= i < |GrowReads(g)| :: InvNode(GrowReads(g)[i].node)
  ensures forall i | 0 <= i < |GrowOps(g)| :: InvNode(GrowOps(g)[i].node)
  ensures InvNode(GrowOps(g)[0].node)
  ensures InvNode(GrowOps(g)[1].node)
  {
    assert InvNode(GrowReads(g)[0].node);
    var newroot := G.Node(InitPivotTable(), [None], Some([g.newchildref]), [EmptyBucket()]);
    WeightBucketListOneEmpty();
    assert InvNode(newroot);
  }

  lemma ValidCloneWritesWFNodes(c: NodeClone)
  requires ValidClone(c)
  requires forall i | 0 <= i < |CloneReads(c)| :: WFNode(CloneReads(c)[i].node)
  ensures forall i | 0 <= i < |CloneOps(c)| :: WFNode(CloneOps(c)[i].node)
  {
    assert WFNode(c.newroot);
  }

  lemma ValidCloneWritesInvNodes(c: NodeClone)
  requires ValidClone(c)
  requires forall i | 0 <= i < |CloneReads(c)| :: InvNode(CloneReads(c)[i].node)
  ensures forall i | 0 <= i < |CloneReads(c)|:: InvNode(CloneOps(c)[i].node)
  {
    assume false;
    // assert InvNode(GrowReads(g)[0].node);
    // var newroot := G.Node(InitPivotTable(), [None], Some([g.newchildref]), [EmptyBucket()]);
    // WeightBucketListOneEmpty();
    // assert InvNode(newroot);
  }

  lemma ValidStepWritesWFNodes(betreeStep: BetreeStep)
  requires ValidBetreeStep(betreeStep)
  requires forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: WFNode(BetreeStepReads(betreeStep)[i].node)
  ensures forall i | 0 <= i < |BetreeStepOps(betreeStep)| :: WFNode(BetreeStepOps(betreeStep)[i].node)
  {
    match betreeStep {
      case BetreeQuery(q) => {}
      case BetreeSuccQuery(q) => {}
      case BetreeInsert(ins) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == InsertionReads(betreeStep.ins)[i].node;
        ValidInsertWritesWFNodes(ins);
      }
      case BetreeFlush(flush) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == FlushReads(betreeStep.flush)[i].node;
        ValidFlushWritesWFNodes(flush);
      }
      case BetreeGrow(growth) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == GrowReads(betreeStep.growth)[i].node;
        ValidGrowWritesWFNodes(growth);
      }
      case BetreeSplit(fusion) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == SplitReads(betreeStep.fusion)[i].node;
        ValidSplitWritesWFNodes(fusion);
      }
      case BetreeMerge(fusion) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == MergeReads(betreeStep.fusion)[i].node;
        ValidMergeWritesWFNodes(fusion);
      }
      case BetreeRepivot(r) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == RepivotReads(betreeStep.repivot)[i].node;
        ValidRepivotWFNodes(r);
      }
      case BetreeClone(r) => {
        assert forall i | 0 <= i < |BetreeStepReads(betreeStep)| :: BetreeStepReads(betreeStep)[i].node == CloneReads(betreeStep.clone)[i].node;
        ValidCloneWritesWFNodes(r);
      }
    }
  }
}
