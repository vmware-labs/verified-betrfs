// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "BookkeepingModel.i.dfy"
include "IOModel.i.dfy"
include "../ByteBlockCacheSystem/AsyncDiskModel.s.dfy"
include "../lib/Buckets/BucketFlushModel.i.dfy"

module FlushModel { 
  import opened IOModel
  import opened BookkeepingModel
  import opened ViewOp
  import opened DiskOpModel

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib
  import opened BucketWeights
  import BucketFlushModel
  import opened Bounds
  import opened BoundedPivotsLib

  import IT = IndirectionTable
  import opened NativeTypes
  import D = AsyncDisk

  function flush(s: BBC.Variables, parentref: BT.G.Reference, slot: int, childref: BT.G.Reference, child: Node, refUpperBound: uint64)
  : BBC.Variables
  requires BBC.Inv(s)
  requires s.Ready?

  requires parentref in s.ephemeralIndirectionTable.graph
  requires parentref in s.cache
  
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires s.cache[parentref].children.value[slot] == childref
  requires forall r | r in s.ephemeralIndirectionTable.graph :: r <= refUpperBound

  requires childref in s.ephemeralIndirectionTable.graph
  requires childref in s.cache
  requires s.cache[childref] == child
  {
    if (
      && s.frozenIndirectionTable.Some?
      && s.frozenIndirectionTable.value.hasEmptyLoc(parentref)
    ) then (
      s
    ) else (
      var parent := s.cache[parentref];

      if BoundedKeySeq(child.pivotTable, parent.buckets[slot].keys) then (
        WeightBucketLeBucketList(parent.buckets, slot);
        lemmaChildrenConditionsOfNode(s, childref);
        lemmaChildrenConditionsOfNode(s, parentref);

        var partialFlushResult(newparentBucket, newbuckets) :=
            BucketFlushModel.partialFlush(
              parent.buckets[slot], child.pivotTable, child.buckets);
        var newchild := child.(buckets := newbuckets);
        var (s2, newchildref) := allocBookkeeping(s, newchild.children, refUpperBound);
        lemmaChildrenConditionsUpdateOfAllocBookkeeping(
          s, newchild.children, parent.children.value, slot, refUpperBound);
        if newchildref.None? then (
          s2
        ) else (
          var newparent := BT.G.Node(
            parent.pivotTable,
            Some(parent.children.value[slot := newchildref.value]),
            parent.buckets[slot := newparentBucket]
          );
          assert s2.WriteAllocConditions();
          var s2 := s2.(cache := s2.cache[newchildref.value := newchild][parentref := newparent]);
          var s2 := writeBookkeeping(s2, parentref, newparent.children);
          s2
        )
      ) else (
        s
      )
    )
  }

  lemma flushCorrect(s: BBC.Variables, parentref: BT.G.Reference, slot: int, childref: BT.G.Reference, child: Node, refUpperBound: uint64)
  requires flush.requires(s, parentref, slot, childref, child, refUpperBound)
  requires s.totalCacheSize() <= MaxCacheSize() - 1
  ensures var s' := flush(s, parentref, slot, childref, child, refUpperBound);
      && s'.Ready?
      && s'.totalCacheSize() <= MaxCacheSize()
      && StateBCImpl.WFCache(s'.cache)
      && betree_next(s, s')
  {
    var s' := flush(s, parentref, slot, childref, child, refUpperBound);

    if (
      && s.frozenIndirectionTable.Some?
      && s.frozenIndirectionTable.value.hasEmptyLoc(parentref)
    ) {
      assert noop(s, s);
    } else {
      var parent := s.cache[parentref];

      if BoundedKeySeq(child.pivotTable, parent.buckets[slot].keys) {
        WeightBucketLeBucketList(parent.buckets, slot);
        lemmaChildrenConditionsOfNode(s, childref);
        lemmaChildrenConditionsOfNode(s, parentref);

        var partialFlushResult(newparentBucket, newbuckets) :=
          BucketFlushModel.partialFlush(
            parent.buckets[slot], child.pivotTable, child.buckets);

        var flushedKeys := {};
        if BucketWellMarshalled(parent.buckets[slot])
            && BucketListWellMarshalled(child.buckets)
            && WFBucketListProper(child.buckets, child.pivotTable)
        {
          flushedKeys := BucketFlushModel.partialFlushCorrect(parent.buckets[slot], child.pivotTable, child.buckets);
        }
        assert (forall key | key in flushedKeys :: key in parent.buckets[slot].keys);

        BucketFlushModel.partialFlushWeightBound(parent.buckets[slot], child.pivotTable, child.buckets);
        
        /*WFBucketIntersect(parent.buckets[slot], flushedKeys);
        WFBucketComplement(parent.buckets[slot], flushedKeys);
        WeightBucketComplement(parent.buckets[slot], flushedKeys);
        WFBucketListFlush(
          BucketIntersect(parent.buckets[slot], flushedKeys),
          child.buckets,
          child.pivotTable);*/
        WeightBucketListShrinkEntry(parent.buckets, slot, newparentBucket);

        // TODO these are actually kind of annoying right now
        assert childref in s.cache;
        assert childref in s.ephemeralIndirectionTable.graph;
        assert child == s.cache[childref];

        assert parentref in s.cache;
        assert parentref in s.ephemeralIndirectionTable.graph;
        assert parent == s.cache[parentref];

        var newchild := child.(buckets := newbuckets);
        var (s2, newchildref) := allocWithNode(s, newchild, refUpperBound);
        reveal_allocBookkeeping();
        if newchildref.None? {
          assert noop(s, s2);
        } else {
          var newparent := BT.G.Node(
            parent.pivotTable,
            Some(parent.children.value[slot := newchildref.value]),
            parent.buckets[slot := newparentBucket]
          );

          var s3 := writeWithNode(s2, parentref, newparent);
          reveal_writeBookkeeping();
          assert s3 == s';

          forall ref | ref in BT.G.Successors(newparent) ensures ref in s2.ephemeralIndirectionTable.graph {
            if (ref == newchildref.value) {
            } else {
              assert ref in BT.G.Successors(parent);
              lemmaChildInGraph(s, parentref, ref);
              assert ref in s2.ephemeralIndirectionTable.graph;
            }
          }
          assert BC.BlockPointsToValidReferences(newparent, s2.ephemeralIndirectionTable.graph);

          forall ref | ref in BT.G.Successors(newchild) ensures ref in s.ephemeralIndirectionTable.graph {
            lemmaChildInGraph(s, childref, ref);
          }

          allocCorrect(s, newchild, refUpperBound);
          writeCorrect(s2, parentref, newparent);

          var flushStep := BT.NodeFlush(
            parentref,
            parent,
            newparent,
            childref,
            child,
            newchildref.value,
            newchild,
            slot);

          assert BT.ValidFlush(flushStep);
          var step := BT.BetreeFlush(flushStep);
          assert newparent == BT.FlushOps(flushStep)[1].node;
          assert BC.Alloc(s, s2, newchildref.value, newchild);
          assert BC.Dirty(s2, s', parentref, newparent);
          BC.MakeTransaction2(s, s2, s', BT.BetreeStepOps(step));
          assert BBC.BetreeMove(s, s', BlockDisk.NoDiskOp, AdvanceOp(UI.NoOp, true), step);
          assert stepsBetree(s, s', AdvanceOp(UI.NoOp, true), step);
          assert stepsBetree(s, s', AdvanceOp(UI.NoOp, true), step);
        } 
      } else {
        assert noop(s, s); 
      }
    }
  }
}
