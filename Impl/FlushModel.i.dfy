include "BookkeepingModel.i.dfy"
include "IOModel.i.dfy"
include "../ByteBlockCacheSystem/AsyncDiskModel.s.dfy"
include "../lib/Buckets/BucketModel.i.dfy"

module FlushModel { 
  import opened StateBCModel
  import opened StateSectorModel

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
  import BucketModel
  import opened Bounds
  import opened BoundedPivotsLib

  import opened NativeTypes
  import D = AsyncDisk

  function flush(s: BCVariables, parentref: BT.G.Reference, slot: int, childref: BT.G.Reference, child: Node)
  : BCVariables
  requires BCInv(s)
  requires s.Ready?

  requires parentref in s.ephemeralIndirectionTable.graph
  requires parentref in s.cache
  
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires s.cache[parentref].children.value[slot] == childref

  requires childref in s.ephemeralIndirectionTable.graph
  requires childref in s.cache
  requires s.cache[childref] == child
  requires |s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 2
  {
    if (
      && s.frozenIndirectionTable.Some?
      && IndirectionTableModel.HasEmptyLoc(s.frozenIndirectionTable.value, parentref)
    ) then (
      s
    ) else (
      var parent := s.cache[parentref];

      if BoundedKeySeq(child.pivotTable, parent.buckets[slot].keys) then (
        WeightBucketLeBucketList(parent.buckets, slot);
        lemmaChildrenConditionsOfNode(s, childref);
        lemmaChildrenConditionsOfNode(s, parentref);

        var partialFlushResult(newparentBucket, newbuckets) :=
            BucketModel.partialFlush(
              parent.buckets[slot], child.pivotTable, child.buckets);
        var newchild := child.(buckets := newbuckets);
        var (s2, newchildref) := allocBookkeeping(s, newchild.children);
        lemmaChildrenConditionsUpdateOfAllocBookkeeping(
          s, newchild.children, parent.children.value, slot);
        if newchildref.None? then (
          s2
        ) else (
          var newparent := BT.G.Node(
            parent.pivotTable,
            Some(parent.children.value[slot := newchildref.value]),
            parent.buckets[slot := newparentBucket]
          );
          var s2 := writeBookkeeping(s2, parentref, newparent.children);
          var s' := s2.(cache := s2.cache[newchildref.value := newchild][parentref := newparent]);
          s'
        )
      ) else (
        s
      )
    )
  }

  lemma flushCorrect(s: BCVariables, parentref: BT.G.Reference, slot: int, childref: BT.G.Reference, child: Node)
  requires flush.requires(s, parentref, slot, childref, child)
  requires TotalCacheSize(s) <= MaxCacheSize() - 1
  ensures
      var s' := flush(s, parentref, slot, childref, child);
      && WFBCVars(s')
      && betree_next(IBlockCache(s), IBlockCache(s'))
  {
    var s' := flush(s, parentref, slot, childref, child);

    if (
      && s.frozenIndirectionTable.Some?
      && IndirectionTableModel.HasEmptyLoc(s.frozenIndirectionTable.value, parentref)
    ) {
      assert noop(IBlockCache(s), IBlockCache(s));
    } else {
      var parent := s.cache[parentref];

      if BoundedKeySeq(child.pivotTable, parent.buckets[slot].keys) {
        WeightBucketLeBucketList(parent.buckets, slot);
        lemmaChildrenConditionsOfNode(s, childref);
        lemmaChildrenConditionsOfNode(s, parentref);

        var partialFlushResult(newparentBucket, newbuckets) :=
          BucketModel.partialFlush(
            parent.buckets[slot], child.pivotTable, child.buckets);

        var flushedKeys := {};
        if BucketWellMarshalled(parent.buckets[slot])
            && BucketListWellMarshalled(child.buckets)
            && WFBucketListProper(child.buckets, child.pivotTable)
        {
          flushedKeys := BucketModel.partialFlushCorrect(parent.buckets[slot], child.pivotTable, child.buckets);
        }
        assert (forall key | key in flushedKeys :: key in parent.buckets[slot].keys);

        BucketModel.partialFlushWeightBound(parent.buckets[slot], child.pivotTable, child.buckets);
        
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
        var (s2, newchildref) := allocWithNode(s, newchild);
        reveal_allocBookkeeping();
        if newchildref.None? {
          assert noop(IBlockCache(s), IBlockCache(s2));
        } else {
          var newparent := BT.G.Node(
            parent.pivotTable,
            Some(parent.children.value[slot := newchildref.value]),
            parent.buckets[slot := newparentBucket]
          );
          reveal_BucketComplement();

          var s3 := writeWithNode(s2, parentref, newparent);
          reveal_writeBookkeeping();
          assert s3 == s';

          forall ref | ref in BT.G.Successors(INode(newparent)) ensures ref in IIndirectionTable(s2.ephemeralIndirectionTable).graph {
            if (ref == newchildref.value) {
            } else {
              assert ref in BT.G.Successors(INode(parent));
              lemmaChildInGraph(s, parentref, ref);
              assert ref in IIndirectionTable(s2.ephemeralIndirectionTable).graph;
            }
          }
          assert BC.BlockPointsToValidReferences(INode(newparent), IIndirectionTable(s2.ephemeralIndirectionTable).graph);

          forall ref | ref in BT.G.Successors(INode(newchild)) ensures ref in IIndirectionTable(s.ephemeralIndirectionTable).graph {
            lemmaChildInGraph(s, childref, ref);
          }

          WeightBucketListClearEntry(parent.buckets, slot);

          allocCorrect(s, newchild);
          writeCorrect(s2, parentref, newparent);

          var flushStep := BT.NodeFlush(
            parentref,
            INode(parent),
            childref,
            INode(child),
            newchildref.value,
            INode(newchild),
            slot,
            flushedKeys,
            INode(newparent).buckets[slot],
            INode(newchild).buckets);
          assert BT.ValidFlush(flushStep);
          var step := BT.BetreeFlush(flushStep);
          assert INode(newparent) == BT.FlushOps(flushStep)[1].node;
          assert BC.Alloc(IBlockCache(s), IBlockCache(s2), newchildref.value, INode(newchild));
          assert BC.Dirty(IBlockCache(s2), IBlockCache(s'), parentref, INode(newparent));
          BC.MakeTransaction2(IBlockCache(s), IBlockCache(s2), IBlockCache(s'), BT.BetreeStepOps(step));
          assert BBC.BetreeMove(IBlockCache(s), IBlockCache(s'), BlockDisk.NoDiskOp, AdvanceOp(UI.NoOp, true), step);
          assert stepsBetree(IBlockCache(s), IBlockCache(s'), AdvanceOp(UI.NoOp, true), step);
          assert stepsBetree(IBlockCache(s), IBlockCache(s'), AdvanceOp(UI.NoOp, true), step);
        } 
      } else {
        assert noop(IBlockCache(s), IBlockCache(s)); 
      }
    }
  }
}
