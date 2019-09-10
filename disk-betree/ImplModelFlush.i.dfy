include "ImplModelCache.i.dfy"
include "ImplModelIO.i.dfy"
include "AsyncDiskModel.s.dfy"
include "KVListPartialFlush.i.dfy"

module ImplModelFlush { 
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelCache
  import KVListPartialFlush

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds

  import opened NativeTypes
  import D = AsyncDisk

  function flush(k: Constants, s: Variables, parentref: BT.G.Reference, slot: int, childref: BT.G.Reference, child: Node)
  : Variables
  requires Inv(k, s)
  requires s.Ready?

  requires parentref in s.ephemeralIndirectionTable
  requires parentref in s.cache

  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires s.cache[parentref].children.value[slot] == childref

  requires childref in s.ephemeralIndirectionTable
  requires childref in s.cache
  requires s.cache[childref] == child
  {
    if (
      && s.frozenIndirectionTable.Some?
      && parentref in s.frozenIndirectionTable.value
      && var entry := s.frozenIndirectionTable.value[parentref];
      && var (loc, _) := entry;
      && loc.None?
    ) then (
      s
    ) else (
      var parent := s.cache[parentref];

      WeightBucketLeBucketList(parent.buckets, slot);
      WFBucketsOfWFBucketList(parent.buckets, parent.pivotTable);
      WFBucketsOfWFBucketList(child.buckets, child.pivotTable);

      var (newparentBucket, newbuckets) := KVListPartialFlush.bucketPartialFlush(parent.buckets[slot], child.buckets, child.pivotTable);
      var newchild := child.(buckets := newbuckets);
      var (s2, newchildref) := alloc(k, s, newchild);
      if newchildref.None? then (
        s2
      ) else (
        var newparent := Node(
          parent.pivotTable,
          Some(parent.children.value[slot := newchildref.value]),
          parent.buckets[slot := newparentBucket]
        );
        var s' := write(k, s2, parentref, newparent);
        s'
      )
    )
  }

  lemma flushCorrect(k: Constants, s: Variables, parentref: BT.G.Reference, slot: int, childref: BT.G.Reference, child: Node)
  requires flush.requires(k, s, parentref, slot, childref, child)
  requires TotalCacheSize(s) <= MaxCacheSize() - 1
  ensures
      var s' := flush(k, s, parentref, slot, childref, child);
      && WFVars(s')
      && M.Next(Ik(k), I(k, s), I(k, s'), UI.NoOp, D.NoDiskOp)
  {
    if (
      && s.frozenIndirectionTable.Some?
      && parentref in s.frozenIndirectionTable.value
      && var entry := s.frozenIndirectionTable.value[parentref];
      && var (loc, _) := entry;
      && loc.None?
    ) {
      assert noop(k, IVars(s), IVars(s));
    } else {
      var parent := s.cache[parentref];

      WeightBucketLeBucketList(parent.buckets, slot);
      WFBucketsOfWFBucketList(parent.buckets, parent.pivotTable);
      WFBucketsOfWFBucketList(child.buckets, child.pivotTable);

      var (newparentBucket, newbuckets) := KVListPartialFlush.bucketPartialFlush(parent.buckets[slot], child.buckets, child.pivotTable);
      var flushedKeys := KVListPartialFlush.bucketPartialFlushRes(parent.buckets[slot], child.buckets, child.pivotTable);

      WFBucketsOfWFBucketList(parent.buckets, parent.pivotTable);
      WFBucketIntersect(parent.buckets[slot], flushedKeys);
      WFBucketComplement(parent.buckets[slot], flushedKeys);
      WeightBucketComplement(parent.buckets[slot], flushedKeys);
      WFBucketListFlush(
        BucketIntersect(parent.buckets[slot], flushedKeys),
        child.buckets,
        child.pivotTable);
      WeightBucketListShrinkEntry(parent.buckets, slot, newparentBucket);

      // TODO these are actually kind of annoying right now
      assume childref in s.cache;
      assume childref in s.ephemeralIndirectionTable;
      assume child == s.cache[childref];
      assume childref != BT.G.Root();

      assert parentref in s.cache;
      assert parentref in s.ephemeralIndirectionTable;
      assert parent == s.cache[parentref];

      var newchild := child.(buckets := newbuckets);
      var (s2, newchildref) := alloc(k, s, newchild);
      reveal_alloc();
      if newchildref.None? {
        assert noop(k, IVars(s), IVars(s2));
      } else {
        var newparent := Node(
          parent.pivotTable,
          Some(parent.children.value[slot := newchildref.value]),
          parent.buckets[slot := newparentBucket]
        );
        reveal_BucketComplement();

        var s' := write(k, s2, parentref, newparent);
        reveal_write();

        forall ref | ref in BT.G.Successors(INode(newparent)) ensures ref in IIndirectionTable(s2.ephemeralIndirectionTable).graph {
          if (ref == newchildref.value) {
          } else {
            assert ref in BT.G.Successors(INode(parent));
            lemmaChildInGraph(k, s, parentref, ref);
            assert ref in IIndirectionTable(s2.ephemeralIndirectionTable).graph;
          }
        }
        assert BC.BlockPointsToValidReferences(INode(newparent), IIndirectionTable(s2.ephemeralIndirectionTable).graph);

        forall ref | ref in BT.G.Successors(INode(newchild)) ensures ref in IIndirectionTable(s.ephemeralIndirectionTable).graph {
          lemmaChildInGraph(k, s, childref, ref);
        }

        WeightBucketListFlush(parent.buckets[slot], child.buckets, child.pivotTable);
        WeightBucketListClearEntry(parent.buckets, slot);

        assume parent.buckets[slot := newparentBucket]
            == parent.buckets[slot := newparentBucket];

        allocCorrect(k, s, newchild);
        writeCorrect(k, s2, parentref, newparent);

        var flushStep := BT.NodeFlush(parentref, INode(parent), childref, INode(child), newchildref.value, INode(newchild), slot, flushedKeys);
        assert BT.ValidFlush(flushStep);
        var step := BT.BetreeFlush(flushStep);
        assert INode(newparent) == BT.FlushOps(flushStep)[1].node;
        assert BC.Alloc(Ik(k), IVars(s), IVars(s2), newchildref.value, INode(newchild));
        assert BC.Dirty(Ik(k), IVars(s2), IVars(s'), parentref, INode(newparent));
        BC.MakeTransaction2(Ik(k), IVars(s), IVars(s2), IVars(s'), BT.BetreeStepOps(step));
        assert BBC.BetreeMove(Ik(k), IVars(s), IVars(s'), UI.NoOp, M.IDiskOp(D.NoDiskOp), step);
        assert stepsBetree(k, IVars(s), IVars(s'), UI.NoOp, step);
        assert stepsBetree(k, IVars(s), IVars(s'), UI.NoOp, step);
      }
    }
  }
}
