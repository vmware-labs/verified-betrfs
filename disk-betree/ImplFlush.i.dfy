include "ImplCache.i.dfy"
include "ImplModelFlush.i.dfy"
include "ImplFlushRootBucket.i.dfy"

module ImplFlush { 
  import opened Impl
  import opened ImplCache
  import opened ImplState
  import opened ImplFlushRootBucket

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib
  import opened BucketWeights

  import opened NativeTypes
  import ImplModel
  import ImplModelCache
  import ImplModelFlush
  import ImplModelFlushRootBucket

  import Native

  method flush(k: ImplConstants, s: ImplVariables, parentref: BT.G.Reference, slot: int, childref: BT.G.Reference, child: ImplModel.Node)
  requires Inv(k, s)
  requires s.ready

  requires parentref in IIndirectionTable(s.ephemeralIndirectionTable)
  requires parentref in s.cache

  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].buckets|
  requires s.cache[parentref].children.value[slot] == childref

  requires childref in IIndirectionTable(s.ephemeralIndirectionTable)
  requires childref in s.cache
  requires s.cache[childref] == child

  modifies s.Repr()

  ensures WellUpdated(s)
  ensures s.ready
  ensures ImplModelFlush.flush(Ic(k), old(s.I()), parentref, slot, childref, child) == s.I()
  {
    if s.frozenIndirectionTable != null {
      var lbaGraph := s.frozenIndirectionTable.Get(parentref);
      if lbaGraph.Some? {
        var (lba, _) := lbaGraph.value;
        if lba.None? {
          print "giving up; flush can't run because frozen isn't written";
          return;
        }
      }
    }

    if parentref == BT.G.Root() {
      ImplModelFlushRootBucket.flushRootBucketCorrect(Ic(k), s.I());
      flushRootBucket(k, s);
    }

    //Native.BenchmarkingUtil.start();

    var node := s.cache[parentref];
    var childref := node.children.value[slot];

    WeightBucketLeBucketList(KMTable.ISeq(node.buckets), slot);

    var newparentBucket, newbuckets := KMTable.PartialFlush(node.buckets[slot], child.buckets, child.pivotTable);
    var newchild := child.(buckets := newbuckets);
    var newchildref := alloc(k, s, newchild);
    if newchildref.None? {
      print "giving up; could not get parentref\n";
      return;
    }

    var newparent := IM.Node(
        node.pivotTable,
        Some(node.children.value[slot := newchildref.value]),
        node.buckets[slot := newparentBucket]
      );

    write(k, s, parentref, newparent);

    //Native.BenchmarkingUtil.end();
  }
}
