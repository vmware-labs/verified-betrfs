include "ImplCache.i.dfy"
include "ImplModelFlushRootBucket.i.dfy"

module ImplFlushRootBucket { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache
  import ImplModelFlushRootBucket
  import opened ImplState

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib
  import opened BucketWeights

  import TTT = TwoThreeTree

  import MS = MapSpec
  import Keyspace = MS.Keyspace

  method {:fuel BC.GraphClosed,0} flushRootBucket(k: ImplConstants, s: ImplVariables)
  requires Inv(k, s)
  requires s.ready
  requires BT.G.Root() in s.cache
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == ImplModelFlushRootBucket.flushRootBucket(Ic(k), old(s.I()))
  {
    ImplModelFlushRootBucket.reveal_flushRootBucket();

    var oldroot := s.cache[BT.G.Root()];

    var rootBucketSeq := TTT.AsSeq(s.rootBucket);

    ghost var IrootBucket := TTT.I(s.rootBucket);
    Keyspace.lenSortedSeqForMap(rootBucketSeq, IrootBucket);
    LenLeWeight(IrootBucket);
    var kmt := KMTable.KmtOfSeq(rootBucketSeq, IrootBucket);

    assume WeightBucket(KMTable.I(kmt)) + WeightBucketList(KMTable.ISeq(oldroot.buckets)) < 0x8000_0000_0000_0000;
    var newbuckets := KMTable.Flush(kmt, oldroot.buckets, oldroot.pivotTable);

    var newroot := oldroot.(buckets := newbuckets);

    s.rootBucket := TTT.EmptyTree;
    s.rootBucketWeightBound := 0;
    s.cache := s.cache[BT.G.Root() := newroot];
  }

}
