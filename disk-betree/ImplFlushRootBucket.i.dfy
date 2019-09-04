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
  returns (s': ImplVariables)
  requires Inv(k, s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  ensures WVars(s')
  ensures IVars(s') == ImplModelFlushRootBucket.flushRootBucket(Ic(k), old(IVars(s)))
  ensures s.ephemeralIndirectionTable == s'.ephemeralIndirectionTable
  ensures s.lru == s'.lru
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

    s' := s.(rootBucket := TTT.EmptyTree)
           .(rootBucketWeightBound := 0)
        .(cache := s.cache[BT.G.Root() := newroot]);
  }

}
