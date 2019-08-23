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

  method {:fuel BC.GraphClosed,0} flushRootBucket(k: ImplConstants, s: ImplVariables)
  returns (s': ImplVariables)
  requires Inv(k, s)
  requires s.Ready?
  requires s.rootBucket != TTT.EmptyTree
  ensures WVars(s')
  ensures IVars(s') == ImplModelFlushRootBucket.flushRootBucket(Ic(k), old(IVars(s)))
  {
    ImplModelFlushRootBucket.reveal_flushRootBucket();

    var oldroot := s.cache[BT.G.Root()];

    var rootBucketSeq := TTT.AsSeq(s.rootBucket);

    if (!(
        && |rootBucketSeq| < 0x800_0000_0000
        && (forall i | 0 <= i < |rootBucketSeq| :: |rootBucketSeq[i].0| < 0x1_000)
        && (forall i | 0 <= i < |rootBucketSeq| :: rootBucketSeq[i].1 != Messages.IdentityMessage())
        && (forall i | 0 <= i < |rootBucketSeq| :: |rootBucketSeq[i].1.value| < 0x1_000)))
    {
      s' := s;
      print "giving up; rootBucketSeq too big\n";
      return;
    }

    var kmt := KMTable.KMTableOfSeq(rootBucketSeq, TTT.I(s.rootBucket));

    if (!(
      && |kmt.keys| < 0x4000_0000_0000_0000
      && |oldroot.buckets| < 0x1_0000_0000_0000_0000
      && (forall i | 0 <= i < |oldroot.buckets| :: |oldroot.buckets[i].keys| < 0x4000_0000_0000_0000)
    )) {
      s' := s;
      print "giving up; kmt/oldroot.buckets too big\n";
      return;
    }

    var newbuckets := KMTable.Flush(kmt, oldroot.buckets, oldroot.pivotTable);

    var newroot := oldroot.(buckets := newbuckets);

    s' := s.(rootBucket := TTT.EmptyTree)
        .(cache := s.cache[BT.G.Root() := newroot]);
  }

}
