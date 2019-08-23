include "ImplModelCache.i.dfy"

module ImplModelFlushRootBucket { 
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelCache

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import MS = MapSpec
  import Keyspace = MS.Keyspace

  function {:opaque} {:fuel BC.GraphClosed,0} flushRootBucket(k: Constants, s: Variables)
  : (s': Variables)
  requires Inv(k, s)
  requires s.Ready?
  requires s.rootBucket != map[]
  {
    var oldroot := s.cache[BT.G.Root()];

    var rootBucketSeq := Keyspace.getSortedSeqForMap(s.rootBucket);

    if (!(
        && |rootBucketSeq| < 0x800_0000_0000
        && (forall i | 0 <= i < |rootBucketSeq| :: |rootBucketSeq[i].0| < 0x1_000)
        && (forall i | 0 <= i < |rootBucketSeq| :: rootBucketSeq[i].1 != Messages.IdentityMessage())
        && (forall i | 0 <= i < |rootBucketSeq| :: |rootBucketSeq[i].1.value| < 0x1_000)
    )) then (
      s
    ) else (
      var kmt := KMTable.kmtableOfSeq(rootBucketSeq);
      if (!(
        && |kmt.keys| < 0x4000_0000_0000_0000
        && |oldroot.buckets| < 0x1_0000_0000_0000_0000
        && (forall i | 0 <= i < |oldroot.buckets| :: |oldroot.buckets[i].keys| < 0x4000_0000_0000_0000)
      )) then (
        s
      ) else (
        var newbuckets := KMTable.flush(kmt, oldroot.buckets, oldroot.pivotTable);
        var newroot := oldroot.(buckets := newbuckets);

        var s' := s.(rootBucket := map[])
            .(cache := s.cache[BT.G.Root() := newroot]);

        s'
      )
    )
  }

  lemma {:fuel BC.GraphClosed,0} flushRootBucketCorrect(k: Constants, s: Variables)
  requires Inv(k, s)
  requires s.Ready?
  requires s.rootBucket != map[]
  ensures var s' := flushRootBucket(k, s);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, D.NoDiskOp)
  {
    reveal_flushRootBucket();
    var s' := flushRootBucket(k, s);

    var oldroot := s.cache[BT.G.Root()];

    var rootBucketSeq := Keyspace.getSortedSeqForMap(s.rootBucket);

    if (!(
        && |rootBucketSeq| < 0x800_0000_0000
        && (forall i | 0 <= i < |rootBucketSeq| :: |rootBucketSeq[i].0| < 0x1_000)
        && (forall i | 0 <= i < |rootBucketSeq| :: rootBucketSeq[i].1 != Messages.IdentityMessage())
        && (forall i | 0 <= i < |rootBucketSeq| :: |rootBucketSeq[i].1.value| < 0x1_000)))
    {
      assert noop(k, IVars(s), IVars(s'));
      return;
    }

    var kmt := KMTable.kmtableOfSeq(rootBucketSeq);
    KMTable.kmtableOfSeqRes(rootBucketSeq, s.rootBucket);

    if (!(
      && |kmt.keys| < 0x4000_0000_0000_0000
      && |oldroot.buckets| < 0x1_0000_0000_0000_0000
      && (forall i | 0 <= i < |oldroot.buckets| :: |oldroot.buckets[i].keys| < 0x4000_0000_0000_0000)
    )) {
      assert noop(k, IVars(s), IVars(s'));
      return;
    }

    forall i, key | 0 <= i < |oldroot.buckets| && key in KMTable.I(oldroot.buckets[i]) ensures Pivots.Route(oldroot.pivotTable, key) == i
    {
      //assert BT.NodeHasWFBucketAt(INode(oldroot), i);
    }

    var newbuckets := KMTable.flush(kmt, oldroot.buckets, oldroot.pivotTable);
    KMTable.flushRes(kmt, oldroot.buckets, oldroot.pivotTable);
    WFBucketListFlush(KMTable.I(kmt), KMTable.ISeq(oldroot.buckets), oldroot.pivotTable);
    assume forall i | 0 <= i < |newbuckets| :: KMTable.Bounded(newbuckets[i]);

    var newroot := oldroot.(buckets := newbuckets);

    BucketListFlushParentEmpty(KMTable.ISeq(newbuckets), oldroot.pivotTable);
    assert INodeRoot(oldroot, s.rootBucket) == INodeRoot(newroot, map[]);
    assert ICache(s.cache, s.rootBucket) == ICache(s'.cache, map[]);

    assert noop(k, IVars(s), IVars(s'));
  }
}
