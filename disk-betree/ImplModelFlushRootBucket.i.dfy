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
  import opened BucketWeights

  import MS = MapSpec
  import Keyspace = MS.Keyspace

  function {:opaque} {:fuel BC.GraphClosed,0} flushRootBucket(k: Constants, s: Variables)
  : (s': Variables)
  requires Inv(k, s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  ensures s'.Ready?
  {
    var oldroot := s.cache[BT.G.Root()];

    var rootBucketSeq := Keyspace.getSortedSeqForMap(s.rootBucket);

    Keyspace.lenSortedSeqForMap(rootBucketSeq, s.rootBucket);
    LenLeWeight(s.rootBucket);
    
    var kmt := KMTable.kmtOfSeq(rootBucketSeq);
    assume WeightBucket(KMTable.I(kmt)) + WeightBucketList(KMTable.ISeq(oldroot.buckets)) < 0x8000_0000_0000_0000;
    var newbuckets := KMTable.flush(kmt, oldroot.buckets, oldroot.pivotTable);
    var newroot := oldroot.(buckets := newbuckets);

    var s' := s.(rootBucket := map[])
        .(rootBucketWeightBound := 0)
        .(cache := s.cache[BT.G.Root() := newroot]);

    s'
  }

  lemma {:fuel BC.GraphClosed,0} flushRootBucketCorrect(k: Constants, s: Variables)
  requires Inv(k, s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  ensures var s' := flushRootBucket(k, s);
    && Inv(k, s')
    && IVars(s) == IVars(s')
    && s'.rootBucket == map[]
    && s'.rootBucketWeightBound == 0
    && TotalCacheSize(s') == TotalCacheSize(s)
  {
    reveal_flushRootBucket();
    var s' := flushRootBucket(k, s);

    var oldroot := s.cache[BT.G.Root()];

    var rootBucketSeq := Keyspace.getSortedSeqForMap(s.rootBucket);

    Keyspace.lenSortedSeqForMap(rootBucketSeq, s.rootBucket);
    LenLeWeight(s.rootBucket);

    var kmt := KMTable.kmtOfSeq(rootBucketSeq);
    KMTable.kmtOfSeqRes(rootBucketSeq, s.rootBucket);

    forall i, key | 0 <= i < |oldroot.buckets| && key in KMTable.I(oldroot.buckets[i]) ensures Pivots.Route(oldroot.pivotTable, key) == i
    {
      //assert BT.NodeHasWFBucketAt(INode(oldroot), i);
    }

    var newbuckets := KMTable.flush(kmt, oldroot.buckets, oldroot.pivotTable);
    WFBucketListFlush(KMTable.I(kmt), KMTable.ISeq(oldroot.buckets), oldroot.pivotTable);
    WeightBucketListFlush(KMTable.I(kmt), KMTable.ISeq(oldroot.buckets), oldroot.pivotTable);

    var newroot := oldroot.(buckets := newbuckets);

    BucketListFlushParentEmpty(KMTable.ISeq(newbuckets), oldroot.pivotTable);
    assert INodeRoot(oldroot, s.rootBucket) == INodeRoot(newroot, map[]);
    assert ICache(s.cache, s.rootBucket) == ICache(s'.cache, map[]);

    WeightBucketEmpty();

    assert WFVars(s');

    assert IVars(s) == IVars(s');
    assert Inv(k, s');
  }

  lemma {:fuel BC.GraphClosed,0} flushRootBucketWeight(k: Constants, s: Variables, slot: int)
  requires Inv(k, s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  requires 0 <= slot < |s.cache[BT.G.Root()].buckets|
  ensures var s' := flushRootBucket(k, s);
    && Inv(k, s')
    && IVars(s) == IVars(s')
    && s'.rootBucket == map[]
    && WeightBucket(KMTable.I(s'.cache[BT.G.Root()].buckets[slot])) <=
         WeightBucket(KMTable.I(s.cache[BT.G.Root()].buckets[slot])) +
         WeightBucket(s.rootBucket);
  {
    reveal_flushRootBucket();
    flushRootBucketCorrect(k, s);

    var s' := flushRootBucket(k, s);
    var oldroot := s.cache[BT.G.Root()];
    var rootBucketSeq := Keyspace.getSortedSeqForMap(s.rootBucket);

    Keyspace.lenSortedSeqForMap(rootBucketSeq, s.rootBucket);
    LenLeWeight(s.rootBucket);

    var kmt := KMTable.kmtOfSeq(rootBucketSeq);
    KMTable.kmtOfSeqRes(rootBucketSeq, s.rootBucket);

    var newbuckets := KMTable.flush(kmt, oldroot.buckets, oldroot.pivotTable);

    WeightBucketListItemFlush(KMTable.I(kmt), KMTable.ISeq(oldroot.buckets), oldroot.pivotTable, slot);
    BucketListFlushAt(KMTable.I(kmt), KMTable.ISeq(oldroot.buckets), oldroot.pivotTable, slot);
  }

  lemma {:fuel BC.GraphClosed,0} flushRootBucketFrozen(k: Constants, s: Variables)
  requires Inv(k, s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  ensures var s' := flushRootBucket(k, s);
    && s'.Ready?
    && s'.frozenIndirectionTable == s.frozenIndirectionTable
  {
    reveal_flushRootBucket();
  }
}
