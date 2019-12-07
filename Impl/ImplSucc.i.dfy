include "Impl.i.dfy"
include "ImplSync.i.dfy"
include "ImplModelSucc.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "ImplBucketSuccessorLoop.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplSucc { 
  import opened Impl
  import opened ImplSync
  import opened ImplIO
  import ImplModelSucc
  import ImplModelCache
  import opened ImplState
  import opened MutableBucket
  import opened Lexicographic_Byte_Order
  import opened ImplNode

  import opened Options
  import opened NativeTypes
  import opened Maps
  import opened Sets
  import opened Sequences

  import opened Bounds
  import opened BucketsLib
  import PivotsLib

  import opened PBS = PivotBetreeSpec`Spec


  predicate {:opaque} BucketListInCache(buckets: seq<MutBucket>, s: ImplVariables)
  reads buckets, s, s.cache
  {
    && forall o | o in buckets :: o in s.cache.Repr
    && MutBucket.ReprSeq(buckets) <= s.cache.Repr
  }

  lemma BucketListInCacheOfEmpty(s: ImplVariables)
  ensures BucketListInCache([], s)

  lemma BucketListInCacheOfAppend(buckets: seq<MutBucket>, s: ImplVariables, b: MutBucket)
  requires BucketListInCache(buckets, s)
  requires b.Repr <= s.cache.Repr
  ensures BucketListInCache(buckets + [b], s)

  lemma BucketListInCacheNotIn(buckets: seq<MutBucket>, s: ImplVariables, other: set<object>)
  requires BucketListInCache(buckets, s)
  requires s.cache.Repr !! other
  ensures MutBucket.ReprSeq(buckets) !! other;
  ensures forall o | o in buckets :: o !in other;

  method getPathInternal(k: ImplConstants, s: ImplVariables, key: MS.Key, acc: seq<MutBucket>, upTo: Option<MS.Key>, ref: BT.G.Reference, counter: uint64, node: Node)
  returns (pr : PathResult)
  requires Inv(k, s)
  requires node.Inv()
  requires ImplModel.WFNode(node.I())
  requires s.ready
  requires BucketListInCache(acc, s)
  requires node.Repr <= s.cache.Repr
  modifies s.Repr()
  decreases counter, 0
  ensures pr.Path? ==> BucketListInCache(pr.buckets, s)
  ensures WellUpdated(s)
  ensures (s.I(), IPathResult(pr))
       == ImplModelSucc.getPathInternal(Ic(k), old(s.I()), key, old(MutBucket.ISeq(acc)), upTo, ref, counter, old(node.I()))
  {
    ImplModelSucc.reveal_getPathInternal();

    var r := Pivots.ComputeRoute(node.pivotTable, key);
    var bucket := node.buckets[r];
    var acc' := acc + [bucket];

    assert bucket.I() == node.I().buckets[r];
    assume bucket.Repr <= s.cache.Repr;
    BucketListInCacheOfAppend(acc, s, bucket);

    //ghost var now_s := s.I();
    //ghost var now_acc' := MutBucket.ISeq(acc');
    //ghost var now_bucket := bucket.I();

    assert MutBucket.ISeq(acc')
        == MutBucket.ISeq(acc) + [bucket.I()];
        //== old(MutBucket.ISeq(acc)) + [bucket.I()]
        //== old(MutBucket.ISeq(acc)) + [now_bucket];

    var upTo';
    if r == |node.pivotTable| as uint64 {
      upTo' := upTo;
    } else {
      var ub := node.pivotTable[r];
      if upTo.Some? {
        var c := cmp(upTo.value, ub);
        var k: MS.Key := if c < 0 then upTo.value else ub;
        upTo' := Some(k);
      } else {
        upTo' := Some(ub);
      }
    }

    assert MutBucket.ISeq(acc')
        == old(MutBucket.ISeq(acc) + [node.I().buckets[r]]);

    if node.children.Some? {
      if counter == 0 {
        pr := Failure;

        //assert (s.I(), IPathResult(pr)) == ImplModelSucc.getPathInternal(Ic(k), old(s.I()), key, old(MutBucket.ISeq(acc)), upTo, ref, counter, old(node.I()));
      } else {
        pr := getPath(k, s, key, acc', upTo', node.children.value[r], counter - 1);

        //assert (s.I(), IPathResult(pr)) == ImplModelSucc.getPathInternal(Ic(k), old(s.I()), key, old(MutBucket.ISeq(acc)), upTo, ref, counter, old(node.I()));
      }
    } else {
      pr := Path(acc', upTo');

      //assert (s.I(), IPathResult(pr)) == ImplModelSucc.getPathInternal(Ic(k), old(s.I()), key, old(MutBucket.ISeq(acc)), upTo, ref, counter, old(node.I()));
    }
  }

  method getPath(k: ImplConstants, s: ImplVariables, key: MS.Key, acc: seq<MutBucket>, upTo: Option<MS.Key>, ref: BT.G.Reference, counter: uint64)
  returns (pr : PathResult)
  requires Inv(k, s)
  requires s.ready
  requires BucketListInCache(acc, s)
  modifies s.Repr()
  decreases counter, 1
  ensures pr.Path? ==> BucketListInCache(pr.buckets, s)
  ensures WellUpdated(s)
  ensures (s.I(), IPathResult(pr))
       == ImplModelSucc.getPath(Ic(k), old(s.I()), key, old(MutBucket.ISeq(acc)), upTo, ref, counter)
  {
    ImplModelSucc.reveal_getPath();

    MutBucket.AllocatedReprSeq(acc);

    var nodeOpt := s.cache.GetOpt(ref);
    if nodeOpt.Some? {
      var node := nodeOpt.value;

      assert node.I() == s.I().cache[ref];
      s.cache.LemmaNodeReprLeRepr(ref);

      pr := getPathInternal(k, s, key, acc, upTo, ref, counter, node);

      ghost var ghosty := true;
      if (ghosty && pr.Path?) {
        // Preserve facts about the buckets across the LRU usage
        // Use that the buckets are all in the cache
        MutBucket.AllocatedReprSeq(pr.buckets);
        BucketListInCacheNotIn(pr.buckets, s, s.lru.Repr);
      }

      LruModel.LruUse(s.I().lru, ref);
      s.lru.Use(ref);
    } else {
      pr := Fetch(ref);
    }
  }
}
