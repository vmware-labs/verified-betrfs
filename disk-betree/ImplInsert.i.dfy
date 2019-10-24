include "Impl.i.dfy"
include "ImplIO.i.dfy"
include "ImplCache.i.dfy"
include "ImplModelInsert.i.dfy"
include "ImplFlushPolicy.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Option.s.dfy"
include "../lib/Sets.i.dfy"
include "PivotBetreeSpec.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplInsert { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache
  import opened ImplModelInsert
  import opened ImplState
  import opened ImplFlushPolicy
  import opened MutableBucket

  import opened Options
  import opened Maps
  import opened Sets
  import opened Sequences
  import opened NativeTypes

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds

  import opened PBS = PivotBetreeSpec`Spec

  import Native

  method InsertKeyValue(k: ImplConstants, s: ImplVariables, key: MS.Key, value: MS.Value)
  returns (success: bool)
  requires Inv(k, s)
  requires s.ready
  requires BT.G.Root() in s.cache.I()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), success) == ImplModelInsert.InsertKeyValue(Ic(k), old(s.I()), key, value)
  {
    ImplModelInsert.reveal_InsertKeyValue();

    if s.frozenIndirectionTable != null {
      var b := s.frozenIndirectionTable.HasEmptyLoc(BT.G.Root());
      if b {
        success := false;
        print "giving up; can't dirty root because frozen isn't written";
        return;
      }
    }


    // TODO this isn't necessary because the children don't change
    var root := s.cache.GetOpt(BT.G.Root());
    var children := root.value.children;

    var msg := Messages.Define(value);
    s.cache.InsertKeyValue(BT.G.Root(), key, msg);

    writeBookkeeping(k, s, BT.G.Root(), children);

    success := true;
  }

  method insert(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (success: bool)
  requires io.initialized()
  requires Inv(k, s)
  requires io !in s.Repr()
  modifies s.Repr()
  modifies io
  ensures WellUpdated(s)
  ensures ImplModelInsert.insert(Ic(k), old(s.I()), old(IIO(io)), key, value, s.I(), success, IIO(io))
  {
    ImplModelInsert.reveal_insert();

    if (!s.ready) {
      PageInIndirectionTableReq(k, s, io);
      success := false;
      return;
    }

    var rootLookup := s.cache.GetOpt(BT.G.Root());
    if (rootLookup.None?) {
      if TotalCacheSize(s) <= MaxCacheSizeUint64() - 1 {
        PageInReq(k, s, io, BT.G.Root());
        success := false;
      } else {
        print "insert: root not in cache, but cache is full\n";
        success := false;
      }
      return;
    }

    var weightSeq := MutBucket.computeWeightOfSeq(rootLookup.value.buckets);

    if WeightKeyUint64(key) + WeightMessageUint64(Messages.Define(value)) + weightSeq
        <= MaxTotalBucketWeightUint64() {
      success := InsertKeyValue(k, s, key, value);
    } else {
      runFlushPolicy(k, s, io);
      success := false;
    }
  }
}
