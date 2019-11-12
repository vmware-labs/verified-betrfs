include "Impl.i.dfy"
include "ImplIO.i.dfy"
include "ImplCache.i.dfy"
include "ImplModelInsert.i.dfy"
include "ImplFlushPolicy.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"
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

  method passiveAggressive(k: ImplConstants, s: ImplVariables, key: MS.Key, value: MS.Value)
  returns (theRef: BT.G.Reference)
  {
    var ref := BT.G.Root();
    var root := s.cache.GetOpt(ref);
    var node := root.value;
    while true
    {
      if node.children.None? {
        return ref;
      }
      var r := Pivots.ComputeRoute(node.pivotTable, key);
      //var q := node.buckets[r].Query(key);
      //if q.Some? {
      //  return ref;
      //}
      if node.buckets[r].Weight != 0 {
        return ref;
      }
      var childref := node.children.value[r];

      var childNode := s.cache.GetOpt(childref);
      if childNode.None? {
        return ref;
      }

      var entry := s.ephemeralIndirectionTable.t.Get(childref);
      if entry.value.loc.Some? {
        return ref;
      }

      var weightSeq := MutBucket.computeWeightOfSeq(childNode.value.buckets);
      if !(WeightKeyUint64(key) + WeightMessageUint64(Messages.Define(value)) + weightSeq
          <= MaxTotalBucketWeightUint64()) {
        return ref;
      }

      ref := childref;
      node := childNode.value;
    }
  }

>>>>>>> 152f3da... passive agressive test
  method InsertKeyValue(k: ImplConstants, s: ImplVariables, key: MS.Key, value: MS.Value)
  returns (success: bool)
  requires Inv(k, s)
  requires s.ready
  requires BT.G.Root() in s.cache.I()
  requires |s.ephemeralIndirectionTable.I().graph| <= IndirectionTableModel.MaxSize() - 1
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), success) == ImplModelInsert.InsertKeyValue(Ic(k), old(s.I()), key, value)
  {
    ImplModelInsert.reveal_InsertKeyValue();

    //Native.BenchmarkingUtil.start("passiveAggressive calc");
    //var ref := passiveAggressive(k, s, key, value);
    var ref := BT.G.Root();
    //Native.BenchmarkingUtil.end("passiveAggressive calc");

    ImplModelCache.lemmaChildrenConditionsOfNode(Ic(k), s.I(), ref);

    if s.frozenIndirectionTable != null {
      var b := s.frozenIndirectionTable.HasEmptyLoc(ref);
      if b {
        success := false;
        print "giving up; can't dirty root because frozen isn't written";
        return;
      }
    }

    var msg := Messages.Define(value);
    s.cache.InsertKeyValue(ref, key, msg);

    writeBookkeepingNoSuccsUpdate(k, s, ref);

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

    var indirectionTableSize := s.ephemeralIndirectionTable.GetSize();
    if (!(indirectionTableSize <= IndirectionTableModel.MaxSizeUint64() - 3)) {
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
