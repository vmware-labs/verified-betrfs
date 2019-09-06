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

  method RemoveLBAFromIndirectionTable(table: MutIndirectionTable, ref: Reference)
  requires table.Inv()
  ensures table.Inv()
  ensures table.Contents == ImplModelInsert.removeLBAFromIndirectionTable(old(table.Contents), ref)
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in table.Repr :: fresh(r) || r in old(table.Repr)
  modifies table.Repr
  {
    var lbaGraph := table.Remove(ref);
    if lbaGraph.Some? {
      // TODO how do we deal with this?
      assume table.Count as nat < 0x10000000000000000 / 8;
      var (lba, graph) := lbaGraph.value;
      var _ := table.Insert(ref, (None, graph));
    }
  }

  method InsertKeyValue(k: ImplConstants, s: ImplVariables, key: MS.Key, value: MS.Value)
  returns (success: bool)
  requires Inv(k, s)
  requires s.ready
  requires BT.G.Root() in s.cache.Contents
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), success) == ImplModelInsert.InsertKeyValue(Ic(k), old(s.I()), key, value)
  {
    ImplModelInsert.reveal_InsertKeyValue();

    if s.frozenIndirectionTable != null {
      var rootInFrozenLbaGraph := s.frozenIndirectionTable.Get(BT.G.Root());
      if (
        && rootInFrozenLbaGraph.Some?
        && rootInFrozenLbaGraph.value.0.None?
      ) {
        // TODO write out the root here instead of giving up
        success := false;
        print "giving up; can't dirty root when frozen is not written yet\n";
        return;
      }
    }

    var msg := Messages.Define(value);
    var newRootBucket := TTT.Insert(s.rootBucket, key, msg);

    // TODO how do we deal with this?
    assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;

    RemoveLBAFromIndirectionTable(s.ephemeralIndirectionTable, BT.G.Root());

    var newW := s.rootBucketWeightBound + WeightKeyUint64(key) + WeightMessageUint64(msg);

    s.rootBucket := newRootBucket;
    s.rootBucketWeightBound := newW;
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

    var rootLookup := s.cache.Get(BT.G.Root());
    if (rootLookup.None?) {
      if TotalCacheSize(s) <= MaxCacheSize() - 1 {
        PageInReq(k, s, io, BT.G.Root());
        success := false;
      } else {
        print "insert: root not in cache, but cache is full\n";
        success := false;
      }
      return;
    }

    var weightSeq := KMTable.computeWeightKMTSeq(rootLookup.value.buckets);

    if WeightKeyUint64(key) + WeightMessageUint64(Messages.Define(value)) +
        s.rootBucketWeightBound +
        weightSeq
        <= MaxTotalBucketWeight() as uint64 {
      success := InsertKeyValue(k, s, key, value);
    } else {
      runFlushPolicy(k, s, io);
      success := false;
    }
  }
}
