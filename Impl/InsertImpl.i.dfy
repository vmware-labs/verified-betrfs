include "IOImpl.i.dfy"
include "BookkeepingImpl.i.dfy"
include "InsertModel.i.dfy"
include "FlushPolicyImpl.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"

// See dependency graph in MainHandlers.dfy

module InsertImpl { 
  import opened IOImpl
  import opened BookkeepingImpl
  import opened InsertModel
  import opened StateImpl
  import opened FlushPolicyImpl
  import opened BucketImpl

  import opened Options
  import opened Maps
  import opened Sets
  import opened Sequences
  import opened NativeTypes
  import opened KeyType
  import opened ValueType
  import ValueMessage

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds

  import opened PBS = PivotBetreeSpec`Spec

  method passiveAggressive(k: ImplConstants, s: ImplVariables, key: Key, value: Value)
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
      if !(WeightKeyUint64(key) + WeightMessageUint64(ValueMessage.Define(value)) + weightSeq
          <= MaxTotalBucketWeightUint64()) {
        return ref;
      }

      ref := childref;
      node := childNode.value;
    }
  }

  method InsertKeyValue(k: ImplConstants, s: ImplVariables, key: Key, value: Value)
  returns (success: bool)
  requires Inv(k, s)
  requires s.ready
  requires BT.G.Root() in s.cache.I()
  requires |s.ephemeralIndirectionTable.I().graph| <= IndirectionTableModel.MaxSize() - 1
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), success) == InsertModel.InsertKeyValue(Ic(k), old(s.I()), key, value)
  {
    InsertModel.reveal_InsertKeyValue();

    BookkeepingModel.lemmaChildrenConditionsOfNode(Ic(k), s.I(), BT.G.Root());
    //Native.BenchmarkingUtil.start("passiveAggressive calc");
    //var ref := passiveAggressive(k, s, key, value);
    var ref := BT.G.Root();
    //Native.BenchmarkingUtil.end("passiveAggressive calc");

    if s.frozenIndirectionTable != null {
      var b := s.frozenIndirectionTable.HasEmptyLoc(ref);
      if b {
        success := false;
        print "giving up; can't dirty root because frozen isn't written";
        return;
      }
    }

    var msg := ValueMessage.Define(value);
    s.cache.InsertKeyValue(ref, key, msg);

    writeBookkeepingNoSuccsUpdate(k, s, ref);

    success := true;
  }

  method insert(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, key: Key, value: Value)
  returns (success: bool)
  requires io.initialized()
  requires Inv(k, s)
  requires io !in s.Repr()
  modifies s.Repr()
  modifies io
  ensures WellUpdated(s)
  ensures InsertModel.insert(Ic(k), old(s.I()), old(IIO(io)), key, value, s.I(), success, IIO(io))
  {
    InsertModel.reveal_insert();

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

    if WeightKeyUint64(key) + WeightMessageUint64(ValueMessage.Define(value)) + weightSeq
        <= MaxTotalBucketWeightUint64() {
      NativeBenchmarking.start("InsertImpl-InsertKeyValue");
      success := InsertKeyValue(k, s, key, value);
      NativeBenchmarking.end("InsertImpl-InsertKeyValue");
    } else {
      NativeBenchmarking.start("InsertImpl-runFlushPolicy");
      runFlushPolicy(k, s, io);
      NativeBenchmarking.end("InsertImpl-runFlushPolicy");
      success := false;
    }
  }
}
