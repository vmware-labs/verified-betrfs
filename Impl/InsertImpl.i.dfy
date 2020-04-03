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
  import opened DiskOpImpl
  import opened MainDiskIOHandler

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

    if s.frozenIndirectionTable != null {
      var b := s.frozenIndirectionTable.HasEmptyLoc(BT.G.Root());
      if b {
        success := false;
        print "giving up; can't dirty root because frozen isn't written";
        return;
      }
    }

    var msg := ValueMessage.Define(value);
    s.cache.InsertKeyValue(BT.G.Root(), key, msg);

    writeBookkeepingNoSuccsUpdate(k, s, BT.G.Root());

    success := true;
  }

  method insert(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, key: Key, value: Value)
  returns (success: bool)
  requires io.initialized()
  requires Inv(k, s)
  requires io !in s.Repr()
  requires s.ready
  modifies s.Repr()
  modifies io
  ensures WellUpdated(s)
  ensures InsertModel.insert(Ic(k), old(s.I()), old(IIO(io)), key, value, s.I(), success, IIO(io))
  {
    InsertModel.reveal_insert();

    var indirectionTableSize := s.ephemeralIndirectionTable.GetSize();
    if (!(indirectionTableSize <= IndirectionTableModel.MaxSizeUint64() - 3)) {
      success := false;
      return;
    }

    var rootLookup := s.cache.GetOpt(BT.G.Root());
    if (rootLookup.None?) {
      if TotalCacheSize(s) <= MaxCacheSizeUint64() - 1 {
        PageInNodeReq(k, s, io, BT.G.Root());
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
      success := InsertKeyValue(k, s, key, value);
    } else {
      runFlushPolicy(k, s, io);
      success := false;
    }
  }
}
