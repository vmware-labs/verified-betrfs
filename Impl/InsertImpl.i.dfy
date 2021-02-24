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
  import InsertModel
  import opened StateBCImpl
  import opened StateSectorImpl
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

  import IT = IndirectionTable
  import opened NodeImpl
  import opened BoundedPivotsLib

  import opened InterpretationDiskOps
  import opened ViewOp
  import opened DiskOpModel

  method InsertKeyValue(linear inout s: ImplVariables, key: Key, value: Value)
  returns (success: bool)
  requires old_s.BCInv() && old_s.Ready?
  requires BT.G.Root() in old_s.cache.I()
  requires |old_s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 1
  requires BoundedKey(old_s.cache.I()[BT.G.Root()].pivotTable, key)
  ensures s.W() && s.Ready?
  ensures (s.IBlockCache(), success) == InsertModel.InsertKeyValue(old_s.IBlockCache(), key, value)
  {
    reveal InsertModel.InsertKeyValue();
    BookkeepingModel.lemmaChildrenConditionsOfNode(s.IBlockCache(), BT.G.Root());
    success := true;

    if s.frozenIndirectionTable.lSome? {
      var b := s.frozenIndirectionTable.value.HasEmptyLoc(BT.G.Root());
      if b {
        success := false;
        print "giving up; can't dirty root because frozen isn't written";
      }
    }

    if (success) {
      var msg := ValueMessage.Define(value);
      inout s.cache.InsertKeyValue(BT.G.Root(), key, msg);

      writeBookkeepingNoSuccsUpdate(inout s, BT.G.Root());
    }
  }

  //TODO Check to see if casing on success is OK
  //     Before it returned but cant do that with linear
  method insert(linear inout s: ImplVariables, io: DiskIOHandler, key: Key, value: Value)
  returns (success: bool)
  requires io.initialized()
  requires old_s.BCInv() && old_s.Ready?
  modifies io
  ensures s.W()

  ensures ValidDiskOp(diskOp(IIO(io)))
  ensures IDiskOp(diskOp(IIO(io))).jdop.NoDiskOp?
  ensures success ==>
    BBC.Next(old_s.IBlockCache(), s.IBlockCache(), IDiskOp(diskOp(IIO(io))).bdop, AdvanceOp(UI.PutOp(key, value), success))
  ensures !success ==>
    IOModel.betree_next_dop(old_s.IBlockCache(), s.IBlockCache(), IDiskOp(diskOp(IIO(io))).bdop)
  {
    success := true;

    var indirectionTableSize := s.ephemeralIndirectionTable.GetSize();
    if (!(indirectionTableSize <= IT.MaxSizeUint64() - 3)) {
      success := false;
    }

    if (success){
      var rootLookup := s.cache.InCache(BT.G.Root());
      if !rootLookup {
        if s.TotalCacheSize() <= MaxCacheSizeUint64() - 1 {
          PageInNodeReq(inout s, io, BT.G.Root());
          success := false;
        } else {
          print "insert: root not in cache, but cache is full\n";
          success := false;
        }
      }
    }

    if (success) {
      var pivots, _ := s.cache.GetNodeInfo(BT.G.Root());
      var bounded := ComputeBoundedKey(pivots, key);
      if !bounded {
        success := false;
        print "giving up; can't insert key at root because root is incorrects";
      }
    }

    if success {
      var weightSeq := s.cache.NodeBucketsWeight(BT.G.Root());
      if WeightKeyUint64(key) + WeightMessageUint64(ValueMessage.Define(value)) + weightSeq
        <= MaxTotalBucketWeightUint64() {
          success := InsertKeyValue(inout s, key, value);
          InsertModel.InsertKeyValueCorrect(old_s.IBlockCache(), key, value, success);
      } else {
        runFlushPolicy(inout s, io);
        success := false;
      }
    }

    if !success {
      assert IOModel.noop(s.IBlockCache(), s.IBlockCache());
    }
  }
}
