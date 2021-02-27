// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

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

  method InsertKeyValue(linear inout s: ImplVariables, key: Key, value: Value)
  returns (success: bool)
  requires old_s.Inv()
  requires old_s.Ready?
  requires BT.G.Root() in old_s.cache.I()
  requires |old_s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 1
  requires BoundedKey(old_s.cache.I()[BT.G.Root()].pivotTable, key)
  ensures s.W()
  ensures (s.I(), success) == InsertModel.InsertKeyValue(old_s.I(), key, value)
  {
    InsertModel.reveal_InsertKeyValue();

    BookkeepingModel.lemmaChildrenConditionsOfNode(s.I(), BT.G.Root());
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
  requires old_s.Inv()
  requires old_s.Ready?
  modifies io
  ensures s.W()
  ensures InsertModel.insert(old_s.I(), old(IIO(io)), key, value, s.I(), success, IIO(io))
  {
    InsertModel.reveal_insert();
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

    if (success) {
      var weightSeq := s.cache.NodeBucketsWeight(BT.G.Root());
      if WeightKeyUint64(key) + WeightMessageUint64(ValueMessage.Define(value)) + weightSeq
        <= MaxTotalBucketWeightUint64() {
          success := InsertKeyValue(inout s, key, value);
      } else {
        runFlushPolicy(inout s, io);
        success := false;
      }
    }
  }
}
