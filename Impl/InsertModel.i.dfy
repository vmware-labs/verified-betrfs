// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "BookkeepingModel.i.dfy"
include "FlushPolicyModel.i.dfy"

module InsertModel { 
  import opened StateSectorModel

  import opened IOModel
  import opened BookkeepingModel
  import opened FlushPolicyModel
  import opened InterpretationDiskOps
  import opened ViewOp
  import opened DiskOpModel

  import opened Options
  import opened Maps
  import opened Sets
  import opened Sequences
  import opened NativeTypes

  import opened BucketWeights
  import opened BucketsLib
  import opened Bounds
  import opened KeyType
  import opened ValueMessage
  import opened BoundedPivotsLib

  import IT = IndirectionTable

  import BT = PivotBetreeSpec`Internal
  
  import Messages = ValueMessage`Internal
  import Pivots = BoundedPivotsLib

  // == insert ==

  function {:opaque} InsertKeyValue(s: BBC.Variables, key: Key, value: Value)
  : (BBC.Variables, bool)
  requires BBC.Inv(s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  requires var root := s.cache[BT.G.Root()];
    && WFNode(root)
    && BoundedKey(root.pivotTable, key)
  {
    lemmaChildrenConditionsOfNode(s, BT.G.Root());

    if (
      && s.frozenIndirectionTable.Some?
      && s.frozenIndirectionTable.value.hasEmptyLoc(BT.G.Root())
    ) then (
      (s, false)
    ) else (
      var msg := Messages.Define(value);
      var rootref := BT.G.Root();
      var newCache := s.cache[rootref := BT.NodeInsertKeyValue(s.cache[rootref], key, msg)];

      var s0 := s.(cache := newCache);
      var s' := writeBookkeepingNoSuccsUpdate(s0, BT.G.Root());
      (s', true)
    )
  }

  lemma InsertKeyValueCorrect(s: BBC.Variables, key: Key, value: Value, replay: bool)
  requires InsertKeyValue.requires(s, key, value)
  requires WeightKey(key) + WeightMessage(Messages.Define(value)) +
      WeightBucketList(s.cache[BT.G.Root()].buckets) 
      <= MaxTotalBucketWeight()
  ensures var (s', success) := InsertKeyValue(s, key, value);
      && (success ==>
        BBC.Next(s, s',
          BlockDisk.NoDiskOp,
          AdvanceOp(UI.PutOp(key, value), replay))
      )
      && (!success ==>
        betree_next(s, s')
      )
      && (StateBCImpl.WFCache(s'.cache))
      && s.totalCacheSize() == s'.totalCacheSize()
  {
    reveal_InsertKeyValue();
    BT.reveal_NodeInsertKeyValue();
    if (
      && s.frozenIndirectionTable.Some?
      && s.frozenIndirectionTable.value.hasEmptyLoc(BT.G.Root())
    ) {
      assert (s.frozenIndirectionTable.Some? && BT.G.Root() in s.frozenIndirectionTable.value.graph) &&
          !(BT.G.Root() in s.frozenIndirectionTable.value.locs);
      // TODO write out the root here instead of giving up
      assert noop(s, s);
      return;
    }

    var msg := Messages.Define(value);
    var root := s.cache[BT.G.Root()];
    var r := Pivots.Route(root.pivotTable, key);
    var bucket := root.buckets[r];

    assert WFBucket(bucket);

    var old_map := bucket.as_map();
    var new_map := old_map[key := msg];
    var newBucket := B(new_map);


    assert WFBucket(newBucket) by {
      assert WFBucketMap(old_map);

      assert old_map.Keys + {key} == new_map.Keys;
      if key !in old_map {
        assert old_map.Values + {msg} == new_map.Values;
        assert WFBucketMap(new_map);
      } else {
        if exists key' :: key' in old_map && key' != key && old_map[key] == old_map[key'] {
          assert old_map[key] in new_map.Values;
          assert old_map.Values + {msg} == new_map.Values;
          assert WFBucketMap(new_map);
        } else {
          assert old_map.Values - {old_map[key]} + {msg} == new_map.Values;
          assert WFBucketMap(new_map);
        }
      }
    }

    var newRoot := root.(buckets := root.buckets[r := newBucket]);
    var newCache := s.cache[BT.G.Root() := newRoot];

    WeightBucketListInsert(root.buckets, root.pivotTable, key, msg);

    assert BC.BlockPointsToValidReferences(root, s.ephemeralIndirectionTable.graph);

    assert WFNode(newRoot);

    var s0 := s.(cache := newCache);
    var s' := writeBookkeepingNoSuccsUpdate(s0, BT.G.Root());

    reveal_writeBookkeepingNoSuccsUpdate();
    writeCorrect(s0, BT.G.Root(), newRoot);

    var oldroot := root;
    var newroot := newRoot;

    assert newroot == BT.AddMessageToNode(oldroot, key, msg);

    assert BT.G.Successors(newroot) == BT.G.Successors(oldroot);

    var btStep := BT.BetreeInsert(BT.MessageInsertion(key, msg, oldroot));
    assert BT.ValidInsertion(BT.MessageInsertion(key, msg, oldroot));

    assert WFNode(newRoot);
    // assert WFBCVars(s');

    assert BC.Dirty(s, s', BT.G.Root(), newroot);
    assert BC.OpStep(s, s', BT.G.WriteOp(BT.G.Root(), newroot));
    assert BT.ValidBetreeStep(btStep);
    assert BC.OpStep(s, s', BT.BetreeStepOps(btStep)[0]);
    assert BC.OpTransaction(s, s', BT.BetreeStepOps(btStep));
    assert BBC.BetreeMove(s, s', BlockDisk.NoDiskOp, AdvanceOp(UI.PutOp(key, value), replay), btStep);
    assert stepsBetree(s, s', AdvanceOp(UI.PutOp(key, value), replay), btStep);
  }
/*

  predicate {:opaque} insert(s: BBC.Variables, io: IO, key: Key, value: Value,
      s': BBC.Variables, success: bool, io': IO)
  requires io.IOInit?
  requires s.Ready?
  requires BCInv(s)
  {
    if !(|s.ephemeralIndirectionTable.graph| <= IT.MaxSize() - 3) then (
      && s' == s
      && io' == io
      && success == false
    ) else if (BT.G.Root() !in s.cache) then (
      if TotalCacheSize(s) <= MaxCacheSize() - 1 then (
        && (s', io') == PageInNodeReq(s, io, BT.G.Root())
        && success == false
      ) else (
        // TODO rule out this case?
        && s' == s
        && io' == io
        && success == false
      )
    ) else if !BoundedKey(s.cache[BT.G.Root()].pivotTable, key) then (
        && s' == s
        && io' == io
        && success == false
    ) else if WeightKey(key) + WeightMessage(Messages.Define(value)) +
        WeightBucketList(s.cache[BT.G.Root()].buckets) 
        <= MaxTotalBucketWeight() then (
      && (s', success) == InsertKeyValue(s, key, value)
      && io' == io
    ) else (
      && runFlushPolicy(s, io, s', io')
      && success == false
    )
  }

  lemma insertCorrect(s: BBC.Variables, io: IO, key: Key, value: Value,
      s': BBC.Variables, success: bool, io': IO, replay: bool)
  requires insert.requires(s, io, key, value, s', success, io')
  requires insert(s, io, key, value, s', success, io');
  ensures WFBCVars(s')
  ensures ValidDiskOp(diskOp(io'))
  ensures IDiskOp(diskOp(io')).jdop.NoDiskOp?

  ensures success ==>
        BBC.Next(s, s',
          IDiskOp(diskOp(io')).bdop,
          AdvanceOp(UI.PutOp(key, value), replay))
  ensures !success ==>
        betree_next_dop(s, s', IDiskOp(diskOp(io')).bdop)
  {
    reveal_insert();

    if !(|s.ephemeralIndirectionTable.graph| <= IT.MaxSize() - 3) {
      assert noop(s, s);
    } else if (BT.G.Root() !in s.cache) {
      if TotalCacheSize(s) <= MaxCacheSize() - 1 {
        PageInNodeReqCorrect(s, io, BT.G.Root());
      } else {
        assert noop(s, s);
      }
    } else if !BoundedKey(s.cache[BT.G.Root()].pivotTable, key) {
      assert noop(s, s);
      return;
    } else if WeightKey(key) + WeightMessage(Messages.Define(value)) +
        WeightBucketList(s.cache[BT.G.Root()].buckets) 
        <= MaxTotalBucketWeight() {
        InsertKeyValueCorrect(s, key, value, replay);
    } else {
      runFlushPolicyCorrect(s, io, s', io');
    }
  }
  */
}
