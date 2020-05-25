include "BookkeepingModel.i.dfy"
include "FlushPolicyModel.i.dfy"

module InsertModel { 
  import opened StateModel
  import opened IOModel
  import opened BookkeepingModel
  import opened FlushPolicyModel
  import opened NodeModel
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

  import PBS = PivotBetreeSpec`Spec

  // == insert ==

  function {:opaque} InsertKeyValue(k: Constants, s: BCVariables, key: Key, value: Value)
  : (BCVariables, bool)
  requires BCInv(k, s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  requires |s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 1
  {
    lemmaChildrenConditionsOfNode(k, s, BT.G.Root());

    if (
      && s.frozenIndirectionTable.Some?
      && IndirectionTableModel.HasEmptyLoc(s.frozenIndirectionTable.value, BT.G.Root())
    ) then (
      (s, false)
    ) else (
      var msg := Messages.Define(value);
      var newCache := CacheInsertKeyValue(s.cache, BT.G.Root(), key, msg);

      var s0 := s.(cache := newCache);
      var s' := writeBookkeepingNoSuccsUpdate(k, s0, BT.G.Root());
      (s', true)
    )
  }

  lemma InsertKeyValueCorrect(k: Constants, s: BCVariables, key: Key, value: Value, replay: bool)
  requires BCInv(k, s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  requires |s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 1
  requires WeightKey(key) + WeightMessage(Messages.Define(value)) +
      WeightBucketList(s.cache[BT.G.Root()].buckets) 
      <= MaxTotalBucketWeight()
  ensures var (s', success) := InsertKeyValue(k, s, key, value);
      && WFBCVars(s')
      && (success ==>
        BBC.Next(Ik(k).bc, IBlockCache(s), IBlockCache(s'),
          BlockDisk.NoDiskOp,
          AdvanceOp(UI.PutOp(key, value), replay))
      )
      && (!success ==>
        betree_next(k, IBlockCache(s), IBlockCache(s'))
      )
  {
    reveal_InsertKeyValue();
    reveal_CacheInsertKeyValue();
    reveal_NodeInsertKeyValue();
    if (
      && s.frozenIndirectionTable.Some?
      && IndirectionTableModel.HasEmptyLoc(s.frozenIndirectionTable.value, BT.G.Root())
    ) {
      assert (s.frozenIndirectionTable.Some? && BT.G.Root() in IIndirectionTable(s.frozenIndirectionTable.value).graph) &&
          !(BT.G.Root() in IIndirectionTable(s.frozenIndirectionTable.value).locs);
      // TODO write out the root here instead of giving up
      assert noop(k, IBlockCache(s), IBlockCache(s));
      return;
    }

    var msg := Messages.Define(value);
    var root := s.cache[BT.G.Root()];
    var r := Pivots.Route(root.pivotTable, key);
    var bucket := root.buckets[r];
    var newBucket := B(bucket.b[key := msg]);
    var newRoot := root.(buckets := root.buckets[r := newBucket]);
    var newCache := s.cache[BT.G.Root() := newRoot];

    WeightBucketListInsert(root.buckets, root.pivotTable, key, msg);

    assert BC.BlockPointsToValidReferences(INode(root), IIndirectionTable(s.ephemeralIndirectionTable).graph);

    //reveal_WFBucket();
    assert WFBucket(newBucket);
    assert WFNode(newRoot);

    var s0 := s.(cache := newCache);
    var s' := writeBookkeepingNoSuccsUpdate(k, s0, BT.G.Root());

    reveal_writeBookkeepingNoSuccsUpdate();
    writeCorrect(k, s0, BT.G.Root(), newRoot);

    var oldroot := INode(root);
    var newroot := INode(newRoot);

    assert newroot == BT.AddMessageToNode(oldroot, key, msg);

    assert BT.G.Successors(newroot) == BT.G.Successors(oldroot);

    var btStep := BT.BetreeInsert(BT.MessageInsertion(key, msg, oldroot));
    assert BT.ValidInsertion(BT.MessageInsertion(key, msg, oldroot));

    assert WFNode(newRoot);
    assert WFBCVars(s');

    assert BC.Dirty(Ik(k).bc, IBlockCache(s), IBlockCache(s'), BT.G.Root(), newroot);
    assert BC.OpStep(Ik(k).bc, IBlockCache(s), IBlockCache(s'), BT.G.WriteOp(BT.G.Root(), newroot));
    assert BT.ValidBetreeStep(btStep);
    assert BC.OpStep(Ik(k).bc, IBlockCache(s), IBlockCache(s'), BT.BetreeStepOps(btStep)[0]);
    assert BC.OpTransaction(Ik(k).bc, IBlockCache(s), IBlockCache(s'), BT.BetreeStepOps(btStep));
    assert BBC.BetreeMove(Ik(k).bc, IBlockCache(s), IBlockCache(s'), BlockDisk.NoDiskOp, AdvanceOp(UI.PutOp(key, value), replay), btStep);
    assert stepsBetree(k, IBlockCache(s), IBlockCache(s'), AdvanceOp(UI.PutOp(key, value), replay), btStep);
  }

  predicate {:opaque} insert(k: Constants, s: BCVariables, io: IO, key: Key, value: Value,
      s': BCVariables, success: bool, io': IO)
  requires io.IOInit?
  requires s.Ready?
  requires BCInv(k, s)
  {
    if !(|s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 3) then (
      && s' == s
      && io' == io
      && success == false
    ) else if (BT.G.Root() !in s.cache) then (
      if TotalCacheSize(s) <= MaxCacheSize() - 1 then (
        && (s', io') == PageInNodeReq(k, s, io, BT.G.Root())
        && success == false
      ) else (
        // TODO rule out this case?
        && s' == s
        && io' == io
        && success == false
      )
    ) else if WeightKey(key) + WeightMessage(Messages.Define(value)) +
        WeightBucketList(s.cache[BT.G.Root()].buckets) 
        <= MaxTotalBucketWeight() then (
      && (s', success) == InsertKeyValue(k, s, key, value)
      && io' == io
    ) else (
      && runFlushPolicy(k, s, io, s', io')
      && success == false
    )
  }

  lemma insertCorrect(k: Constants, s: BCVariables, io: IO, key: Key, value: Value,
      s': BCVariables, success: bool, io': IO, replay: bool)
  requires io.IOInit?
  requires s.Ready?
  requires BCInv(k, s)
  requires insert(k, s, io, key, value, s', success, io');
  ensures WFBCVars(s')
  ensures ValidDiskOp(diskOp(io'))
  ensures IDiskOp(diskOp(io')).jdop.NoDiskOp?

  ensures success ==>
        BBC.Next(Ik(k).bc, IBlockCache(s), IBlockCache(s'),
          IDiskOp(diskOp(io')).bdop,
          AdvanceOp(UI.PutOp(key, value), replay))
  ensures !success ==>
        betree_next_dop(k, IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop)
  {
    reveal_insert();

    if !(|s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 3) {
      assert noop(k, IBlockCache(s), IBlockCache(s));
    } else if (BT.G.Root() !in s.cache) {
      if TotalCacheSize(s) <= MaxCacheSize() - 1 {
        PageInNodeReqCorrect(k, s, io, BT.G.Root());
      } else {
        assert noop(k, IBlockCache(s), IBlockCache(s));
      }
    } else if WeightKey(key) + WeightMessage(Messages.Define(value)) +
        WeightBucketList(s.cache[BT.G.Root()].buckets) 
        <= MaxTotalBucketWeight() {
      InsertKeyValueCorrect(k, s, key, value, replay);
    } else {
      runFlushPolicyCorrect(k, s, io, s', io');
    }
  }
}
