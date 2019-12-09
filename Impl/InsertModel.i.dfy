include "CacheModel.i.dfy"
include "FlushPolicyModel.i.dfy"

module ImplModelInsert { 
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelCache
  import opened ImplModelFlushPolicy

  import opened Options
  import opened Maps
  import opened Sets
  import opened Sequences
  import opened NativeTypes

  import opened BucketWeights
  import opened BucketsLib
  import opened Bounds

  import PBS = PivotBetreeSpec`Spec

  // == insert ==

  function {:opaque} NodeInsertKeyValue(node: Node, key: MS.Key, msg: Message) : Node
  requires WFNode(node)
  {
    var r := Pivots.Route(node.pivotTable, key);
    var bucket := node.buckets[r];
    var newBucket := BucketInsert(bucket, key, msg);
    node.(buckets := node.buckets[r := newBucket])
  }

  function {:opaque} CacheInsertKeyValue(cache: map<BT.G.Reference, Node>, ref: BT.G.Reference, key: MS.Key, msg: Message) : map<BT.G.Reference, Node>
  requires ref in cache
  requires WFNode(cache[ref])
  {
    cache[ref := NodeInsertKeyValue(cache[ref], key, msg)]
  }

  function {:opaque} InsertKeyValue(k: Constants, s: Variables, key: MS.Key, value: MS.Value)
  : (Variables, bool)
  requires Inv(k, s)
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

  lemma InsertKeyValueCorrect(k: Constants, s: Variables, key: MS.Key, value: MS.Value)
  requires Inv(k, s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  requires |s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 1
  requires WeightKey(key) + WeightMessage(Messages.Define(value)) +
      WeightBucketList(s.cache[BT.G.Root()].buckets) 
      <= MaxTotalBucketWeight()
  ensures var (s', success) := InsertKeyValue(k, s, key, value);
      && WFVars(s')
      && M.Next(Ik(k), IVars(s), IVars(s'), if success then UI.PutOp(key, value) else UI.NoOp, D.NoDiskOp)
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
      assert noop(k, IVars(s), IVars(s));
      return;
    }

    var msg := Messages.Define(value);
    var root := s.cache[BT.G.Root()];
    var r := Pivots.Route(root.pivotTable, key);
    var bucket := root.buckets[r];
    var newBucket := bucket[key := msg];
    var newRoot := root.(buckets := root.buckets[r := newBucket]);
    var newCache := s.cache[BT.G.Root() := newRoot];

    WeightBucketListInsert(root.buckets, root.pivotTable, key, msg);

    assert BC.BlockPointsToValidReferences(INode(root), IIndirectionTable(s.ephemeralIndirectionTable).graph);

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
    assert WFVars(s');

    assert BC.Dirty(Ik(k), IVars(s), IVars(s'), BT.G.Root(), newroot);
    assert BC.OpStep(Ik(k), IVars(s), IVars(s'), BT.G.WriteOp(BT.G.Root(), newroot));
    assert BT.ValidBetreeStep(btStep);
    assert BC.OpStep(Ik(k), IVars(s), IVars(s'), BT.BetreeStepOps(btStep)[0]);
    assert BC.OpTransaction(Ik(k), IVars(s), IVars(s'), BT.BetreeStepOps(btStep));
    assert BBC.BetreeMove(Ik(k), IVars(s), IVars(s'), UI.PutOp(key, value), SD.NoDiskOp, btStep);
    assert stepsBetree(k, IVars(s), IVars(s'), UI.PutOp(key, value), btStep);

    assert M.NextStep(Ik(k), IVars(s), IVars(s'), UI.PutOp(key, value), D.NoDiskOp,
        M.Step(BBC.BetreeMoveStep(btStep)));
  }

  predicate {:opaque} insert(k: Constants, s: Variables, io: IO, key: MS.Key, value: MS.Value,
      s': Variables, success: bool, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  {
    if (s.Unready?) then (
      && (s', io') == PageInIndirectionTableReq(k, s, io)
      && success == false
    ) else if !(|s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 3) then (
      && s' == s
      && io' == io
      && success == false
    ) else if (BT.G.Root() !in s.cache) then (
      if TotalCacheSize(s) <= MaxCacheSize() - 1 then (
        && (s', io') == PageInReq(k, s, io, BT.G.Root())
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

  lemma insertCorrect(k: Constants, s: Variables, io: IO, key: MS.Key, value: MS.Value,
      s': Variables, success: bool, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires insert(k, s, io, key, value, s', success, io');
  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'),
        if success then UI.PutOp(key, value) else UI.NoOp,
        diskOp(io'))
  {
    reveal_insert();

    if (s.Unready?) {
      PageInIndirectionTableReqCorrect(k, s, io);
    } else if !(|s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 3) {
      assert noop(k, IVars(s), IVars(s));
    } else if (BT.G.Root() !in s.cache) {
      if TotalCacheSize(s) <= MaxCacheSize() - 1 {
        PageInReqCorrect(k, s, io, BT.G.Root());
      } else {
        assert noop(k, IVars(s), IVars(s));
      }
    } else if WeightKey(key) + WeightMessage(Messages.Define(value)) +
        WeightBucketList(s.cache[BT.G.Root()].buckets) 
        <= MaxTotalBucketWeight() {
      InsertKeyValueCorrect(k, s, key, value);
    } else {
      runFlushPolicyCorrect(k, s, io, s', io');
    }
  }

}
