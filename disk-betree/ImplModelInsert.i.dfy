include "ImplModelCache.i.dfy"
include "ImplModelFlushPolicy.i.dfy"

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

  function removeLBAFromIndirectionTable(table: IndirectionTable, ref: BT.G.Reference) : IndirectionTable
  {
    if ref in table then (
      var lbaGraph := table[ref];
      var (lba, graph) := lbaGraph;
      table[ref := (None, graph)]
    ) else (
      table
    )
  }

  function {:opaque} InsertKeyValue(k: Constants, s: Variables, key: MS.Key, value: MS.Value)
  : (Variables, bool)
  requires Inv(k, s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  {
    if (
      && s.frozenIndirectionTable.Some?
      && BT.G.Root() in s.frozenIndirectionTable.value
      && var rootInFrozenLbaGraph := s.frozenIndirectionTable.value[BT.G.Root()];
      && rootInFrozenLbaGraph.0.None?
    ) then (
      (s, false)
    ) else (
      var msg := Messages.Define(value);
      var newRootBucket := s.rootBucket[key := msg];

      var newW := s.rootBucketWeightBound + WeightKey(key) as uint64 + WeightMessage(msg) as uint64;

      var s' := s.(rootBucket := newRootBucket)
          .(rootBucketWeightBound := newW)
          .(ephemeralIndirectionTable := removeLBAFromIndirectionTable(s.ephemeralIndirectionTable, BT.G.Root()));
      (s', true)
    )
  }

  lemma LemmaInsertToRootBucket(node: Node, rootBucket: map<Key, Message>, rootBucket': map<Key, Message>, key: Key, msg: Message)
  requires WFNode(node)
  requires BT.WFNode(INodeRoot(node, rootBucket))
  requires rootBucket' == rootBucket[key := msg]
  requires msg.Define?
  ensures INodeRoot(node, rootBucket') == BT.AddMessageToNode(INodeRoot(node, rootBucket), key, msg)
  {
    BucketListInsertBucketListFlush(rootBucket, KMTable.ISeq(node.buckets), node.pivotTable, key, msg);
    /*assert BucketListFlush(TTT.I(rootBucket'), KMTable.ISeq(node.buckets), node.pivotTable)
        == BucketListFlush(TTT.I(rootBucket)[key := msg], KMTable.ISeq(node.buckets), node.pivotTable)
        == BucketListFlush(BucketInsert(TTT.I(rootBucket), key, msg), KMTable.ISeq(node.buckets), node.pivotTable)
        == BucketListInsert(BucketListFlush(TTT.I(rootBucket), KMTable.ISeq(node.buckets), node.pivotTable), node.pivotTable, key, msg);*/
  }

  lemma InsertKeyValueCorrect(k: Constants, s: Variables, key: MS.Key, value: MS.Value)
  requires Inv(k, s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  requires WeightKey(key) + WeightMessage(Messages.Define(value)) +
      s.rootBucketWeightBound as int +
      WeightBucketList(KMTable.ISeq(s.cache[BT.G.Root()].buckets)) 
      <= MaxTotalBucketWeight()
  ensures var (s', success) := InsertKeyValue(k, s, key, value);
      && WFVars(s')
      && M.Next(Ik(k), IVars(s), IVars(s'), if success then UI.PutOp(key, value) else UI.NoOp, D.NoDiskOp)
  {
    reveal_InsertKeyValue();
    if (
      && s.frozenIndirectionTable.Some?
      && BT.G.Root() in s.frozenIndirectionTable.value
      && var rootInFrozenLbaGraph := s.frozenIndirectionTable.value[BT.G.Root()];
      && rootInFrozenLbaGraph.0.None?
    ) {
      assert (s.frozenIndirectionTable.Some? && BT.G.Root() in IIndirectionTable(s.frozenIndirectionTable.value).graph) &&
          !(BT.G.Root() in IIndirectionTable(s.frozenIndirectionTable.value).locs);
      // TODO write out the root here instead of giving up
      assert noop(k, IVars(s), IVars(s));
      return;
    }

    var msg := Messages.Define(value);

    WeightBucketPut(s.rootBucket, key, msg);

    var baseroot := s.cache[BT.G.Root()];

    var r := Pivots.Route(baseroot.pivotTable, key);
    var bucket := baseroot.buckets[r];

    assert BC.BlockPointsToValidReferences(INodeRoot(baseroot, s.rootBucket), IIndirectionTable(s.ephemeralIndirectionTable).graph);

    var newRootBucket := s.rootBucket[key := msg];

    var newW := s.rootBucketWeightBound + WeightKey(key) as uint64 + WeightMessage(msg) as uint64;

    var s' := s.(rootBucket := newRootBucket)
        .(rootBucketWeightBound := newW)
        .(ephemeralIndirectionTable := removeLBAFromIndirectionTable(s.ephemeralIndirectionTable, BT.G.Root()));

    var oldroot := INodeRoot(baseroot, s.rootBucket);
    var newroot := INodeRoot(baseroot, newRootBucket);

    LemmaInsertToRootBucket(baseroot, s.rootBucket, newRootBucket, key, msg);
    assert newroot == BT.AddMessageToNode(oldroot, key, msg);

    assert BT.G.Successors(newroot) == BT.G.Successors(oldroot);

    WeightBucketListFlush(s.rootBucket, KMTable.ISeq(baseroot.buckets), oldroot.pivotTable);

    var btStep := BT.BetreeInsert(BT.MessageInsertion(key, msg, oldroot));
    assert BT.ValidInsertion(BT.MessageInsertion(key, msg, oldroot));

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
        s.rootBucketWeightBound as int +
        WeightBucketList(KMTable.ISeq(s.cache[BT.G.Root()].buckets)) 
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
    } else if (BT.G.Root() !in s.cache) {
      if TotalCacheSize(s) <= MaxCacheSize() - 1 {
        PageInReqCorrect(k, s, io, BT.G.Root());
      } else {
        assert noop(k, IVars(s), IVars(s));
      }
    } else if WeightKey(key) + WeightMessage(Messages.Define(value)) +
        s.rootBucketWeightBound as int +
        WeightBucketList(KMTable.ISeq(s.cache[BT.G.Root()].buckets)) 
        <= MaxTotalBucketWeight() {
      InsertKeyValueCorrect(k, s, key, value);
    } else {
      runFlushPolicyCorrect(k, s, io, s', io');
    }
  }

}
