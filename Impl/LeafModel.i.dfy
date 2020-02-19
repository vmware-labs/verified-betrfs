include "BookkeepingModel.i.dfy"

module LeafModel { 
  import opened StateModel
  import opened IOModel
  import opened BookkeepingModel

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import PivotsLib
  import KVList
  import PivotBetreeSpec`Internal

  import opened NativeTypes

  function {:opaque} repivotLeaf(k: Constants, s: Variables, ref: BT.G.Reference, node: Node)
  : (s': Variables)
  requires Inv(k, s)
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable.graph
  requires ref in s.cache
  requires node == s.cache[ref]
  requires node.children.None?
  requires |node.buckets| == 1
  requires |s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 1
  {
    if (
      && s.frozenIndirectionTable.Some?
      && IndirectionTableModel.HasEmptyLoc(s.frozenIndirectionTable.value, ref)
    ) then (
      s
    ) else (
      var pivot := getMiddleKey(node.buckets[0]);
      var pivots := [pivot];

      var buckets' := [
          SplitBucketLeft(node.buckets[0], pivot),
          SplitBucketRight(node.buckets[0], pivot)
      ];
      var newnode := Node(pivots, None, buckets');
      var s1 := writeBookkeeping(k, s, ref, None);
      var s' := s1.(cache := s1.cache[ref := newnode]);
      s'
    )
  }

  lemma repivotLeafCorrect(k: Constants, s: Variables, ref: BT.G.Reference, node: Node)
  requires Inv(k, s)
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable.graph
  requires ref in s.cache
  requires node == s.cache[ref]
  requires node.children.None?
  requires |node.buckets| == 1
  requires |s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 1
  ensures var s' := repivotLeaf(k, s, ref, node);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, D.NoDiskOp)
  {
    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();
    var s' := repivotLeaf(k, s, ref, node);

    reveal_repivotLeaf();

    if (
      && s.frozenIndirectionTable.Some?
      && IndirectionTableModel.HasEmptyLoc(s.frozenIndirectionTable.value, ref)
    ) {
      assert s' == s;
      assert WFVars(s');
      assert noop(k, IVars(s), IVars(s));
      return;
    }

    var pivot := getMiddleKey(node.buckets[0]);
    var pivots := [pivot];

    KVList.WFPivotsOfGetMiddleKey(node.buckets[0]);

    var buckets' := [
        SplitBucketLeft(node.buckets[0], pivot),
        SplitBucketRight(node.buckets[0], pivot)
    ];

    reveal_WFBucket();

    var newnode := Node(pivots, None, buckets');
    var s1 := writeWithNode(k, s, ref, newnode);
    reveal_writeBookkeeping();

    assert s1 == s';

    WeightBucketLeBucketList(node.buckets, 0);
    WeightSplitBucketAdditiveLe(node.buckets[0], pivot);
    WeightBucketList2(
        SplitBucketLeft(node.buckets[0], pivot),
        SplitBucketRight(node.buckets[0], pivot));

    assert WFNode(newnode);
    writeCorrect(k, s, ref, newnode);
    assert WFVars(s');

    //assert IVars(s1).cache == IVars(s).cache[ref := INode(newnode)];

    assert JoinBucketList(node.buckets).b
        == MapUnion(JoinBucketList([]).b, node.buckets[0].b)
        == MapUnion(map[], node.buckets[0].b)
        == node.buckets[0].b;
    assert SplitBucketOnPivots(JoinBucketList(node.buckets), pivots)
        == SplitBucketOnPivots(node.buckets[0], pivots)
        == buckets';

    assert PivotBetreeSpec.ApplyRepivot(INode(node), [pivot]) == INode(newnode);

    assert BT.ValidRepivot(BT.Repivot(ref, INode(node), pivots));
    var step := BT.BetreeRepivot(BT.Repivot(ref, INode(node), pivots));
    assert BT.ValidBetreeStep(step);
    assert |BT.BetreeStepOps(step)| == 1; // TODO
    assert BC.Dirty(Ik(k), IVars(s), IVars(s'), ref, INode(newnode));
    assert BC.OpStep(Ik(k), IVars(s), IVars(s'), BT.BetreeStepOps(step)[0]);
    BC.MakeTransaction1(Ik(k), IVars(s), IVars(s'), BT.BetreeStepOps(step));
    //assert BC.ReadStep(k, IVars(s), BT.BetreeStepReads(step)[0]);
    //assert BBC.BetreeMove(Ik(k), IVars(s), IVars(s'), UI.NoOp, SD.NoDiskOp, step);
    assert stepsBetree(k, IVars(s), IVars(s'), UI.NoOp, step);
  }
}
