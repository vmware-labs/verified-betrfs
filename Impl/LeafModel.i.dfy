include "BookkeepingModel.i.dfy"

module LeafModel { 
  import opened StateSectorModel

  import opened IOModel
  import opened BookkeepingModel
  import opened ViewOp
  import opened DiskOpModel

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import opened BoundedPivotsLib

  import IT = IndirectionTable
  import opened NativeTypes

  function {:opaque} repivotLeaf(s: BBC.Variables, ref: BT.G.Reference, node: Node)
  : (s': BBC.Variables)
  requires BBC.Inv(s)
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable.graph
  requires ref in s.cache
  requires node == s.cache[ref]
  requires node.children.None?
  requires |node.buckets| == 1
  {
    if (
      && s.frozenIndirectionTable.Some?
      && s.frozenIndirectionTable.value.hasEmptyLoc(ref)
    ) then (
      s
    ) else (
      // if data was corrupted before we won't allow access to it after repivot
      if !BoundedBucketList(node.buckets, node.pivotTable) then (
        s
      ) else (
        var pivot := getMiddleKey(node.buckets[0]);
        var pivots := insert(InitPivotTable(), KeyToElement(pivot), 1);

        var buckets' := [
            SplitBucketLeft(node.buckets[0], pivot),
            SplitBucketRight(node.buckets[0], pivot)
        ];
        var newnode := BT.G.Node(pivots, None, buckets');
        var s1 := writeBookkeeping(s, ref, None);
        var s' := s1.(cache := s1.cache[ref := newnode]);
        s'
      )
    )
  }

  lemma repivotLeafCorrect(s: BBC.Variables, ref: BT.G.Reference, node: Node)
  requires BBC.Inv(s)
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable.graph
  requires ref in s.cache
  requires node == s.cache[ref]
  requires node.children.None?
  requires |node.buckets| == 1
  ensures var s' := repivotLeaf(s, ref, node);
    && betree_next(s, s')
  {
    reveal_SplitBucketLeft();
    reveal_SplitBucketRight();
    var s' := repivotLeaf(s, ref, node);

    reveal_repivotLeaf();

    if (
      && s.frozenIndirectionTable.Some?
      && s.frozenIndirectionTable.value.hasEmptyLoc(ref)
    ) {
      assert s' == s;
      assert noop(s, s);
      return;
    }

    if !BoundedBucketList(node.buckets, node.pivotTable) {
      assert noop(s, s);
      return;
    }

    var pivot := getMiddleKey(node.buckets[0]);
    var pivots := insert(InitPivotTable(), KeyToElement(pivot), 1);
    assert Last(InitPivotTable()) == Keyspace.Max_Element;

    WFPivotsOfGetMiddleKey(node.buckets[0]);

    var buckets' := [
        SplitBucketLeft(node.buckets[0], pivot),
        SplitBucketRight(node.buckets[0], pivot)
    ];

    //reveal_WFBucket();

    var newnode := BT.G.Node(pivots, None, buckets');
    var s1 := writeWithNode(s, ref, newnode);
    reveal_writeBookkeeping();

    assert s1 == s';

    WeightBucketLeBucketList(node.buckets, 0);
    WeightSplitBucketAdditiveLe(node.buckets[0], pivot);
    WeightBucketList2(
        SplitBucketLeft(node.buckets[0], pivot),
        SplitBucketRight(node.buckets[0], pivot));

    assert WFNode(newnode);
    writeCorrect(s, ref, newnode);

    //assert IBlockCache(s1).cache == s.cache[ref := INode(newnode)];

    assert JoinBucketList(node.buckets).b
        == MapUnion(JoinBucketList([]).b, node.buckets[0].b)
        == MapUnion(map[], node.buckets[0].b)
        == node.buckets[0].b;

    BT.PivotsHasAllKeys(pivots);
    BoundedBucketListJoin(node.buckets, pivots);

    assert SplitBucketOnPivots(JoinBucketList(node.buckets), pivots)
        == SplitBucketOnPivots(node.buckets[0], pivots)
        == buckets';

    assert BT.ApplyRepivot(BT.Repivot(ref, node, pivots)) == newnode;

    assert BT.ValidRepivot(BT.Repivot(ref, node, pivots));
    var step := BT.BetreeRepivot(BT.Repivot(ref, node, pivots));
    assert BT.ValidBetreeStep(step);
    assert |BT.BetreeStepOps(step)| == 1; // TODO
    assert BC.Dirty(s, s', ref, newnode);
    assert BC.OpStep(s, s', BT.BetreeStepOps(step)[0]);
    BC.MakeTransaction1(s, s', BT.BetreeStepOps(step));
    //assert BC.ReadStep(s, BT.BetreeStepReads(step)[0]);
    //assert BBC.BetreeMove(s, s', UI.NoOp, SD.NoDiskOp, step);
    assert stepsBetree(s, s', AdvanceOp(UI.NoOp, true), step);
  }
}
