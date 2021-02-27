// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "BookkeepingModel.i.dfy"

module LeafModel { 
  import opened StateBCModel
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
  import PivotBetreeSpecWFNodes

  import IT = IndirectionTable
  import opened NativeTypes

  function {:opaque} repivotLeaf(s: BCVariables, ref: BT.G.Reference, node: Node)
  : (s': BCVariables)
  requires BCInv(s)
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable.graph
  requires ref in s.cache
  requires node == s.cache[ref]
  requires node.children.None?
  requires |node.buckets| == 1
  requires |s.ephemeralIndirectionTable.graph| <= IT.MaxSize() - 1
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

  lemma repivotLeafCorrect(s: BCVariables, ref: BT.G.Reference, node: Node)
  requires BCInv(s)
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable.graph
  requires ref in s.cache
  requires node == s.cache[ref]
  requires node.children.None?
  requires |node.buckets| == 1
  requires |s.ephemeralIndirectionTable.graph| <= IT.MaxSize() - 1
  ensures var s' := repivotLeaf(s, ref, node);
    && WFBCVars(s')
    && betree_next(IBlockCache(s), IBlockCache(s'))
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
      assert WFBCVars(s');
      assert noop(IBlockCache(s), IBlockCache(s));
      return;
    }

    if !BoundedBucketList(node.buckets, node.pivotTable) {
      assert noop(IBlockCache(s), IBlockCache(s));
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

    /*WeightBucketLeBucketList(node.buckets, 0);
    WeightSplitBucketAdditiveLe(node.buckets[0], pivot);
    WeightBucketList2(
        SplitBucketLeft(node.buckets[0], pivot),
        SplitBucketRight(node.buckets[0], pivot));*/
    PivotBetreeSpecWFNodes.WFApplyRepivot(
        BT.Repivot(ref, INode(node), pivots, pivot));

    assert WFNode(newnode);
    writeCorrect(s, ref, newnode);
    assert WFBCVars(s');

    //assert IBlockCache(s1).cache == IBlockCache(s).cache[ref := INode(newnode)];

    BT.PivotsHasAllKeys(pivots);

    assert BT.ApplyRepivot(BT.Repivot(ref, INode(node), pivots, pivot)) == INode(newnode);

    assert BT.ValidRepivot(BT.Repivot(ref, INode(node), pivots, pivot));
    var step := BT.BetreeRepivot(BT.Repivot(ref, INode(node), pivots, pivot));
    assert BT.ValidBetreeStep(step);
    assert |BT.BetreeStepOps(step)| == 1; // TODO
    assert BC.Dirty(IBlockCache(s), IBlockCache(s'), ref, INode(newnode));
    assert BC.OpStep(IBlockCache(s), IBlockCache(s'), BT.BetreeStepOps(step)[0]);
    BC.MakeTransaction1(IBlockCache(s), IBlockCache(s'), BT.BetreeStepOps(step));
    //assert BC.ReadStep(IBlockCache(s), BT.BetreeStepReads(step)[0]);
    //assert BBC.BetreeMove(IBlockCache(s), IBlockCache(s'), UI.NoOp, SD.NoDiskOp, step);
    assert stepsBetree(IBlockCache(s), IBlockCache(s'), AdvanceOp(UI.NoOp, true), step);
  }
}
