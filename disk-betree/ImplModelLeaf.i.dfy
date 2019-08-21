include "ImplModelCache.i.dfy"

module ImplModelLeaf { 
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelCache

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib
  import PivotsLib

  import opened NativeTypes

  function GetNewPivots(bucket: KMTable.KMTable) : (pivots : seq<MS.Key>)

  lemma WFGetNewPivots(bucket: KMTable.KMTable)
  requires KMTable.WF(bucket)
  ensures PivotsLib.WFPivots(GetNewPivots(bucket))
  {
    assume false;
  }

  function {:opaque} repivotLeaf(k: Constants, s: Variables, ref: BT.G.Reference, slot: int, node: Node)
  : (s': Variables)
  requires Inv(k, s)
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable
  requires ref in s.cache
  requires node == s.cache[ref]
  requires node.children.None?
  requires 0 <= slot < |s.cache[ref].buckets|
  requires ref != BT.G.Root()
  requires s.frozenIndirectionTable.Some? && ref in IIndirectionTable(s.frozenIndirectionTable.value).graph ==>
      ref in IIndirectionTable(s.frozenIndirectionTable.value).locs
  {
    if (!(
      && |node.buckets| < 0x8000_0000
      && (forall i | 0 <= i < |node.buckets| :: |node.buckets[i].keys| < 0x1_0000_0000)
    )) then (
      s
    ) else (
      var joined := KMTable.join(node.buckets);
      KMTable.joinEqJoinBucketList(node.buckets, node.pivotTable);

      var pivots := GetNewPivots(joined);
      if (!(|pivots| < 0x7fff_ffff_ffff_ffff)) then (
        s
      ) else (
        assume KMTable.Bounded(joined);
        var buckets' := KMTable.splitOnPivots(joined, pivots);
        var newnode := Node(pivots, None, buckets');
        var s' := write(k, s, ref, newnode);
        s'
      )
    )
  }

  lemma repivotLeafCorrect(k: Constants, s: Variables, ref: BT.G.Reference, slot: int, node: Node)
  requires Inv(k, s)
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable
  requires ref in s.cache
  requires node == s.cache[ref]
  requires node.children.None?
  requires 0 <= slot < |s.cache[ref].buckets|
  requires ref != BT.G.Root()
  requires s.frozenIndirectionTable.Some? && ref in IIndirectionTable(s.frozenIndirectionTable.value).graph ==>
      ref in IIndirectionTable(s.frozenIndirectionTable.value).locs
  ensures var s' := repivotLeaf(k, s, ref, slot, node);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, D.NoDiskOp)
  {
    reveal_repivotLeaf();

    if (!(
      && |node.buckets| < 0x8000_0000
      && (forall i | 0 <= i < |node.buckets| :: |node.buckets[i].keys| < 0x1_0000_0000)
    )) {
      assert noop(k, IVars(s), IVars(s));
      return;
    }

    //assert MapsTo(IVars(s).cache, ref, INode(node));

    forall i, j, key1, key2 | 0 <= i < j < |node.buckets| && key1 in KMTable.I(node.buckets[i]) && key2 in KMTable.I(node.buckets[j])
    ensures MS.Keyspace.lt(key1, key2)
    {
      //assert BT.NodeHasWFBucketAt(INode(node), i);
      //assert BT.NodeHasWFBucketAt(INode(node), j);
      assert Pivots.Route(node.pivotTable, key1) == i;
      assert Pivots.Route(node.pivotTable, key2) == j;
      MS.Keyspace.IsStrictlySortedImpliesLte(node.pivotTable, i, j-1);
    }

    var joined := KMTable.join(node.buckets);
    KMTable.joinEqJoinBucketList(node.buckets, node.pivotTable);
    assume KMTable.Bounded(joined);

    var pivots := GetNewPivots(joined);
    WFGetNewPivots(joined);

    if (!(|pivots| < 0x7fff_ffff_ffff_ffff)) {
      assert noop(k, IVars(s), IVars(s));
      return;
    }

    var buckets' := KMTable.splitOnPivots(joined, pivots);
    var newnode := Node(pivots, None, buckets');

    KMTable.WFImpliesWFBucket(joined);

    WFSplitBucketOnPivots(KMTable.I(joined), pivots);
    var s' := write(k, s, ref, newnode);
    writeCorrect(k, s, ref, newnode);
    reveal_write();

    //assert BT.ValidRepivot(BT.Repivot(ref, node, pivots));
    ghost var step := BT.BetreeRepivot(BT.Repivot(ref, INode(node), pivots));
    assert BT.ValidBetreeStep(step);
    assert |BT.BetreeStepOps(step)| == 1; // TODO
    assert BC.OpStep(Ik(k), IVars(s), IVars(s'), BT.BetreeStepOps(step)[0]);
    BC.MakeTransaction1(Ik(k), IVars(s), IVars(s'), BT.BetreeStepOps(step));
    //assert BC.ReadStep(k, IVars(s), BT.BetreeStepReads(step)[0]);
    //assert BBC.BetreeMove(Ik(k), IVars(s), IVars(s'), UI.NoOp, SD.NoDiskOp, step);
    assert stepsBetree(k, IVars(s), IVars(s'), UI.NoOp, step);
  }
}
