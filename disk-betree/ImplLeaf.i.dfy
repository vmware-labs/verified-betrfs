include "ImplCache.i.dfy"

module ImplLeaf { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes

  method GetNewPivots(bucket: KMTable.KMTable)
  returns (pivots : seq<MS.Key>)
  requires KMTable.WF(bucket)
  ensures Pivots.WFPivots(pivots)
  {
    // try to split the keys evenly, but don't let any bucket
    // be larger than the cap

    var n := |bucket.keys|;

    var m := (n + Marshalling.CapNumBuckets() as int) / Marshalling.CapNumBuckets() as int;
    if m > 500 {
      m := 500;
    }
    if m < 1 {
      m := 1;
    }

    MS.Keyspace.reveal_IsStrictlySorted();
    var r := [];
    var i := m;
    while i < n
    invariant MS.Keyspace.IsStrictlySorted(r);
    invariant |r| > 0 ==> 0 <= i-m < n && r[|r|-1] == bucket.keys[i - m];
    invariant |r| > 0 ==> MS.Keyspace.NotMinimum(r[0]);
    invariant i > 0
    {
      MS.Keyspace.IsNotMinimum(bucket.keys[0], bucket.keys[i]);

      r := r + [bucket.keys[i]];
      i := i + m;
    }

    pivots := r;
  }

  method repivotLeaf(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference, slot: int, node: IS.Node)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires s.Ready?
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in s.cache
  requires node == s.cache[ref]
  requires node.children.None?
  requires 0 <= slot < |s.cache[ref].buckets|
  requires io.initialized()
  requires s.rootBucket == TTT.EmptyTree // FIXME we don't actually need this unless we're flushing the root
  requires s.frozenIndirectionTable.Some? && ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph ==>
      ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).locs
  modifies io
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies s.ephemeralIndirectionTable.Repr
  {
    if (!(
      && |node.buckets| < 0x8000_0000
      && (forall i | 0 <= i < |node.buckets| :: |node.buckets[i].keys| < 0x1_0000_0000)
    )) {
      s' := s;
      assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
      print "giving up; stuff too big to call Join\n";
      return;
    }

    forall i, j, key1, key2 | 0 <= i < j < |node.buckets| && key1 in KMTable.I(node.buckets[i]) && key2 in KMTable.I(node.buckets[j])
    ensures MS.Keyspace.lt(key1, key2)
    {
      //assert BT.NodeHasWFBucketAt(IS.INode(node), i);
      //assert BT.NodeHasWFBucketAt(IS.INode(node), j);
      assert Pivots.Route(node.pivotTable, key1) == i;
      assert Pivots.Route(node.pivotTable, key2) == j;
      MS.Keyspace.IsStrictlySortedImpliesLte(node.pivotTable, i, j-1);
    }

    var joined := KMTable.Join(node.buckets, node.pivotTable);
    var pivots := GetNewPivots(joined);

    if (!(|pivots| < 0x7fff_ffff_ffff_ffff)) {
      s' := s;
      assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
      print "giving up; stuff too big to call Split\n";
      return;
    }

    var buckets' := KMTable.SplitOnPivots(joined, pivots);
    var newnode := IS.Node(pivots, None, buckets');

    KMTable.WFImpliesWFBucket(joined);

    WFSplitBucketOnPivots(KMTable.I(joined), pivots);
    s' := write(k, s, ref, newnode);

    //assert BT.ValidRepivot(BT.Repivot(ref, node, pivots));
    ghost var step := BT.BetreeRepivot(BT.Repivot(ref, IS.INode(node), pivots));
    assert BT.ValidBetreeStep(step);
    assert |BT.BetreeStepOps(step)| == 1; // TODO
    assert BC.OpStep(k, old(IS.IVars(s)), IS.IVars(s'), BT.BetreeStepOps(step)[0]);
    BC.MakeTransaction1(k, old(IS.IVars(s)), IS.IVars(s'), BT.BetreeStepOps(step));
    assume stepsBetree(k, old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, step);
  }
}
