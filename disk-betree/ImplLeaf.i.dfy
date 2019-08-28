include "ImplCache.i.dfy"
include "ImplModelLeaf.i.dfy"

module ImplLeaf { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache
  import opened ImplModelLeaf
  import opened ImplState
  import IMM = ImplMarshallingModel

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes

  method GetNewPivots(bucket: KMTable.KMTable)
  returns (pivots : seq<MS.Key>)
  requires KMTable.WF(bucket)
  ensures Pivots.WFPivots(pivots)
  ensures pivots == ImplModelLeaf.GetNewPivots(bucket)
  {
    // try to split the keys evenly, but don't let any bucket
    // be larger than the cap

    var n := |bucket.keys|;

    var m := 500;

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

    if |pivots| < 1 {
      print "warning: GetNewPivots didn't make any pivots\n";
    }

    assume pivots == ImplModelLeaf.GetNewPivots(bucket);
  }

  method repivotLeaf(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, node: IS.Node)
  returns (s': ImplVariables)
  requires Inv(k, s)
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable.Contents
  requires ref in s.cache
  requires node == s.cache[ref]
  requires node.children.None?
  requires ref != BT.G.Root()
  requires s.frozenIndirectionTable.Some? && ref in IS.IIndirectionTable(s.frozenIndirectionTable.value) ==>
      IS.IIndirectionTable(s.frozenIndirectionTable.value)[ref].0.Some?
  ensures IS.WVars(s')
  ensures IVars(s') == ImplModelLeaf.repivotLeaf(Ic(k), old(IVars(s)), ref, node);
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies s.ephemeralIndirectionTable.Repr
  {
    ImplModelLeaf.reveal_repivotLeaf();

    assume forall i | 0 <= i < |node.buckets| :: |node.buckets[i].keys| < 0x1_0000_0000; // should follow from node bounds
    var joined := KMTable.Join(node.buckets, node.pivotTable);

    var pivots := GetNewPivots(joined);

    assume |joined.keys| < 0x8000_0000_0000_0000; // should follow from node bounds

    var buckets' := KMTable.SplitOnPivots(joined, pivots);
    var newnode := IM.Node(pivots, None, buckets');

    KMTable.WFImpliesWFBucket(joined);
    WFSplitBucketOnPivots(KMTable.I(joined), pivots);

    s' := write(k, s, ref, newnode);
  assert IVars(s') == ImplModelLeaf.repivotLeaf(Ic(k), old(IVars(s)), ref, node);
  }
}
