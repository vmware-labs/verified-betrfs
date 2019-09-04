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

  import KMTable = KMTable`Internal

  method GetNewPivots(bucket: KMTable.KMT)
  returns (pivots : seq<MS.Key>)
  requires KMTable.WF(bucket)
  ensures Pivots.WFPivots(pivots)
  ensures pivots == ImplModelLeaf.GetNewPivots(bucket)
  {
    // try to split the keys evenly, but don't let any bucket
    // be larger than the cap

    var kvl := bucket.kvl;
    var n := |kvl.keys|;

    var m := (n + 8 as int) / 8 as int;
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
    invariant |r| > 0 ==> 0 <= i-m < n && r[|r|-1] == kvl.keys[i - m];
    invariant |r| > 0 ==> MS.Keyspace.NotMinimum(r[0]);
    invariant i > 0
    {
      MS.Keyspace.IsNotMinimum(kvl.keys[0], kvl.keys[i]);

      r := r + [kvl.keys[i]];
      i := i + m;
    }

    pivots := r;

    if |pivots| < 1 {
      //print n; print "\n";
      //print |pivots|; print "\n";
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
  ensures IS.WVars(s')
  ensures s'.Ready?
  ensures IVars(s') == ImplModelLeaf.repivotLeaf(Ic(k), old(IVars(s)), ref, node);
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  ensures forall r | r in s'.lru.Repr :: fresh(r) || r in old(s.lru.Repr)
  modifies s.ephemeralIndirectionTable.Repr
  modifies s.lru.Repr
  {
    ImplModelLeaf.reveal_repivotLeaf();

    if s.frozenIndirectionTable.Some? {
      var lbaGraph := s.frozenIndirectionTable.value.Get(ref);
      if lbaGraph.Some? {
        var (lba, _) := lbaGraph.value;
        if lba.None? {
          s' := s;
          print "giving up; flush can't run because frozen isn't written";
          return;
        }
      }
    }

    var joined := KMTable.Join(node.buckets, node.pivotTable);
    var pivots := GetNewPivots(joined);

    var buckets' := KMTable.SplitOnPivots(joined, pivots);
    var newnode := IM.Node(pivots, None, buckets');

    KMTable.WFImpliesWFBucket(joined);
    WFSplitBucketOnPivots(KMTable.I(joined), pivots);

    s' := write(k, s, ref, newnode);
  assert IVars(s') == ImplModelLeaf.repivotLeaf(Ic(k), old(IVars(s)), ref, node);
  }
}
