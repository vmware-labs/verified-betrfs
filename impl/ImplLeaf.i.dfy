include "../treemodel/ImplCache.i.dfy"
include "../treemodel/ImplModelLeaf.i.dfy"

module ImplLeaf { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache
  import opened ImplModelLeaf
  import opened ImplState
  import opened ImplNode
  import opened MutableBucket
  import IMM = ImplMarshallingModel

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes

  method repivotLeaf(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, node: Node)
  requires Inv(k, s)
  requires s.ready
  requires ref in s.ephemeralIndirectionTable.I().graph
  requires s.cache.ptr(ref) == Some(node)
  requires node.Inv()
  requires node.children.None?
  requires |node.buckets| == 1
  requires |s.ephemeralIndirectionTable.I().graph| <= IndirectionTableModel.MaxSize() - 1
  modifies s.Repr()
  ensures s.ready
  ensures WellUpdated(s)
  ensures s.I() == ImplModelLeaf.repivotLeaf(Ic(k), old(s.I()), ref, old(node.I()));
  {
    ImplModelLeaf.reveal_repivotLeaf();

    if s.frozenIndirectionTable != null {
      var b := s.frozenIndirectionTable.HasEmptyLoc(ref);
      if b {
        print "giving up; repivotLeaf can't run because frozen isn't written";
        return;
      }
    }

    var kvl := node.buckets[0 as uint64].GetKvl();
    var pivot := KVList.GetMiddleKey(kvl);

    var pivots := [pivot];

    var left, right := node.buckets[0 as uint64].SplitLeftRight(pivot);

    var buckets' := [left, right];
    MutBucket.ReprSeqDisjointOfLen2(buckets');
    MutBucket.ListReprOfLen2(buckets');
    var newnode := new Node(pivots, None, buckets');

    writeBookkeeping(k, s, ref, None);

    newnode.LemmaRepr();
    assert fresh(newnode.Repr);
    assert s.cache.Repr !! newnode.Repr;
    s.cache.Insert(ref, newnode);

    assert s.W();

    ghost var a := s.I();
    ghost var b := ImplModelLeaf.repivotLeaf(Ic(k), old(s.I()), ref, old(node.I()));
    assert newnode.I() == old(IM.Node(pivots, None, [
          SplitBucketLeft(node.I().buckets[0], pivot),
          SplitBucketRight(node.I().buckets[0], pivot)
        ]));
      
    assert a.cache == b.cache;
  }
}
