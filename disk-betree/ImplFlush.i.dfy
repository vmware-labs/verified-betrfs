include "ImplCache.i.dfy"
include "ImplModelFlush.i.dfy"

module ImplFlush { 
  import opened Impl
  import opened ImplCache
  import opened ImplState
  import opened ImplNode

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import opened MutableBucket

  import opened NativeTypes
  import ImplModel
  import ImplModelCache
  import ImplModelFlush

  import Native

  method flush(k: ImplConstants, s: ImplVariables, parentref: BT.G.Reference, slot: int, childref: BT.G.Reference, child: Node)
  requires Inv(k, s)
  requires s.ready

  requires Some(child) == s.cache.ptr(childref)

  requires parentref in IIndirectionTable(s.ephemeralIndirectionTable)
  requires parentref in s.cache.I()

  requires s.cache.I()[parentref].children.Some?
  requires 0 <= slot < |s.cache.I()[parentref].children.value|
  requires s.cache.I()[parentref].children.value[slot] == childref

  requires childref in IIndirectionTable(s.ephemeralIndirectionTable)

  modifies s.Repr()

  ensures WellUpdated(s)
  ensures s.ready
  ensures ImplModelFlush.flush(Ic(k), old(s.I()), parentref, slot, childref, old(child.I())) == s.I()
  {
    if s.frozenIndirectionTable != null {
      var lbaGraph := s.frozenIndirectionTable.Get(parentref);
      if lbaGraph.Some? {
        var (lba, _) := lbaGraph.value;
        if lba.None? {
          print "giving up; flush can't run because frozen isn't written";
          return;
        }
      }
    }

    //Native.BenchmarkingUtil.start();

    var nodeOpt := s.cache.GetOpt(parentref);
    var parent := nodeOpt.value;
    ghost var parentI := parent.I();
    var childref := parent.children.value[slot];

    assert s.I().cache[parentref] == parent.I();
    assert parent.I().children == s.I().cache[parentref].children;
    s.cache.LemmaNodeReprLeRepr(parentref);

    WeightBucketLeBucketList(MutableBucket.MutBucket.ISeq(parent.buckets), slot);

    assert WeightBucketList(s.I().cache[childref].buckets) <= MaxTotalBucketWeight();
    assert s.I().cache[childref].buckets == MutBucket.ISeq(child.buckets);
    assert WeightBucketList(MutBucket.ISeq(child.buckets)) <= MaxTotalBucketWeight();

    var newparentBucket, newbuckets := MutableBucket.MutBucket.PartialFlush(parent.buckets[slot], child.buckets, child.pivotTable);
    var newchild := new Node(child.pivotTable, child.children, newbuckets);
    var newchildref := allocBookkeeping(k, s, newchild.children);
    if newchildref.None? {
      print "giving up; could not get parentref\n";
      return;
    }

    assert parent.I().children == s.I().cache[parentref].children;

    var newparent_children := parent.children.value[slot := newchildref.value];

    writeBookkeeping(k, s, parentref, Some(newparent_children));

    assume parentref != newchildref.value;

    ghost var c1 := s.cache.I();

    s.cache.Insert(newchildref.value, newchild);

    ghost var c2 := s.cache.I();
    assert c2 == c1[newchildref.value := newchild.I()];
    ghost var newParentBucketI := newparentBucket.Bucket;

    s.cache.UpdateNodeSlot(parentref, slot as uint64, newparentBucket, newchildref.value);

    ghost var c3 := s.cache.I();

    //Native.BenchmarkingUtil.end();

    assert c3 == c2[parentref := IM.Node(
          parentI.pivotTable,
          Some(parentI.children.value[slot := newchildref.value]),
          parentI.buckets[slot := newParentBucketI]
        )];

    ghost var a := ImplModelFlush.flush(Ic(k), old(s.I()), parentref, slot, childref, old(child.I()));
    ghost var b := s.I();
    assert a.cache == b.cache;
  }
}
