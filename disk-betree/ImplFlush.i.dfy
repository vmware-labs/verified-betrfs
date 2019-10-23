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

  method flush(k: ImplConstants, s: ImplVariables, parentref: BT.G.Reference, slot: uint64, childref: BT.G.Reference, child: Node)
  requires Inv(k, s)
  requires s.ready

  requires Some(child) == s.cache.ptr(childref)

  requires parentref in IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires parentref in s.cache.I()

  requires s.cache.I()[parentref].children.Some?
  requires 0 <= slot as int < |s.cache.I()[parentref].children.value|
  requires s.cache.I()[parentref].children.value[slot] == childref

  requires childref in IIndirectionTable(s.ephemeralIndirectionTable).graph

  modifies s.Repr()

  ensures WellUpdated(s)
  ensures s.ready
  ensures ImplModelFlush.flush(Ic(k), old(s.I()), parentref, slot as int, childref, old(child.I())) == s.I()
  {
    if s.frozenIndirectionTable != null {
      var b := s.frozenIndirectionTable.HasEmptyLoc(parentref);
      if b {
        print "giving up; flush can't run because frozen isn't written";
        return;
      }
    }

    //Native.BenchmarkingUtil.start();

    MutBucket.reveal_ReprSeq();

    var nodeOpt := s.cache.GetOpt(parentref);
    var parent := nodeOpt.value;
    ghost var parentI := parent.I();
    var childref := parent.children.value[slot];

    assert s.I().cache[parentref] == parent.I();
    assert parent.I().children == s.I().cache[parentref].children;
    s.cache.LemmaNodeReprLeRepr(parentref);

    WeightBucketLeBucketList(MutableBucket.MutBucket.ISeq(parent.buckets), slot as int);

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

    var newparent_children := parent.children.value[slot as int := newchildref.value];

    writeBookkeeping(k, s, parentref, Some(newparent_children));

    assume parentref != newchildref.value;

    ghost var c1 := s.cache.I();
    assert c1 == old(s.cache.I());

    s.cache.Insert(newchildref.value, newchild);

    ghost var c2 := s.cache.I();
    assert c2 == c1[newchildref.value := newchild.I()];
    //assert newchild.I() == old(child.I()).(buckets := MutBucket.ISeq(newbuckets));
    ghost var newParentBucketI := newparentBucket.Bucket;

    s.cache.UpdateNodeSlot(parentref, slot, newparentBucket, newchildref.value);

    ghost var c3 := s.cache.I();

    //Native.BenchmarkingUtil.end();

    assert c3 == c2[parentref := IM.Node(
          parentI.pivotTable,
          Some(parentI.children.value[slot as int := newchildref.value]),
          parentI.buckets[slot as int := newParentBucketI]
        )];
    //assert parentI == old(s.I()).cache[parentref];

    //assert c2 == old(s.I()).cache
    //      [newchildref.value := old(child.I()).(buckets := MutBucket.ISeq(newbuckets))];

    ghost var a := ImplModelFlush.flush(Ic(k), old(s.I()), parentref, slot as int, childref, old(child.I()));
    ghost var b := s.I();
    assert a.cache
        /*== old(s.I()).cache
                  [newchildref.value := old(child.I()).(buckets := MutBucket.ISeq(newbuckets))]
                  [parentref := IM.Node(
                    parentI.pivotTable,
                    Some(parentI.children.value[slot := newchildref.value]),
                    parentI.buckets[slot := newParentBucketI]
                  )]*/
        == c3
        == b.cache;
  }
}
