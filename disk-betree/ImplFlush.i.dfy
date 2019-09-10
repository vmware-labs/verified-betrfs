include "ImplCache.i.dfy"
include "ImplModelFlush.i.dfy"

module ImplFlush { 
  import opened Impl
  import opened ImplCache
  import opened ImplState

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib
  import opened BucketWeights

  import opened NativeTypes
  import ImplModel
  import ImplModelCache
  import ImplModelFlush

  import Native

  method flush(k: ImplConstants, s: ImplVariables, parentref: BT.G.Reference, slot: int, childref: BT.G.Reference, child: Node)
  requires Inv(k, s)
  requires s.ready

  requires parentref in IIndirectionTable(s.ephemeralIndirectionTable)
  requires parentref in s.cache.Contents

  requires s.cache.Contents[parentref].children.Some?
  requires 0 <= slot < |s.cache.Contents[parentref].children.value|
  requires s.cache.Contents[parentref].children.value[slot] == childref

  requires childref in IIndirectionTable(s.ephemeralIndirectionTable)
  requires childref in s.cache.Contents
  requires s.cache.Contents[childref] == child
  requires ICache(s.cache)[childref] == INode(child)

  modifies s.Repr()

  ensures WellUpdated(s)
  ensures s.ready
  ensures ImplModelFlush.flush(Ic(k), old(s.I()), parentref, slot, childref, old(INode(child))) == s.I()
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

    var nodeOpt := s.cache.Get(parentref);
    var node := nodeOpt.value;
    assert INode(node) == ICache(s.cache)[parentref];
    var childref := node.children.value[slot];

    assert BucketListReprInv(node.buckets);

    WeightBucketLeBucketList(MutableBucket.MutBucket.ISeq(node.buckets), slot);

    var newparentBucket, newbuckets := MutableBucket.MutBucket.PartialFlush(node.buckets[slot], child.buckets, child.pivotTable);
    var newchild := child.(buckets := newbuckets);
    var newchildref := alloc(k, s, newchild);
    if newchildref.None? {
      print "giving up; could not get parentref\n";
      return;
    }

    assert BucketListReprInv(node.buckets);

    var newparent := IS.Node(
        node.pivotTable,
        Some(node.children.value[slot := newchildref.value]),
        node.buckets[slot := newparentBucket]
      );

    forall i, j | 0 <= i < |newparent.buckets| && 0 <= j < |newparent.buckets| && i != j ensures
        newparent.buckets[i].Repr !! newparent.buckets[j].Repr
    {
      if i == slot {
        assert newparent.buckets[i].Repr !! newparent.buckets[j].Repr;
      }
      else if j == slot {
        assert newparent.buckets[i].Repr !! newparent.buckets[j].Repr;
      } else {
        assert newparent.buckets[i].Repr !! newparent.buckets[j].Repr;
      }
    }

    assert BucketListReprInv(newparent.buckets);

    assume false;

    write(k, s, parentref, newparent);

    //Native.BenchmarkingUtil.end();
  }
}
