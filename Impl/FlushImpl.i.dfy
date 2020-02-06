include "BookkeepingImpl.i.dfy"
include "FlushModel.i.dfy"

module FlushImpl { 
  import opened BookkeepingImpl
  import opened StateImpl
  import opened NodeImpl

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import opened BucketImpl

  import opened NativeTypes
  import StateModel
  import BookkeepingModel
  import FlushModel
  import KVListPartialFlush

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

  requires |s.ephemeralIndirectionTable.I().graph| <= IndirectionTableModel.MaxSize() - 2

  modifies s.Repr()

  ensures WellUpdated(s)
  ensures s.ready
  ensures FlushModel.flush(Ic(k), old(s.I()), parentref, slot as int, childref, old(child.I())) == s.I()
  {
    NativeBenchmarking.start("flush.0");

    if s.frozenIndirectionTable != null {
      var b := s.frozenIndirectionTable.HasEmptyLoc(parentref);
      if b {
        print "giving up; flush can't run because frozen isn't written";
        return;
      }
    }

    NativeBenchmarking.end("flush.0");
    NativeBenchmarking.start("flush.2");

    //Native.BenchmarkingUtil.start();

    MutBucket.reveal_ReprSeq();

    var nodeOpt := s.cache.GetOpt(parentref);
    var parent := nodeOpt.value;
    ghost var parentI := parent.I();
    var childref := parent.children.value[slot];

    BookkeepingModel.lemmaChildrenConditionsOfNode(Ic(k), s.I(), childref);
    BookkeepingModel.lemmaChildrenConditionsOfNode(Ic(k), s.I(), parentref);

    assert s.I().cache[parentref] == parent.I();
    assert parent.I().children == s.I().cache[parentref].children;
    s.cache.LemmaNodeReprLeRepr(parentref);

    WeightBucketLeBucketList(BucketImpl.MutBucket.ISeq(parent.buckets), slot as int);

    assert WeightBucketList(s.I().cache[childref].buckets) <= MaxTotalBucketWeight();
    assert s.I().cache[childref].buckets == MutBucket.ISeq(child.buckets);
    assert WeightBucketList(MutBucket.ISeq(child.buckets)) <= MaxTotalBucketWeight();

    NativeBenchmarking.end("flush.2");
    NativeBenchmarking.start("flush.3");

    var newparentBucket, newbuckets := KVListPartialFlush.PartialFlush(parent.buckets[slot], child.buckets, child.pivotTable);

    NativeBenchmarking.end("flush.3");

    NativeBenchmarking.start("flush.4");
    var newchild := new Node(child.pivotTable, child.children, newbuckets);
    NativeBenchmarking.end("flush.4");

    BookkeepingModel.lemmaChildrenConditionsUpdateOfAllocBookkeeping(
        Ic(k), s.I(), newchild.children, parent.children.value, slot as int);

    BookkeepingModel.allocRefDoesntEqual(Ic(k), s.I(), newchild.children, parentref);
    NativeBenchmarking.start("flush.5");
    var newchildref := allocBookkeeping(k, s, newchild.children);
    NativeBenchmarking.end("flush.5");
    if newchildref.None? {
      print "giving up; could not get parentref\n";
      return;
    }

    assert parent.I().children == s.I().cache[parentref].children;

    NativeBenchmarking.start("flush.6");
    var newparent_children := SeqIndexUpdate(
      parent.children.value, slot, newchildref.value);
    NativeBenchmarking.end("flush.6");

    NativeBenchmarking.start("flush.7");
    writeBookkeeping(k, s, parentref, Some(newparent_children));
    NativeBenchmarking.end("flush.7");

    assert parentref != newchildref.value;

    ghost var c1 := s.cache.I();
    assert c1 == old(s.cache.I());

    NativeBenchmarking.start("flush.8");
    s.cache.Insert(newchildref.value, newchild);
    NativeBenchmarking.end("flush.8");

    ghost var c2 := s.cache.I();
    assert c2 == c1[newchildref.value := newchild.I()];
    //assert newchild.I() == old(child.I()).(buckets := MutBucket.ISeq(newbuckets));
    ghost var newParentBucketI := newparentBucket.Bucket;

    NativeBenchmarking.start("flush.9");
    s.cache.UpdateNodeSlot(parentref, slot, newparentBucket, newchildref.value);
    NativeBenchmarking.end("flush.9");

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

    ghost var a := FlushModel.flush(Ic(k), old(s.I()), parentref, slot as int, childref, old(child.I()));
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
