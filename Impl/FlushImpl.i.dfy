include "BookkeepingImpl.i.dfy"
include "FlushModel.i.dfy"

module FlushImpl { 
  import opened BookkeepingImpl
  import opened StateImpl
  import opened BoxNodeImpl
  import opened DiskOpImpl

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import opened BucketImpl
  import opened LinearSequence_s
  import opened LinearSequence_i
  import opened BoundedPivotsLib

  import opened NativeTypes
  import StateModel
  import BookkeepingModel
  import FlushModel

  import IT = IndirectionTable

  method flush(s: ImplVariables, parentref: BT.G.Reference, slot: uint64, childref: BT.G.Reference, child: Node)
  requires Inv(s)
  requires s.ready

  requires Some(child) == s.cache.ptr(childref)

  requires parentref in s.ephemeralIndirectionTable.I().graph
  requires parentref in s.cache.I()

  requires s.cache.I()[parentref].children.Some?
  requires 0 <= slot as int < |s.cache.I()[parentref].children.value|
  requires s.cache.I()[parentref].children.value[slot] == childref

  requires childref in s.ephemeralIndirectionTable.I().graph

  requires |s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 2

  modifies s.Repr()

  ensures WellUpdated(s)
  ensures s.ready
  ensures FlushModel.flush(old(s.I()), parentref, slot as int, childref, old(child.I())) == s.I()
  {
    if s.frozenIndirectionTable != null {
      var b := s.frozenIndirectionTable.HasEmptyLoc(parentref);
      if b {
        print "giving up; flush can't run because frozen isn't written";
        return;
      }
    }

    var nodeOpt := s.cache.GetOpt(parentref);
    var parent := nodeOpt.value;

    var children := parent.GetChildren();
    var childref := children.value[slot];
    var childpivots := child.GetPivots();

    var bounded := parent.BoundedBucket(childpivots, slot);
    if bounded {
      //Native.BenchmarkingUtil.start();
      ghost var parentI := parent.I();
      assert Some(parent) == s.cache.ptr(parentref);

      BookkeepingModel.lemmaChildrenConditionsOfNode(s.I(), childref);
      BookkeepingModel.lemmaChildrenConditionsOfNode(s.I(), parentref);

      assert s.I().cache[parentref] == parent.I();
      assert parent.I().children == s.I().cache[parentref].children;

      WeightBucketLeBucketList(BucketImpl.MutBucket.ILseq(parent.box.Borrow().buckets), slot as int);

      assert WeightBucketList(s.I().cache[childref].buckets) <= MaxTotalBucketWeight();
      assert s.I().cache[childref].buckets == MutBucket.ILseq(child.Read().buckets);
      assert WeightBucketList(MutBucket.ILseq(child.Read().buckets)) <= MaxTotalBucketWeight();

      linear var newparentBucket, newbuckets := BucketImpl.PartialFlush(
          lseq_peek(parent.box.Borrow().buckets, slot as uint64), child.box.Borrow().buckets, child.box.Borrow().pivotTable);

      var childchildren := child.GetChildren();
      var newchild := new Node(childpivots, childchildren, newbuckets);
      
      assert Some(parent) == s.cache.ptr(parentref);
      BookkeepingModel.lemmaChildrenConditionsUpdateOfAllocBookkeeping(
          s.I(), newchild.Read().children, parent.Read().children.value, slot as int);
      BookkeepingModel.allocRefDoesntEqual(s.I(), newchild.Read().children, parentref);

      var newchildref := allocBookkeeping(s, childchildren);
      if newchildref.None? {
        var _ := FreeMutBucket(newparentBucket);
        print "giving up; could not get parentref\n";
      } else {
        assert Some(parent) == s.cache.ptr(parentref);
        assert parent.I().children == s.I().cache[parentref].children;

        var newparent_children := SeqIndexUpdate(
          children.value, slot, newchildref.value);

        writeBookkeeping(s, parentref, Some(newparent_children));
        assert Some(parent) == s.cache.ptr(parentref);
        assert parentref != newchildref.value;

        ghost var c1 := s.cache.I();
        assert c1 == old(s.cache.I());
        s.cache.Insert(newchildref.value, newchild);
        assert Some(parent) == s.cache.ptr(parentref);

        ghost var c2 := s.cache.I();
        assert c2 == c1[newchildref.value := newchild.I()];

        ghost var newParentBucketI := newparentBucket.bucket;
        s.cache.UpdateNodeSlot(parentref, parent, slot, newparentBucket, newchildref.value);

        ghost var c3 := s.cache.I();
        //Native.BenchmarkingUtil.end();

        assert c3 == c2[parentref := BT.G.Node(
              parentI.pivotTable,
              Some(parentI.children.value[slot as int := newchildref.value]),
              parentI.buckets[slot as int := newParentBucketI]
            )];

        ghost var a := FlushModel.flush(old(s.I()), parentref, slot as int, childref, old(child.I()));
        ghost var b := s.I();

        assert a.cache.Keys == c3.Keys;
        forall key | key in a.cache
          ensures a.cache[key] == c3[key]
        {
          if key == parentref {
            assert a.cache[key] == c3[key];
          } else if key == newchildref.value {
            assert a.cache[key] == c3[key];
          } else if key == childref {
            assert a.cache[key] == c3[key];
          } else {
            assert a.cache[key] == c3[key];
          }
        }
      
        assert a.cache
            == c3
            == b.cache;
      }
    } else {
        print "giving up; flush can't run because flushed keys are out of bound for its children";
        return;
    }
  }
}
