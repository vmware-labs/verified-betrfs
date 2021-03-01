include "BookkeepingImpl.i.dfy"
include "FlushModel.i.dfy"

module FlushImpl { 
  import opened BookkeepingImpl
  import opened StateBCImpl
  import opened StateSectorImpl

  import opened NodeImpl
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
  import BookkeepingModel
  import FlushModel
  import IOModel

  import IT = IndirectionTable

  method flushInteral(linear inout s: ImplVariables, parentref: BT.G.Reference, slot: uint64, childref: BT.G.Reference)
  requires old_s.Inv()
  requires old_s.Ready?
  requires old_s.cache.ptr(childref).Some?

  requires parentref in old_s.ephemeralIndirectionTable.I().graph
  requires parentref in old_s.cache.I()

  requires old_s.cache.I()[parentref].children.Some?
  requires 0 <= slot as int < |old_s.cache.I()[parentref].children.value|
  requires old_s.cache.I()[parentref].children.value[slot] == childref

  requires childref in old_s.ephemeralIndirectionTable.I().graph

  requires |old_s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 2

  ensures s.W()
  ensures s.Ready?
  ensures s.WriteAllocConditions()
  ensures s.I() == FlushModel.flush(old_s.I(), parentref, slot as int, childref, 
    old_s.cache.I()[childref]);
  ensures LruModel.I(s.lru.Queue()) == s.cache.I().Keys;
  {
    var b := false;
    if s.frozenIndirectionTable.lSome? {
      b := s.frozenIndirectionTable.value.HasEmptyLoc(parentref);
    }
  
    if b {
      print "giving up; flush can't run because frozen isn't written";
    } else {
      var bounded := s.cache.NodeBoundedBucket(parentref, childref, slot);
      if bounded {
        //Native.BenchmarkingUtil.start();

        ghost var parentI := s.cache.I()[parentref];
        ghost var childI := s.cache.I()[childref];

        linear var newparentBucket, newchild := 
          s.cache.NodePartialFlush(parentref, childref, slot);

        BookkeepingModel.lemmaChildrenConditionsOfNode(s.I(), childref);
        BookkeepingModel.lemmaChildrenConditionsOfNode(s.I(), parentref);
        BookkeepingModel.lemmaChildrenConditionsUpdateOfAllocBookkeeping(
            s.I(), newchild.children, parentI.children.value, slot as int);
        BookkeepingModel.allocRefDoesntEqual(s.I(), newchild.children, parentref);

        var newchildref := allocBookkeeping(inout s, newchild.children);
        if newchildref.None? {
          var _ := FreeMutBucket(newparentBucket);
          var _ := FreeNode(newchild);
          print "giving up; could not get parentref\n";
        } else {
          inout s.cache.Insert(newchildref.value, newchild);

          var newparent_children := inout s.cache.NodeUpdateSlot(parentref,
            slot, newparentBucket, newchildref.value);
          writeBookkeeping(inout s, parentref, newparent_children);

          assert LruModel.I(s.lru.Queue()) == s.cache.I().Keys;
        }
      } else {
        print "giving up; flush can't run because flushed keys are out of bound for its children";
      }
    }
  }
  
  method flush(linear inout s: ImplVariables, parentref: BT.G.Reference, slot: uint64, childref: BT.G.Reference)
  requires old_s.Inv()
  requires old_s.Ready?
  requires old_s.cache.ptr(childref).Some?

  requires parentref in old_s.ephemeralIndirectionTable.I().graph
  requires parentref in old_s.cache.I()

  requires old_s.cache.I()[parentref].children.Some?
  requires 0 <= slot as int < |old_s.cache.I()[parentref].children.value|
  requires old_s.cache.I()[parentref].children.value[slot] == childref

  requires childref in old_s.ephemeralIndirectionTable.I().graph

  requires |old_s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 2

  requires old_s.totalCacheSize() <= MaxCacheSize() - 1

  ensures s.WFBCVars()
  ensures IOModel.betree_next(old_s.I(), s.I())
  {
    FlushModel.flushCorrect(s.I(), parentref, slot as int, childref, s.cache.I()[childref]);
    flushInteral(inout s, parentref, slot, childref);
    assert s.WFBCVars();
  }

}