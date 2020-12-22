include "BookkeepingImpl.i.dfy"
include "FlushModel.i.dfy"

module FlushImpl { 
  import opened BookkeepingImpl
  import opened StateImpl
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
  import StateModel
  import BookkeepingModel
  import FlushModel

  method flush(s: ImplVariables, parentref: BT.G.Reference, slot: uint64, childref: BT.G.Reference)
  requires Inv(s)
  requires s.ready
  requires s.cache.ptr(childref).Some?

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
  ensures FlushModel.flush(old(s.I()), parentref, slot as int, childref, 
    old(s.cache.I()[childref])) == s.I()
  {
    if s.frozenIndirectionTable != null {
      var b := s.frozenIndirectionTable.HasEmptyLoc(parentref);
      if b {
        print "giving up; flush can't run because frozen isn't written";
        return;
      }
    }

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

      var newchildref := allocBookkeeping(s, newchild.children);
      if newchildref.None? {
        var _ := FreeMutBucket(newparentBucket);
        var _ := FreeNode(newchild);
        print "giving up; could not get parentref\n";
      } else {
        s.cache.Insert(newchildref.value, newchild);

        var newparent_children := s.cache.NodeUpdateSlot(parentref,
          slot, newparentBucket, newchildref.value);
        writeBookkeeping(s, parentref, newparent_children);

        //Native.BenchmarkingUtil.end();
      }
    } else {
        print "giving up; flush can't run because flushed keys are out of bound for its children";
        return;
    }
  }
}
