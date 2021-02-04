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

  import IT = IndirectionTable

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

  ensures s.W()
  ensures s.Ready?
  ensures FlushModel.flush(old_s.I(), parentref, slot as int, childref, 
    old_s.cache.I()[childref]) == s.I()
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
          // assert WeightBucket(newparentBucket.I()) <= WeightBucket(s.cache.I()[parentref].buckets[slot as int]);

          inout s.cache.Insert(newchildref.value, newchild);

          // assert WeightBucket(newparentBucket.I()) <= WeightBucket(s.cache.I()[parentref].buckets[slot as int]);

          var newparent_children := inout s.cache.NodeUpdateSlot(parentref,
            slot, newparentBucket, newchildref.value);
          writeBookkeeping(inout s, parentref, newparent_children);

          //Native.BenchmarkingUtil.end();
        }
      } else {
        print "giving up; flush can't run because flushed keys are out of bound for its children";
      }
    }
  }
}

/*
Impl/FlushImpl.i.dfy(32,9): Verification out of resource (Impl$$FlushImpl.__default.flush)
Impl/FlushImpl.i.dfy(83,30): Out of resource on BP5002: A precondition for this call might not hold.
Impl/CacheImpl.i.dfy(115,28): Related location: This is the precondition that might not hold.
Execution trace:
    (0,0): anon0
    (0,0): anon11_Else
    (0,0): anon3
    (0,0): anon12_Else
    (0,0): anon13_Then
    (0,0): anon14_Else
Impl/FlushImpl.i.dfy(85,64): Out of resource on BP5002: A precondition for this call might not hold.
Impl/CacheImpl.i.dfy(233,31): Related location: This is the precondition that might not hold.
Execution trace:
    (0,0): anon0
    (0,0): anon11_Else
    (0,0): anon3
    (0,0): anon12_Else
    (0,0): anon13_Then
    (0,0): anon14_Else
Impl/FlushImpl.i.dfy(85,64): Out of resource on BP5002: A precondition for this call might not hold.
Impl/CacheImpl.i.dfy(234,16): Related location: This is the precondition that might not hold.
Impl/../PivotBetree/PivotBetreeSpec.i.dfy(82,35): Related location
Execution trace:
    (0,0): anon0
    (0,0): anon11_Else
    (0,0): anon3
    (0,0): anon12_Else
    (0,0): anon13_Then
    (0,0): anon14_Else
Impl/FlushImpl.i.dfy(85,64): Out of resource on BP5002: A precondition for this call might not hold.
Impl/CacheImpl.i.dfy(234,16): Related location: This is the precondition that might not hold.
Impl/../PivotBetree/PivotBetreeSpec.i.dfy(83,47): Related location
Execution trace:
    (0,0): anon0
    (0,0): anon11_Else
    (0,0): anon3
    (0,0): anon12_Else
    (0,0): anon13_Then
    (0,0): anon14_Else
Impl/FlushImpl.i.dfy(85,64): Out of resource on BP5002: A precondition for this call might not hold.
Impl/CacheImpl.i.dfy(235,28): Related location: This is the precondition that might not hold.
Execution trace:
    (0,0): anon0
    (0,0): anon11_Else
    (0,0): anon3
    (0,0): anon12_Else
    (0,0): anon13_Then
    (0,0): anon14_Else
*/