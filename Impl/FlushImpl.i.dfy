// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

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
  import opened TranslationImpl

  import opened NativeTypes
  import BookkeepingModel
  import FlushModel
  import IOModel

  import IT = IndirectionTable

  method {:timeLimitMultiplier 4} doFlush(linear inout s: ImplVariables, parentref: BT.G.Reference, slot: uint64, childref: BT.G.Reference)
  requires old_s.Inv()
  requires old_s.Ready?
  requires old_s.cache.ptr(childref).Some?

  requires parentref in old_s.ephemeralIndirectionTable.I().graph
  requires parentref in old_s.cache.I()

  requires old_s.cache.I()[parentref].children.Some?
  requires 0 <= slot as int < |old_s.cache.I()[parentref].children.value|
  requires old_s.cache.I()[parentref].children.value[slot] == childrefs

  requires childref in old_s.ephemeralIndirectionTable.I().graph

  requires |old_s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 2
  requires forall r | r in old_s.ephemeralIndirectionTable.graph :: r <= old_s.ephemeralIndirectionTable.refUpperBound

  ensures s.W()
  ensures s.Ready?
  ensures s.WriteAllocConditions()
  ensures s.I() == FlushModel.flush(old_s.I(), parentref, slot as int, childref, 
    old_s.cache.I()[childref], old_s.ephemeralIndirectionTable.refUpperBound);
  ensures LruModel.I(s.lru.Queue()) == s.cache.I().Keys;
  {
    ghost var refUpperBound := s.ephemeralIndirectionTable.refUpperBound;
    var b := false;
    if s.frozenIndirectionTable.lSome? {
      b := s.frozenIndirectionTable.value.HasEmptyLoc(parentref);
    }
  
    if b {
      print "giving up; flush can't run because frozen isn't written";
    } else {
      var parentpivots, parentedges, _ := s.cache.GetNodeInfo(parentref);
      var childpivots, _, _ := s.cache.GetNodeInfo(childref);

      var inrange := ComputeParentKeysInChildRange(parentpivots, parentedges, childpivots, slot);
      if inrange {
        var bucketsfit := parentedges[slot].None?;
        if parentedges[slot].Some? {
          var lcp := ComputePivotLcp(parentpivots[slot], parentpivots[slot+1]);
          bucketsfit := s.cache.NodeBucketsWillFitInPkv(childref, parentedges[slot].value, lcp);
        }

        if bucketsfit {
          linear var newchild := s.cache.NodeRestrictAndTranslateChild(parentref, childref, slot);
          var bucketslen := lseq_length_as_uint64(newchild.buckets);
          var succ, weight := MutBucket.tryComputeWeightOfSeq(newchild.buckets, 0, bucketslen);
          assert MutBucket.ILseq(newchild.buckets)[0..bucketslen] == MutBucket.ILseq(newchild.buckets);

          if succ && weight <= MaxTotalBucketWeightUint64() {
            //Native.BenchmarkingUtil.start();

            ghost var parentI := s.cache.I()[parentref];
            ghost var childI := s.cache.I()[childref];

            BookkeepingModel.lemmaChildrenConditionsOfNode(s.I(), childref);
            BookkeepingModel.lemmaChildrenConditionsOfNode(s.I(), parentref);
            FlushModel.lemmaChildrenConditionsRestrictAndTranslateChild(s.I(), parentI, childI, slot as int);
            assert BookkeepingModel.ChildrenConditions(s.I(), newchild.I().children);

            linear var Node(newchildpivots, newchildedges, newchildchildren, newchildbuckets) := newchild;
            BucketFlushModel.partialFlushWeightBound(parentI.buckets[slot as nat], newchildpivots, MutBucket.ILseq(newchildbuckets));
            linear var newparentBucket := s.cache.NodePartialFlush(inout newchildbuckets, parentref, newchildpivots, slot);
            newchild := Node(newchildpivots, newchildedges, newchildchildren, newchildbuckets);

            BookkeepingModel.lemmaChildrenConditionsUpdateOfAllocBookkeeping(
                s.I(), newchild.children, parentI.children.value, slot as int, refUpperBound);
            BookkeepingModel.allocRefDoesntEqual(s.I(), newchild.children, parentref, refUpperBound);

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
            var _ := FreeNode(newchild);
            print "giving up; flush can't run because flushed child will be overweight";
          }
        } else {
          print "giving up; flush can't run because flushed child can't be marshalled";
        }
      } else {
        print "giving up; flush can't run because flushed keys are out of bound for its children";
      }
    }
  }
  
  method {:timeLimitMultiplier 2} flush(linear inout s: ImplVariables, parentref: BT.G.Reference, slot: uint64, childref: BT.G.Reference)
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

  ensures s.WFBCVars() && s.Ready?
  ensures IOModel.betree_next(old_s.I(), s.I())
  {
    s.ephemeralIndirectionTable.UpperBounded();
    FlushModel.flushCorrect(s.I(), parentref, slot as int, childref, s.cache.I()[childref], s.ephemeralIndirectionTable.refUpperBound);
    doFlush(inout s, parentref, slot, childref);
  }
}