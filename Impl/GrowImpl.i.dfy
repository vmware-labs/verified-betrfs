// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "BookkeepingImpl.i.dfy"
include "GrowModel.i.dfy"

module GrowImpl { 
  import opened IOImpl
  import opened BookkeepingImpl
  import opened StateBCImpl
  import opened NodeImpl
  import opened BucketImpl
  import opened DiskOpImpl
  import GrowModel

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets
  import opened BucketWeights
  import opened BucketsLib
  import opened LinearSequence_s
  import opened LinearSequence_i
  import opened BoundedPivotsLib
  import opened Bounds

  import IT = IndirectionTable

  import opened NativeTypes

  /// The root was found to be too big: grow
  method doGrow(linear inout s: ImplVariables)
  requires old_s.Inv()
  requires old_s.Ready?
  requires BT.G.Root() in old_s.I().cache
  requires |old_s.ephemeralIndirectionTable.graph| <= IT.MaxSize() - 2
  requires forall r | r in old_s.ephemeralIndirectionTable.graph :: r <= old_s.ephemeralIndirectionTable.refUpperBound

  ensures s.W()
  ensures s.Ready?
  ensures s.I() == GrowModel.grow(old_s.I(), old_s.ephemeralIndirectionTable.refUpperBound)
  ensures s.WriteAllocConditions()
  ensures LruModel.I(s.lru.Queue()) == s.cache.I().Keys;
  {
    GrowModel.reveal_grow();

    var root := BT.G.Root();
    BookkeepingModel.lemmaChildrenConditionsOfNode(s.I(), root);
    var nop := false;

    if s.frozenIndirectionTable.lSome? {
      var b := s.frozenIndirectionTable.value.HasEmptyLoc(root);
      if b {
        print "giving up; grow can't run because frozen isn't written";
        nop := true;
      }
    }

    if !nop {
      var oldpivots, oldchildren := s.cache.GetNodeInfo(root);
      var containsall := ComputeContainsAllKeys(oldpivots);
      if !containsall {
        print "giving up; grow can't run because root node is incorrect";
        assert old_s.I() == s.I();
      } else {
        // BookkeepingModel.lemmaChildrenConditionsSingleOfAllocBookkeeping(s.I(), oldchildren);
        var newref := allocBookkeeping(inout s, oldchildren);
        match newref {
          case None => {
            print "giving up; could not allocate ref\n";
            assert old_s.I() == s.I();
          }
          case Some(newref) => {
            // assert BookkeepingModel.ChildrenConditions(s.I(), Some([newref]));
            WeightBucketEmpty();

            linear var mutbucket := MutBucket.Alloc();
            linear var buckets := lseq_alloc(1);
            lseq_give_inout(inout buckets, 0, mutbucket);

            linear var newroot := Node(InitPivotTable(), Some([newref]), buckets);
            assert newroot.I() == BT.G.Node(InitPivotTable(), Some([newref]), [EmptyBucket()]);
            assert s.I().cache[root] == old_s.I().cache[root];

            writeBookkeeping(inout s, root, Some([newref]));
            inout s.cache.MoveAndReplace(root, newref, newroot);

            assert LruModel.I(s.lru.Queue()) == s.cache.I().Keys;
          }
        }
      }
    } else {
      assert old_s.I() == s.I();
    }
  }

  method grow(linear inout s: ImplVariables)
  requires old_s.Inv()
  requires old_s.Ready?
  requires BT.G.Root() in old_s.I().cache
  requires |old_s.ephemeralIndirectionTable.graph| <= IT.MaxSize() - 2
  requires old_s.totalCacheSize() <= MaxCacheSize() - 1
  
  ensures s.WFBCVars() && s.Ready?;
  ensures IOModel.betree_next(old_s.I(), s.I())
  {
    old_s.ephemeralIndirectionTable.UpperBounded();
    GrowModel.growCorrect(s.I(), old_s.ephemeralIndirectionTable.refUpperBound);
    doGrow(inout s);
    assert s.WFBCVars();
  }
}
