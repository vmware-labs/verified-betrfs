include "BookkeepingImpl.i.dfy"
include "BookkeepingModel.i.dfy"
// include "GrowModel.i.dfy"

module GrowImpl { 
  import opened IOImpl
  import opened BookkeepingImpl
  import opened StateBCImpl
  import opened NodeImpl
  import opened BucketImpl
  import opened DiskOpImpl
  import BookkeepingModel

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

  import BlockDisk
  import opened ViewOp
  import IOModel

  import IT = IndirectionTable

  import opened NativeTypes
  import SSM = StateSectorModel

  /// The root was found to be too big: grow
  method grow(linear inout s: ImplVariables)
  requires old_s.BCInv()
  requires old_s.Ready?
  requires BT.G.Root() in old_s.IBlockCache().cache
  requires |old_s.IBlockCache().ephemeralIndirectionTable.graph| <= IT.MaxSize() - 2
  requires old_s.totalCacheSize() <= MaxCacheSize() - 1

  ensures s.Ready?
  ensures s.WFBCVars()
  ensures IOModel.betree_next(old_s.IBlockCache(), s.IBlockCache())
  {
    var root := BT.G.Root();
    lemmaChildrenConditionsOfNode(s, root);
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
        assert IOModel.noop(old_s.IBlockCache(), s.IBlockCache());
        assert IOModel.betree_next(old_s.IBlockCache(), s.IBlockCache());
      } else {
        var newref := allocBookkeeping(inout s, oldchildren);
        match newref {
          case None => {
            print "giving up; could not allocate ref\n";
            assert IOModel.noop(old_s.IBlockCache(), s.IBlockCache());
            assert IOModel.betree_next(old_s.IBlockCache(), s.IBlockCache());
          }
          case Some(newref) => {
            WeightBucketEmpty();

            linear var mutbucket := MutBucket.Alloc();
            linear var buckets := lseq_alloc(1);
            lseq_give_inout(inout buckets, 0, mutbucket);
            linear var newroot := Node(InitPivotTable(), Some([newref]), buckets);

            writeBookkeeping(inout s, root, Some([newref]));
            inout s.cache.MoveAndReplace(root, newref, newroot);

            // assume && WFCache(s.cache.I());

            ghost var old_root := old_s.cache.I()[root];
            ghost var gs0 := old_s.IBlockCache();

            ghost var (gs1: BC.Variables, newref2) := BookkeepingModel.allocWithNode(gs0, old_root);
            // assume newref2.Some? && newref == newref2.value;
            ghost var gs2 := BookkeepingModel.writeWithNode(gs1, BT.G.Root(), newroot.I());

            BookkeepingModel.writeCorrect(gs1, BT.G.Root(), newroot.I());

            // ghost var growth := BT.RootGrowth(SSM.INode(old_s.cache.I()[root]), newref);
            // assert SSM.INode(newroot.I()) == BT.G.Node(InitPivotTable(), Some([growth.newchildref]), [B(map[])]);
            // ghost var step := BT.BetreeGrow(growth);
            // assert BT.ValidGrow(growth);
            // BC.MakeTransaction2(old_s.IBlockCache(), s1, s.IBlockCache(), BT.BetreeStepOps(step));
            // assert BBC.BetreeMove(old_s.IBlockCache(), s.IBlockCache(), BlockDisk.NoDiskOp, AdvanceOp(UI.NoOp, true), step);
            // assert IOModel.stepsBetree(old_s.IBlockCache(), s.IBlockCache(), AdvanceOp(UI.NoOp, true), step);
            // assert IOModel.betree_next(old_s.IBlockCache(), s.IBlockCache());

            assume false;
          }
        }
      }
    } else {
        assert IOModel.noop(old_s.IBlockCache(), s.IBlockCache());
        assert IOModel.betree_next(old_s.IBlockCache(), s.IBlockCache());
    }
  }
}
