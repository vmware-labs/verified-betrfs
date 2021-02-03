include "BookkeepingImpl.i.dfy"
// include "GrowModel.i.dfy"

module GrowImpl { 
  import opened IOImpl
  import opened BookkeepingImpl
  import opened StateBCImpl
  import opened NodeImpl
  import opened BucketImpl
  import opened DiskOpImpl
  // import GrowModel

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
  // ensures IOModel.betree_next(old_s.IBlockCache(), s.IBlockCache())
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
      } else {
        var newref := allocBookkeeping(inout s, oldchildren);

        match newref {
          case None => {
            print "giving up; could not allocate ref\n";
          }
          case Some(newref) => {
            WeightBucketEmpty();

            linear var mutbucket := MutBucket.Alloc();
            linear var buckets := lseq_alloc(1);
            lseq_give_inout(inout buckets, 0, mutbucket);

            linear var newroot := Node.Alloc(InitPivotTable(), Some([newref]), buckets);
            writeBookkeeping(inout s, root, Some([newref]));
            assert newref !in s.cache.I();
            inout s.cache.MoveAndReplace(root, newref, newroot);
            assert s.TotalCacheSize() == old_s.TotalCacheSize() + 1;

            assume && WFCache(s.cache.I());
          }
        }
      }
    }
  }
}