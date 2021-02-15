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

  import IT = IndirectionTable

  import opened NativeTypes

  /// The root was found to be too big: grow
  method grow(linear inout s: ImplVariables)
  requires old_s.Inv()
  requires old_s.Ready?
  requires BT.G.Root() in old_s.I().cache
  requires |old_s.I().ephemeralIndirectionTable.graph| <= IT.MaxSize() - 2
  ensures s.W()
  ensures s.Ready?
  ensures s.I() == GrowModel.grow(old_s.I())
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
      } else {
        BookkeepingModel.lemmaChildrenConditionsSingleOfAllocBookkeeping(s.I(), oldchildren);
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

            linear var newroot := Node(InitPivotTable(), Some([newref]), buckets);
            assert newroot.I() == BT.G.Node(InitPivotTable(), Some([newref]), [EmptyBucket()]);
            assert s.I().cache[root] == old_s.I().cache[root];

            writeBookkeeping(inout s, root, Some([newref]));
            inout s.cache.MoveAndReplace(root, newref, newroot);

            ghost var a := s.I();
            ghost var b := GrowModel.grow(old_s.I());
            assert a.cache == b.cache;
            assert a.ephemeralIndirectionTable == b.ephemeralIndirectionTable;
            assert a.lru == b.lru;
          }
        }
      }
    }
  }
}
