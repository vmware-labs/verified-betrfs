include "BookkeepingImpl.i.dfy"
include "GrowModel.i.dfy"

module GrowImpl { 
  import opened IOImpl
  import opened BookkeepingImpl
  import opened StateBCImpl
  import opened BoxNodeImpl
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

  import opened NativeTypes

  /// The root was found to be too big: grow
  method grow(s: ImplVariables)
  requires Inv(s)
  requires s.ready
  requires BT.G.Root() in s.cache.I()
  requires |s.ephemeralIndirectionTable.I().graph| <= IndirectionTableModel.MaxSize() - 2
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures s.I() == GrowModel.grow(old(s.I()))
  {
    GrowModel.reveal_grow();

    BookkeepingModel.lemmaChildrenConditionsOfNode(s.I(), BT.G.Root());

    assert s.blockAllocator.Repr <= s.Repr();

    if s.frozenIndirectionTable != null {
      var b := s.frozenIndirectionTable.HasEmptyLoc(BT.G.Root());
      if b {
        print "giving up; grow can't run because frozen isn't written";
        return;
      }
    }

    var oldrootOpt := s.cache.GetOpt(BT.G.Root());
    var oldroot := oldrootOpt.value;
    var oldpivots := oldroot.GetPivots();

    var containsall := ComputeContainsAllKeys(oldpivots);
    if !containsall {
      print "giving up; grow can't run because root node is incorrect";
      return;
    }

    BookkeepingModel.lemmaChildrenConditionsSingleOfAllocBookkeeping(s.I(), oldroot.Read().children);
    var children := oldroot.GetChildren();
    var newref := allocBookkeeping(s, children);

    match newref {
      case None => {
        print "giving up; could not allocate ref\n";
      }
      case Some(newref) => {
        WeightBucketEmpty();

        linear var mutbucket := MutBucket.Alloc();
        linear var buckets := lseq_alloc(1);
        lseq_give_inout(inout buckets, 0, mutbucket);

        var newroot := new Node(InitPivotTable(), Some([newref]), buckets);
        assert newroot.I() == BT.G.Node(InitPivotTable(), Some([newref]), [B(map[])]);
        assert s.I().cache[BT.G.Root()] == old(s.I().cache[BT.G.Root()]);
        assert fresh(newroot.Repr);

        writeBookkeeping(s, BT.G.Root(), Some([newref]));

        s.cache.MoveAndReplace(BT.G.Root(), newref, newroot);

        ghost var a := s.I();
        ghost var b := GrowModel.grow(old(s.I()));
        assert a.cache == b.cache;
        assert a.ephemeralIndirectionTable == b.ephemeralIndirectionTable;
        assert a.lru == b.lru;
      }
    }
  }
}
