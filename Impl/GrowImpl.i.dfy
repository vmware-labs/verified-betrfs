include "BookkeepingImpl.i.dfy"
include "GrowModel.i.dfy"

module GrowImpl { 
  import opened IOImpl
  import opened BookkeepingImpl
  import opened StateImpl
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

  import opened NativeTypes

  /// The root was found to be too big: grow
  method grow(k: ImplConstants, s: ImplVariables)
  requires Inv(k, s)
  requires s.ready
  requires BT.G.Root() in s.cache.I()
  requires |s.ephemeralIndirectionTable.I().graph| <= IndirectionTableModel.MaxSize() - 2
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures s.I() == GrowModel.grow(Ic(k), old(s.I()))
  {
    GrowModel.reveal_grow();

    BookkeepingModel.lemmaChildrenConditionsOfNode(Ic(k), s.I(), BT.G.Root());

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

    BookkeepingModel.lemmaChildrenConditionsSingleOfAllocBookkeeping(Ic(k), s.I(), oldroot.children);
    var newref := allocBookkeeping(k, s, oldroot.children);

    match newref {
      case None => {
        print "giving up; could not allocate ref\n";
      }
      case Some(newref) => {
        //var emptyPkv := PKV.EmptyPkv();
        WeightBucketEmpty();

        var mutbucket := new MutBucket();

        MutBucket.ListReprOfLen1([mutbucket]);
        MutBucket.ReprSeqDisjointOfLen1([mutbucket]);
        var newroot := new Node([], Some([newref]), [mutbucket]);
        
        assert newroot.I() == IM.Node([], Some([newref]), [B(map[])]);
        assert s.I().cache[BT.G.Root()] == old(s.I().cache[BT.G.Root()]);
        assert fresh(newroot.Repr);

        writeBookkeeping(k, s, BT.G.Root(), newroot.children);

        s.cache.MoveAndReplace(BT.G.Root(), newref, newroot);

        ghost var a := s.I();
        ghost var b := GrowModel.grow(Ic(k), old(s.I()));
        assert a.cache == b.cache;
        assert a.ephemeralIndirectionTable == b.ephemeralIndirectionTable;
        assert a.lru == b.lru;
      }
    }
  }
}
