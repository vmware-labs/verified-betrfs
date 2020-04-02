include "BookkeepingModel.i.dfy"

module GrowModel { 
  import opened StateModel
  import opened IOModel
  import opened BookkeepingModel
  import opened ViewOp
  import opened DiskOpModel

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets
  import opened BucketWeights
  import opened Bounds
  import opened BucketsLib

  import opened NativeTypes

  /// The root was found to be too big: grow
  function {:opaque} grow(k: Constants, s: BCVariables)
  : (BCVariables)
  requires BCInv(k, s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  requires |s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 2
  {
    lemmaChildrenConditionsOfNode(k, s, BT.G.Root());

    if (
      && s.frozenIndirectionTable.Some?
      && IndirectionTableModel.HasEmptyLoc(s.frozenIndirectionTable.value, BT.G.Root())
    ) then (
      s
    ) else (
      var oldroot := s.cache[BT.G.Root()];
      var (s1, newref) := allocBookkeeping(k, s, oldroot.children);

      lemmaChildrenConditionsSingleOfAllocBookkeeping(k, s, oldroot.children);

      match newref {
        case None => (
          s1
        )
        case Some(newref) => (
          var newroot := Node([], Some([newref]), [B(map[])]);
          var s2 := writeBookkeeping(k, s1, BT.G.Root(), newroot.children);
          var s' := s2.(cache := s2.cache[newref := oldroot][BT.G.Root() := newroot]);
          s'
        )
      }
    )
  }

  lemma growCorrect(k: Constants, s: BCVariables)
  requires BCInv(k, s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  requires TotalCacheSize(s) <= MaxCacheSize() - 1
  requires |s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 2
  ensures var s' := grow(k, s);
    && WFBCVars(s')
    && betree_next(k, IBlockCache(s), IBlockCache(s'))
  {
    reveal_grow();

    var s' := grow(k, s);

    lemmaChildrenConditionsOfNode(k, s, BT.G.Root());

    if (
      && s.frozenIndirectionTable.Some?
      && IndirectionTableModel.HasEmptyLoc(s.frozenIndirectionTable.value, BT.G.Root())
    ) {
      assert noop(k, IBlockCache(s), IBlockCache(s));
      return;
    }

    var oldroot := s.cache[BT.G.Root()];
    var (s1, newref) := allocWithNode(k, s, oldroot);
    reveal_allocBookkeeping();
    reveal_writeBookkeeping();

    match newref {
      case None => {
        assert noop(k, IBlockCache(s), IBlockCache(s1));
      }
      case Some(newref) => {
        var newroot := Node([], Some([newref]), [B(map[])]);
        WeightBucketListOneEmpty();

        assert BT.G.Root() in s.cache;
        assert BT.G.Root() in ICache(s.cache);
        assert BT.G.Root() in ICache(s1.cache);
        assert BT.G.Root() in s1.cache;

        var s2 := writeWithNode(k, s1, BT.G.Root(), newroot);
        assert s2 == s';

        allocCorrect(k, s, oldroot);
        writeCorrect(k, s1, BT.G.Root(), newroot);

        var growth := BT.RootGrowth(INode(oldroot), newref);
        assert INode(newroot) == BT.G.Node([], Some([growth.newchildref]), [B(map[])]);
        var step := BT.BetreeGrow(growth);
        BC.MakeTransaction2(Ik(k).bc, IBlockCache(s), IBlockCache(s1), IBlockCache(s'), BT.BetreeStepOps(step));
        assert BBC.BetreeMove(Ik(k).bc, IBlockCache(s), IBlockCache(s'), BlockDisk.NoDiskOp, AdvanceOp(UI.NoOp, true), step);
        assert stepsBetree(k, IBlockCache(s), IBlockCache(s'), AdvanceOp(UI.NoOp, true), step);
      }
    }
  }
}
