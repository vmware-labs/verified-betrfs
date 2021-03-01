include "BookkeepingModel.i.dfy"

module GrowModel { 
  import opened StateSectorModel

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
  import opened BoundedPivotsLib

  import IT = IndirectionTable
  import opened NativeTypes
  import StateBCImpl

  /// The root was found to be too big: grow
  function {:opaque} grow(s: BBC.Variables)
  : (BBC.Variables)
  requires BBC.Inv(s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  {
    lemmaChildrenConditionsOfNode(s, BT.G.Root());

    if (
      && s.frozenIndirectionTable.Some?
      && s.frozenIndirectionTable.value.hasEmptyLoc(BT.G.Root())
    ) then (
      s
    ) else (
      var oldroot := s.cache[BT.G.Root()];
      if !ContainsAllKeys(oldroot.pivotTable) then (
        s
      ) else (
        var (s1, newref) := allocBookkeeping(s, oldroot.children);
        lemmaChildrenConditionsSingleOfAllocBookkeeping(s, oldroot.children);

        match newref {
          case None => (
            s1
          )
          case Some(newref) => (
            var newroot := BT.G.Node(InitPivotTable(), Some([newref]), [B(map[])]);
            var s2 := writeBookkeeping(s1, BT.G.Root(), newroot.children);
            var s' := s2.(cache := s2.cache[BT.G.Root() := newroot][newref := oldroot]);
            s'
          )
        }
      )
    )
  }

  lemma growCorrect(s: BBC.Variables)
  requires grow.requires(s)
  requires s.totalCacheSize() <= MaxCacheSize() - 1
  ensures var s' := grow(s);
    && s'.Ready?
    && s'.totalCacheSize() <= MaxCacheSize()
    && StateBCImpl.WFCache(s'.cache)
    && betree_next(s, s')
  {
    reveal_grow();

    var s' := grow(s);

    lemmaChildrenConditionsOfNode(s, BT.G.Root());

    if (
      && s.frozenIndirectionTable.Some?
      && var table := s.frozenIndirectionTable.value;
      && BT.G.Root() in table.graph
      && BT.G.Root() !in table.locs
    ) {
      assert noop(s, s);
      return;
    }

    var oldroot := s.cache[BT.G.Root()];
    if !ContainsAllKeys(oldroot.pivotTable) {
      assert noop(s, s);
      return;
    }

    var (s1, newref) := allocWithNode(s, oldroot);
    reveal_allocBookkeeping();
    reveal_writeBookkeeping();

    match newref {
      case None => {
        assert noop(s, s);
      }
      case Some(newref) => {
        var newroot := BT.G.Node(InitPivotTable(), Some([newref]), [B(map[])]);
        WeightBucketListOneEmpty();

        assert BT.G.Root() in s.cache;
        assert BT.G.Root() in s1.cache;

        var s2 := writeWithNode(s1, BT.G.Root(), newroot);
        assert s2 == s';

        allocCorrect(s, oldroot);
        writeCorrect(s1, BT.G.Root(), newroot);

        var growth := BT.RootGrowth(oldroot, newref);
        assert newroot == BT.G.Node(InitPivotTable(), Some([growth.newchildref]), [B(map[])]);
        var step := BT.BetreeGrow(growth);
        assert BT.ValidGrow(growth);
        BC.MakeTransaction2(s, s1, s', BT.BetreeStepOps(step));
        assert BBC.BetreeMove(s, s', BlockDisk.NoDiskOp, AdvanceOp(UI.NoOp, true), step);
        assert stepsBetree(s, s', AdvanceOp(UI.NoOp, true), step);
      }
    }
  }
}
