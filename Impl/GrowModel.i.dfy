// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "BookkeepingModel.i.dfy"

module GrowModel { 
  import opened StateBCModel
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

  /// The root was found to be too big: grow
  function {:opaque} grow(s: BCVariables)
  : (BCVariables)
  requires BCInv(s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  requires |s.ephemeralIndirectionTable.graph| <= IT.MaxSize() - 2
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
            var newroot := BT.G.Node(InitPivotTable(), Some([newref]), [EmptyBucket()]);
            var s2 := writeBookkeeping(s1, BT.G.Root(), newroot.children);
            var s' := s2.(cache := s2.cache[BT.G.Root() := newroot][newref := oldroot]);
            s'
          )
        }
      )
    )
  }

  lemma growCorrect(s: BCVariables)
  requires grow.requires(s)
  requires TotalCacheSize(s) <= MaxCacheSize() - 1
  ensures var s' := grow(s);
    && WFBCVars(s')
    && betree_next(IBlockCache(s), IBlockCache(s'))
  {
    reveal_grow();

    var s' := grow(s);

    lemmaChildrenConditionsOfNode(s, BT.G.Root());

    if (
      && s.frozenIndirectionTable.Some?
      && s.frozenIndirectionTable.value.hasEmptyLoc(BT.G.Root())
    ) {
      assert noop(IBlockCache(s), IBlockCache(s));
      return;
    }

    var oldroot := s.cache[BT.G.Root()];
    if !ContainsAllKeys(oldroot.pivotTable) {
      assert noop(IBlockCache(s), IBlockCache(s));
      return;
    }

    var (s1, newref) := allocWithNode(s, oldroot);
    reveal_allocBookkeeping();
    reveal_writeBookkeeping();

    match newref {
      case None => {
        assert noop(IBlockCache(s), IBlockCache(s1));
      }
      case Some(newref) => {
        var newroot := BT.G.Node(InitPivotTable(), Some([newref]), [EmptyBucket()]);
        WeightBucketListOneEmpty();

        assert BT.G.Root() in s.cache;
        assert BT.G.Root() in ICache(s.cache);
        assert BT.G.Root() in ICache(s1.cache);
        assert BT.G.Root() in s1.cache;

        var s2 := writeWithNode(s1, BT.G.Root(), newroot);
        assert s2 == s';

        allocCorrect(s, oldroot);
        writeCorrect(s1, BT.G.Root(), newroot);

        var growth := BT.RootGrowth(INode(oldroot), newref);
        assert INode(newroot) == BT.G.Node(InitPivotTable(), Some([growth.newchildref]), [EmptyBucket()]);
        var step := BT.BetreeGrow(growth);
        assert BT.ValidGrow(growth);
        BC.MakeTransaction2(IBlockCache(s), IBlockCache(s1), IBlockCache(s'), BT.BetreeStepOps(step));
        assert BBC.BetreeMove(IBlockCache(s), IBlockCache(s'), BlockDisk.NoDiskOp, AdvanceOp(UI.NoOp, true), step);
        assert stepsBetree(IBlockCache(s), IBlockCache(s'), AdvanceOp(UI.NoOp, true), step);
      }
    }
  }
}
