// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "BookkeepingModel.i.dfy"

module CloneModel { 
  import opened IOModel
  import opened BookkeepingModel
  import opened ViewOp
  import opened DiskOpModel
  import opened KeyType
  import opened Sequences
  import opened Bounds
  import opened BucketsLib
  import opened BoundedPivotsLib

  lemma lemmaChildrenConditionsCloneNewRoot(s: BBC.Variables, oldroot: Node, from: Key, to: Key)
  requires s.Ready?
  requires BT.CloneNewRoot.requires(oldroot, from, to)
  requires ChildrenConditions(s, oldroot.children)
  requires |BT.CloneNewRoot(oldroot, from, to).children.value| <= MaxNumChildren()
  ensures ChildrenConditions(s, BT.CloneNewRoot(oldroot, from, to).children)
  {
    BT.reveal_CutoffNode();
    BT.reveal_CutoffNodeAndKeepLeft();
    BT.reveal_CutoffNodeAndKeepRight();
  }

  function {:opaque} doClone(s: BBC.Variables, from: Key, to: Key): (BBC.Variables, bool)
  requires BBC.Inv(s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  {
    if (
      && s.frozenIndirectionTable.Some?
      && s.frozenIndirectionTable.value.hasEmptyLoc(BT.G.Root())
    ) then (
      (s, false)
    ) else (
      var oldroot := s.cache[BT.G.Root()];
      lemmaChildrenConditionsOfNode(s, BT.G.Root());
      if (
        && to != [] 
        && oldroot.children.Some? 
        && ContainsAllKeys(oldroot.pivotTable) 
      ) then (
        if BT.ValidCloneBucketList(oldroot, from) then (
          var newroot := BT.CloneNewRoot(oldroot, from, to);
          if NumBuckets(newroot.pivotTable) <= MaxNumChildren() then (
            lemmaChildrenConditionsCloneNewRoot(s, oldroot, from, to);
            var s1 := writeBookkeeping(s, BT.G.Root(), newroot.children);
            var s' := s1.(cache := s1.cache[BT.G.Root() := newroot]);
            (s', true)
          ) else (
            (s, false)
          )
        ) else (
          (s, false)
        )
      ) else (
        (s, false)
      )
    )
  }

  lemma doCloneCorrect(s: BBC.Variables, from: Key, to: Key)
  requires doClone.requires(s, from, to)
  requires s.totalCacheSize() <= MaxCacheSize()
  ensures var (s', success) := doClone(s, from, to);
      && (success ==>
        BBC.Next(s, s',
          BlockDisk.NoDiskOp,
          AdvanceOp(UI.CloneOp(BT.CloneMap(from, to)), true))
      )
      && (!success ==>
        betree_next(s, s')
      )
      && (StateBCImpl.WFCache(s'.cache))
      && s.totalCacheSize() == s'.totalCacheSize()
  {
    reveal_doClone();

    var (s', success) := doClone(s, from, to);
    lemmaChildrenConditionsOfNode(s, BT.G.Root());

    if (
      && s.frozenIndirectionTable.Some?
      && s.frozenIndirectionTable.value.hasEmptyLoc(BT.G.Root())
    ) {
      assert noop(s, s);
      return;
    }

    var oldroot := s.cache[BT.G.Root()];

    if !(
      && to != [] 
      && oldroot.children.Some? 
      && ContainsAllKeys(oldroot.pivotTable) 
    ) {
      assert noop(s, s);
      return;
    }

    if !BT.ValidCloneBucketList(oldroot, from) {
      assert noop(s, s);
      return;
    }

    var newroot := BT.CloneNewRoot(oldroot, from, to);
    if NumBuckets(newroot.pivotTable) <= MaxNumChildren() {
      lemmaChildrenConditionsCloneNewRoot(s, oldroot, from, to);

      reveal_writeBookkeeping();

      var s1 := writeWithNode(s, BT.G.Root(), newroot);
      writeCorrect(s, BT.G.Root(), newroot);
      assert s1 == s';

      var clone := BT.NodeClone(oldroot, newroot, from, to);
      var step := BT.BetreeClone(clone);

      assert BT.ValidClone(clone);
      BC.MakeTransaction1(s, s', BT.BetreeStepOps(step));
      assert BBC.BetreeMove(s, s', BlockDisk.NoDiskOp, AdvanceOp(UI.CloneOp(BT.CloneMap(from, to)), true), step);
      assert stepsBetree(s, s', AdvanceOp(UI.CloneOp(BT.CloneMap(from, to)), true), step);
    } else {
      assert noop(s, s);
    }
  }
}
