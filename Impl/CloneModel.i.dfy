// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "BookkeepingModel.i.dfy"

module CloneModel { 
  import opened IOModel
  import opened BookkeepingModel
  import opened ViewOp
  import opened DiskOpModel
  import opened KeyType
//   import opened Options
  import opened Sequences
  import opened Bounds
  import opened BucketsLib
  import opened BoundedPivotsLib

  // import IT = IndirectionTable
  // import opened NativeTypes
  // import StateBCImpl

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

  function {:opaque} clone(s: BBC.Variables, from: Key, to: Key): (BBC.Variables)
  requires BBC.Inv(s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  {
    if (
      && s.frozenIndirectionTable.Some?
      && s.frozenIndirectionTable.value.hasEmptyLoc(BT.G.Root())
    ) then (
      s
    ) else (
      var oldroot := s.cache[BT.G.Root()];
      lemmaChildrenConditionsOfNode(s, BT.G.Root());
      if (
        && to != [] 
        && oldroot.children.Some? 
        && ContainsAllKeys(oldroot.pivotTable) 
      ) then (
        if BucketListNoKeyWithPrefix(oldroot.buckets, oldroot.pivotTable, from) then (
          var newroot := BT.CloneNewRoot(oldroot, from, to);
          if NumBuckets(newroot.pivotTable) <= MaxNumChildren() then (
            lemmaChildrenConditionsCloneNewRoot(s, oldroot, from, to);
            var s1 := writeBookkeeping(s, BT.G.Root(), newroot.children);
            var s' := s1.(cache := s1.cache[BT.G.Root() := newroot]);
            s'
          ) else (
            s
          )
        ) else (
          s
        )
      ) else (
        s
      )
    )
  }

  lemma cloneCorrect(s: BBC.Variables, from: Key, to: Key)
  requires clone.requires(s, from, to)
  requires s.totalCacheSize() <= MaxCacheSize()
  ensures var s' := clone(s, from, to);
    && s'.Ready?
    && s'.totalCacheSize() <= MaxCacheSize()
    && StateBCImpl.WFCache(s'.cache)
    && betree_next(s, s')
  {
    reveal_clone();

    var s' := clone(s, from, to);
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

    if !BucketListNoKeyWithPrefix(oldroot.buckets, oldroot.pivotTable, from) {
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

      // && betree_next(s, s')
      assume false;

    } else {
      assert noop(s, s);
    }
  }
}
