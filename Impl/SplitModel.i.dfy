// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "BookkeepingModel.i.dfy"

module SplitModel {
  import opened IOModel
  import opened BookkeepingModel
  import opened ViewOp
  import opened DiskOpModel

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import IT = IndirectionTable
  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import opened KeyType
  import opened PivotBetreeSpec`Internal
  import opened BoundedPivotsLib
  import opened TranslationLib
  import opened TranslationImpl
  import PBSWF = PivotBetreeSpecWFNodes

  import opened NativeTypes

  lemma lemmaChildrenConditionsRestrictAndTranslateChild(s: BBC.Variables, 
      parent: Node, child: Node, slot: int)
  requires s.Ready?
  requires WFNode(parent)
  requires WFNode(child)
  requires 0 <= slot < NumBuckets(parent.pivotTable)
  requires ParentKeysInChildRange(parent.pivotTable, parent.edgeTable, child.pivotTable, slot)
  requires ChildrenConditions(s, child.children)
  ensures ChildrenConditions(s, RestrictAndTranslateChild(parent, child, slot).children)
  {
    reveal_CutoffNode();
    reveal_CutoffNodeAndKeepLeft();
    reveal_CutoffNodeAndKeepRight();
  }

  lemma lemmaChildrenConditionsSplitChild(
      s: BBC.Variables, child: Node, num_children_left: int)
  requires SplitChildLeft.requires(child, num_children_left)
  requires SplitChildRight.requires(child, num_children_left)
  requires s.Ready?
  requires ChildrenConditions(s, child.children)
  ensures ChildrenConditions(s, SplitChildLeft(child, num_children_left).children)
  ensures ChildrenConditions(s, SplitChildRight(child, num_children_left).children)
  {
  }

  // TODO can we get BetreeBlockCache to ensure that will be true generally whenever taking a betree step?
  // This sort of proof logic shouldn't have to be in the implementation.
  lemma lemmaSplitChildValidReferences(parent: Node, child1: BT.G.Node, child: BT.G.Node, slot: int, num_children_left: int, graph: map<BT.G.Reference, seq<BT.G.Reference>>)
  requires BT.WFNode(parent)
  requires BT.WFNode(child1)
  requires 0 <= slot < NumBuckets(parent.pivotTable)
  requires ParentKeysInChildRange(parent.pivotTable, parent.edgeTable, child1.pivotTable, slot)
  requires child == RestrictAndTranslateChild(parent, child1, slot)
  requires 1 <= num_children_left < |child.buckets|
  requires BC.BlockPointsToValidReferences(child1, graph);
  ensures BC.BlockPointsToValidReferences(BT.SplitChildLeft(child, num_children_left), graph);
  ensures BC.BlockPointsToValidReferences(BT.SplitChildRight(child, num_children_left), graph);
  {
  }

  lemma lemmaSplitParentValidReferences(fused_parent: BT.G.Node, pivot: Key, slot: int, left_childref: BT.G.Reference, right_childref: BT.G.Reference, graph: map<BT.G.Reference, seq<BT.G.Reference>>)
  requires BT.WFNode(fused_parent)
  requires 0 <= slot < |fused_parent.buckets|
  requires fused_parent.children.Some?
  requires BC.BlockPointsToValidReferences(fused_parent, graph);
  requires left_childref in graph
  requires right_childref in graph
  requires PivotInsertable(fused_parent.pivotTable, slot+1, pivot)
  ensures BC.BlockPointsToValidReferences(SplitParent(fused_parent, pivot, slot, left_childref, right_childref), graph);
  {
    var split_parent := SplitParent(fused_parent, pivot, slot, left_childref, right_childref);
    forall r | r in BT.G.Successors(split_parent)
    ensures r in graph
    {
      assert BC.BlockPointsToValidReferences(fused_parent, graph);
      var idx :| 0 <= idx < |split_parent.children.value| && split_parent.children.value[idx] == r;
      if (idx < slot) {
        assert r == fused_parent.children.value[idx];
        assert r in graph;
      } else if (idx == slot) {
        assert r == left_childref;
        assert r in graph;
      } else if (idx == slot + 1) {
        assert r == right_childref;
        assert r in graph;
      } else {
        assert r == fused_parent.children.value[idx-1];
        assert r in graph;
      }
    }
  }

  function {:opaque} splitBookkeeping(s: BBC.Variables, left_childref: BT.G.Reference, right_childref: BT.G.Reference, parentref: BT.G.Reference, fused_parent_children: seq<BT.G.Reference>, left_child: Node, right_child: Node, slot: int) : (s': BBC.Variables)
  requires 0 <= slot < |fused_parent_children|
  requires s.Ready?
  requires s.WriteAllocConditions()
  requires ChildrenConditions(s, left_child.children)
  requires ChildrenConditions(s, right_child.children)
  requires ChildrenConditions(s, Some(fused_parent_children))
  requires |fused_parent_children| < MaxNumChildren()
  ensures s'.Ready?
  ensures s'.cache == s.cache
  {
    lemmaChildrenConditionsPreservedWriteBookkeeping(s, left_childref, left_child.children, right_child.children);
    lemmaChildrenConditionsPreservedWriteBookkeeping(s, left_childref, left_child.children, Some(fused_parent_children));
    lemmaRefInGraphOfWriteBookkeeping(s, left_childref, left_child.children);
    var s1 := writeBookkeeping(s, left_childref, left_child.children);

    lemmaChildrenConditionsPreservedWriteBookkeeping(s1, right_childref, right_child.children, Some(fused_parent_children));
    lemmaRefInGraphOfWriteBookkeeping(s1, right_childref, right_child.children);
    lemmaRefInGraphPreservedWriteBookkeeping(s1, right_childref, right_child.children, left_childref);

    var s2 := writeBookkeeping(s1, right_childref, right_child.children);

    lemmaChildrenConditionsOfReplace1With2(s2, fused_parent_children, slot, left_childref, right_childref);

    var s3 := writeBookkeeping(s2, parentref, Some(replace1with2(fused_parent_children, left_childref, right_childref, slot)));

    s3
  }

  function {:opaque} splitCacheChanges(s: BBC.Variables, left_childref: BT.G.Reference,
      right_childref: BT.G.Reference, parentref: BT.G.Reference, slot: int, num_children_left: int, pivot: Key, left_child: Node, right_child: Node) : (s': BBC.Variables)
  requires s.Ready?
  requires parentref in s.cache
  requires BT.WFNode(s.cache[parentref]);
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].children.value|
  {
    var fused_parent := s.cache[parentref];
    var split_parent := SplitParent(fused_parent, pivot, slot, left_childref, right_childref);
    s.(cache := s.cache
        [left_childref := left_child]
        [right_childref := right_child]
        [parentref := split_parent])
  }

  function {:opaque} splitDoChanges(s: BBC.Variables, child: Node,
      left_childref: BT.G.Reference, right_childref: BT.G.Reference, parentref: BT.G.Reference,
      fused_parent_children: seq<BT.G.Reference>, slot: int) : (s': BBC.Variables)
  requires s.Ready?
  requires parentref in s.cache
  requires WFNode(s.cache[parentref]);
  requires WFPivots(child.pivotTable)
  requires NumBuckets(child.pivotTable) == |child.buckets|
  requires |child.edgeTable| == |child.buckets| 
  requires child.children.Some? ==> |child.children.value| == |child.buckets|
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires 0 <= slot < |fused_parent_children|
  requires |child.buckets| >= 2
  requires s.WriteAllocConditions()
  requires ChildrenConditions(s, Some(fused_parent_children))
  requires ChildrenConditions(s, child.children)
  requires |fused_parent_children| < MaxNumChildren()
  {
    var num_children_left := |child.buckets| / 2;
    var pivot := GetKey(child.pivotTable, num_children_left);

    if !PivotInsertable(s.cache[parentref].pivotTable, slot+1, pivot) then (
      s
    ) else if !SplitChildrenWeight(child.buckets, num_children_left) then (
      s
    ) else (
      var left_child := SplitChildLeft(child, num_children_left);
      var right_child := SplitChildRight(child, num_children_left);
      var s3 := splitBookkeeping(s, left_childref, right_childref, parentref, fused_parent_children, left_child, right_child, slot);
      var s' := splitCacheChanges(s3, left_childref, right_childref, parentref, slot, num_children_left, pivot, left_child, right_child);
      s'
    )
  }

  function {:opaque} doSplit(s: BBC.Variables, parentref: BT.G.Reference, childref: BT.G.Reference, slot: int, refUpperBound: uint64)
  : (s': BBC.Variables)
  requires s.Ready?
  requires BBC.Inv(s)
  requires childref in s.ephemeralIndirectionTable.graph
  requires parentref in s.ephemeralIndirectionTable.graph
  requires childref in s.cache
  requires parentref in s.cache
  requires s.cache[parentref].children.Some?
  requires |s.cache[parentref].buckets| <= MaxNumChildren() - 1
  requires 0 <= slot < |s.cache[parentref].children.value|
  requires s.cache[parentref].children.value[slot] == childref
  requires forall r | r in s.ephemeralIndirectionTable.graph :: r <= refUpperBound
  {
    if (
      && s.frozenIndirectionTable.Some?
      && s.frozenIndirectionTable.value.hasEmptyLoc(parentref)
    ) then (
      s
    ) else (
      var fused_parent := s.cache[parentref];
      var fused_child := s.cache[childref];

      if !( ParentKeysInChildRange(fused_parent.pivotTable, fused_parent.edgeTable, fused_child.pivotTable, slot)
      ) then (
        s
      ) else (
        var lcp := PivotLcp(fused_parent.pivotTable[slot], fused_parent.pivotTable[slot+1]);
        var prefix := fused_parent.edgeTable[slot];
        if ( prefix.None? || (prefix.Some? && TranslateBucketsWillFit(fused_child.buckets, prefix.value, lcp))) then (
          lemmaChildrenConditionsOfNode(s, parentref);
          lemmaChildrenConditionsOfNode(s, childref);

          var child := RestrictAndTranslateChild(fused_parent, fused_child, slot);
          if (|child.pivotTable| == 2) then (
            // TODO there should be an operation which just
            // cuts off the node and doesn't split it.
            s
          ) else (
            lemmaChildrenConditionsRestrictAndTranslateChild(s, fused_parent, fused_child, slot);
            var left_childref := getFreeRef(s, refUpperBound);
            if left_childref.None? then (
              s
            ) else (
              var right_childref := getFreeRef2(s, left_childref.value, refUpperBound);
              if right_childref.None? then (
                s
              ) else (
                splitDoChanges(s, child, left_childref.value, right_childref.value,
                  parentref, fused_parent.children.value, slot)
              )
            )
          )
        ) else (
          s
        )
      )
    )
  }

  lemma {:timeLimitMultiplier 8} doSplitCorrect(s: BBC.Variables, parentref: BT.G.Reference, childref: BT.G.Reference, slot: int, refUpperBound: uint64)
  requires doSplit.requires(s, parentref, childref, slot, refUpperBound)
  requires s.totalCacheSize() <= MaxCacheSize() - 2
  ensures var s' := doSplit(s, parentref, childref, slot, refUpperBound);
    && s'.Ready?
    && s'.totalCacheSize() <= MaxCacheSize()
    && StateBCImpl.WFCache(s'.cache)
    && betree_next(s, s')
  {
    var s' := doSplit(s, parentref, childref, slot, refUpperBound);
    reveal_doSplit();

    if (
      && s.frozenIndirectionTable.Some?
      && s.frozenIndirectionTable.value.hasEmptyLoc(parentref)
    ) {
      assert noop(s, s);
      return;
    }

    var fused_parent := s.cache[parentref];
    var fused_child := s.cache[childref];

    if !( ParentKeysInChildRange(fused_parent.pivotTable, fused_parent.edgeTable, fused_child.pivotTable, slot)) {
      assert noop(s, s);
      return;
    }

    var lcp := PivotLcp(fused_parent.pivotTable[slot], fused_parent.pivotTable[slot+1]);
    var prefix := fused_parent.edgeTable[slot];
    if !(prefix.None? || (prefix.Some? && TranslateBucketsWillFit(fused_child.buckets, prefix.value, lcp))) {
      assert noop(s, s);
      return;
    }

    lemmaChildrenConditionsOfNode(s, parentref);
    lemmaChildrenConditionsOfNode(s, childref);

    var child := RestrictAndTranslateChild(fused_parent, fused_child, slot);
    if (|child.pivotTable| == 2) {
      // TODO there should be an operation which just
      // cuts off the node and doesn't split it.
      assert noop(s, s);
      return;
    }

    lemmaChildrenConditionsRestrictAndTranslateChild(s, fused_parent, fused_child, slot);
    var left_childref := getFreeRef(s, refUpperBound);
    if left_childref.None? {
      assert noop(s, s);
      return;
    }

    var right_childref := getFreeRef2(s, left_childref.value, refUpperBound);
    if right_childref.None? {
      assert noop(s, s);
      return;
    }

    reveal_splitDoChanges();
    var num_children_left := |child.buckets| / 2;
    var pivot := GetKey(child.pivotTable, num_children_left);

    if !PivotInsertable(fused_parent.pivotTable, slot+1, pivot) {
      assert noop(s, s);
      return;
    }

    if !SplitChildrenWeight(child.buckets, num_children_left) {
      assert noop(s, s);
      return;
    }
 
    lemmaChildrenConditionsSplitChild(s, child, num_children_left);
    var left_child := SplitChildLeft(child, num_children_left);
    var right_child := SplitChildRight(child, num_children_left);
    var split_parent := SplitParent(fused_parent, pivot, slot, left_childref.value, right_childref.value);

    lemmaChildrenConditionsPreservedWriteBookkeeping(s, left_childref.value, left_child.children, right_child.children);
    lemmaChildrenConditionsPreservedWriteBookkeeping(s, left_childref.value, left_child.children, fused_parent.children);
    lemmaRefInGraphOfWriteBookkeeping(s, left_childref.value, left_child.children);

    var s1 := writeWithNode(s, left_childref.value, left_child);
    var s2 := writeWithNode(s1, right_childref.value, right_child);

    lemmaChildrenConditionsOfReplace1With2(s2, fused_parent.children.value, slot, left_childref.value, right_childref.value);

    reveal_writeBookkeeping();
    reveal_splitCacheChanges();
    reveal_splitBookkeeping();

    var s3 := writeWithNode(s2, parentref, split_parent);
    assert s' == s3;

    var splitStep := NodeFusion(
      parentref,
      childref,
      left_childref.value,
      right_childref.value,
      fused_parent,
      split_parent,
      fused_child,
      left_child,
      right_child,
      slot,
      num_children_left,
      pivot
    );

    PBSWF.ValidSplitWritesWFNodes(splitStep);
    lemmaBlockPointsToValidReferences(s, childref);
    assert BC.BlockPointsToValidReferences(fused_child, s.ephemeralIndirectionTable.graph);
    lemmaSplitChildValidReferences(fused_parent, fused_child, child, slot, num_children_left, s.ephemeralIndirectionTable.graph);

    writeNewRefIsAlloc(s, left_childref.value, left_child);
    writeNewRefIsAlloc(s1, right_childref.value, right_child);

    lemmaBlockPointsToValidReferences(s, parentref);
    assert BC.BlockPointsToValidReferences(fused_parent, s2.ephemeralIndirectionTable.graph);
    lemmaSplitParentValidReferences(fused_parent, pivot, slot, left_childref.value, right_childref.value, s2.ephemeralIndirectionTable.graph);

    assert 1 <= num_children_left < |child.buckets|;
    assert splitStep.num_children_left == num_children_left;
    assert splitStep.fused_child == fused_child;
    assert left_childref.value != right_childref.value;
    assert ValidSplit(splitStep);
    var step := BetreeSplit(splitStep);
    var ops := [
      BT.G.AllocOp(left_childref.value, left_child),
      BT.G.AllocOp(right_childref.value, right_child),
      BT.G.WriteOp(parentref, split_parent)
    ];
    assert ops == BetreeStepOps(step);
    BC.MakeTransaction3(s, s1, s2, s', ops);
    assert stepsBetree(s, s', AdvanceOp(UI.NoOp, true), step);
  }
}
