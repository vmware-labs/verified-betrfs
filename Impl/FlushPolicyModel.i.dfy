// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "FlushModel.i.dfy"
include "GrowModel.i.dfy"
include "SplitModel.i.dfy"
include "LeafModel.i.dfy"
include "../PivotBetree/Bounds.i.dfy"

module FlushPolicyModel {
  import opened IOModel
  import opened BookkeepingModel
  import opened FlushModel
  import opened GrowModel
  import opened SplitModel
  import opened LeafModel
  import opened InterpretationDiskOps
  import opened DiskOpModel

  import opened Sequences

  import opened BoundedPivotsLib
  import opened Bounds
  import opened NativeTypes
  import opened BucketsLib
  import opened BucketWeights
  import PivotBetreeSpec

  import IT = IndirectionTable

  datatype Action =
    | ActionPageIn(ref: BT.G.Reference)
    | ActionSplit(parentref: BT.G.Reference, slot: uint64)
    | ActionFlush(parentref: BT.G.Reference, slot: uint64)
    | ActionRepivot(ref: BT.G.Reference)
    | ActionGrow
    | ActionEvict
    | ActionFail

  predicate ValidStackSlots(s: BBC.Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>)
  {
    && |stack| == |slots| + 1
    && s.Ready?
    && (forall j | 0 <= j < |stack| :: stack[j] in s.cache)
    && (forall j | 0 <= j < |stack| - 1 :: s.cache[stack[j]].children.Some?)
    && (forall j | 0 <= j < |stack| - 1 :: slots[j] as int < |s.cache[stack[j]].children.value| <= MaxNumChildren())
  }

  predicate ValidAction(s: BBC.Variables, action: Action)
  {
    && s.Ready?
    && (action.ActionPageIn? ==> (
      && action.ref in s.ephemeralIndirectionTable.graph
      && action.ref !in s.cache
      && action.ref in s.ephemeralIndirectionTable.locs
      && s.totalCacheSize() <= MaxCacheSize() - 1
    ))
    && ((action.ActionSplit? || action.ActionFlush?) ==> (
      && action.parentref in s.ephemeralIndirectionTable.graph
      && action.parentref in s.cache
      && s.cache[action.parentref].children.Some?
      && 0 <= action.slot as int < |s.cache[action.parentref].children.value|
      && s.cache[action.parentref].children.value[action.slot] in s.cache
      && s.cache[action.parentref].children.value[action.slot] in s.ephemeralIndirectionTable.graph
    ))
    && (action.ActionSplit? ==> (
      && |s.cache[s.cache[action.parentref].children.value[action.slot]].buckets| >= 2
      && |s.cache[action.parentref].buckets| <= MaxNumChildren() - 1
      && s.totalCacheSize() <= MaxCacheSize() - 2
    ))
    && (action.ActionFlush? ==> (
      && s.totalCacheSize() <= MaxCacheSize() - 1
    ))
    && (action.ActionGrow? ==> (
      && s.totalCacheSize() <= MaxCacheSize() - 1
    ))
    && (action.ActionRepivot? ==> (
      && action.ref in s.ephemeralIndirectionTable.graph
      && action.ref in s.cache
      && s.cache[action.ref].children.None?
      && |s.cache[action.ref].buckets| == 1
    ))
  }

  function {:opaque} getActionToSplit(s: BBC.Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>, i: uint64) : (action : Action)
  requires 0 <= i as int < |stack|
  requires ValidStackSlots(s, stack, slots)
  ensures action.ActionGrow? || action.ActionRepivot? || action.ActionSplit? || action.ActionEvict?
  {
    if i == 0 then
      // Can't split root until we grow it.
      if s.totalCacheSize() <= MaxCacheSize() - 1 then (
        ActionGrow
      ) else (
        ActionEvict
      )
    else (
      if |s.cache[stack[i-1]].children.value| as uint64 < MaxNumChildren() as uint64 then (
        if |s.cache[stack[i]].buckets| == 1 then (
          ActionRepivot(stack[i])
        ) else (
          if s.totalCacheSize() <= MaxCacheSize() - 2 then (
            ActionSplit(stack[i-1], slots[i-1])
          ) else (
            ActionEvict
          )
        )
      ) else (
        getActionToSplit(s, stack, slots, i-1)
      )
    )
  }

  lemma {:timeLimitMultiplier 6} getActionToSplitValidAction(s: BBC.Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>, i: uint64)
  requires 0 <= i as int < |stack|
  requires BBC.Inv(s)
  requires ValidStackSlots(s, stack, slots)
  requires forall j | 0 <= j < |stack| :: stack[j] in s.ephemeralIndirectionTable.graph
  requires forall j | 0 <= j < |stack| - 1 :: s.cache[stack[j]].children.value[slots[j]] == stack[j+1]
  requires s.cache[stack[ |stack| - 1]].children.Some? ==> |s.cache[stack[ |stack| - 1]].buckets| >= 2
  requires i as int < |stack| - 1 ==> |s.cache[stack[i]].buckets| >= MaxNumChildren()
  ensures ValidAction(s, getActionToSplit(s, stack, slots, i))
  {
    reveal_getActionToSplit();
    var action := getActionToSplit(s, stack, slots, i);

    if i == 0 {
      assert ValidAction(s, action);
      return;
    }

    var pre := i - 1;

    if |s.cache[stack[pre]].children.value| >= MaxNumChildren() {
      getActionToSplitValidAction(s, stack, slots, pre);
      return;
    }

    assert |s.cache[stack[pre]].children.value| < MaxNumChildren();

    if |s.cache[stack[i]].buckets| as uint64 == 1 {
      assert i as int == |stack| - 1;

      assert s.cache[stack[i]].children.None?;
      assert ValidAction(s, action);
    } else {  
      if s.totalCacheSize() <= MaxCacheSize() - 2 {
        assert action == ActionSplit(stack[i-1], slots[i-1]);
        assert ValidAction(s, action);
      } else {
        assert ValidAction(s, action);
      }
    }
  }

  function {:opaque} getActionToFlush(s: BBC.Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>) : Action
  requires |stack| <= 40
  requires ValidStackSlots(s, stack, slots)
  requires BBC.Inv(s)
  decreases 0x1_0000_0000_0000_0000 - |stack|
  {
    if |stack| as uint64 == 40 then (
      ActionFail
    ) else (
      var ref := stack[|stack| as uint64 - 1];
      var node := s.cache[ref];
      if node.children.None? || |node.buckets| == MaxNumChildren() then (
        getActionToSplit(s, stack, slots, |stack| as uint64 - 1)
      ) else (
        var (slot, slotWeight) := biggestSlot(node.buckets);
        // TODO:
        //if slotWeight >= FlushTriggerWeight() as uint64 then (
        var childref := node.children.value[slot];
        if childref in s.cache then (
          var child := s.cache[childref];

          var childTotalWeight: uint64 := WeightBucketList(child.buckets) as uint64;
          if childTotalWeight + FlushTriggerWeight() as uint64 <= MaxTotalBucketWeight() as uint64 then (
            // If there's room for FlushTriggerWeight() worth of stuff, then
            // we flush. We flush as much as we can (which will end up being at least
            // FlushTriggerWeight - max key weight - max message weight).
            if s.totalCacheSize() <= MaxCacheSize() - 1 then (
              ActionFlush(ref, slot)
            ) else (
              ActionEvict
            )
          ) else (
            getActionToFlush(s, stack + [childref], slots + [slot])
          )
        ) else (
          if s.totalCacheSize() <= MaxCacheSize() - 1 then (
            ActionPageIn(childref)
          ) else (
            ActionEvict
          )
        )
      )
    )
  }

  predicate GetActionToFlushValidStackSlots(s: BBC.Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>)
  {
    && |stack| <= 40
    && ValidStackSlots(s, stack, slots)
    && BBC.Inv(s)
    && forall j | 0 <= j < |stack| :: stack[j] in s.ephemeralIndirectionTable.graph
    && forall j | 0 <= j < |stack| - 1 :: s.cache[stack[j]].children.value[slots[j]] == stack[j+1]
  }

  lemma getActionToFlushValidActionRec(s: BBC.Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>, slot: uint64, childref: BT.G.Reference)
    returns (stack': seq<BT.G.Reference>, slots': seq<uint64>)
    requires GetActionToFlushValidStackSlots(s, stack, slots)
    requires |stack| != 40
    requires var node := s.cache[stack[ |stack| as uint64 - 1]];
      && node.children.Some?
      && |node.buckets| < MaxNumChildren()
      && slot == biggestSlot(node.buckets).0
      && childref == node.children.value[slot]
      && childref in s.cache
      && WeightBucketList(s.cache[childref].buckets) + FlushTriggerWeight() > MaxTotalBucketWeight()

    ensures stack' == stack + [childref]
    ensures slots' == slots + [slot]
    ensures GetActionToFlushValidStackSlots(s, stack', slots')
  {
    var ref := stack[ |stack| as uint64 - 1];
    lemmaChildInGraph(s, ref, childref);

    stack' := stack + [childref];
    slots' := slots + [slot];

    var k := |stack| - 1;
    var node := s.cache[stack[k]];

    forall j | 0 <= j < |stack'|
    ensures stack'[j] in s.cache
    {
      if j == |stack'| - 1 {
        assert stack'[j] == childref;
      }
    }

    forall j | 0 <= j < |stack'| - 1
      ensures s.cache[stack'[j]].children.Some?
    {
      if j == k {
        assert s.cache[stack'[j]] == node;
      }
    }

    forall j | 0 <= j < |stack'| - 1
    ensures slots'[j] as int < |s.cache[stack'[j]].children.value| <= MaxNumChildren()
    {
      if j == k {
        assert slots'[k] == slot;
        assert s.cache[stack'[j]] == node;
        assert slot as int < |node.buckets| < MaxNumChildren();
        assert PivotBetreeSpec.WFNode(node);
        assert |node.buckets| == |node.children.value|;
      }
    }
  }

  lemma {:timeLimitMultiplier 6} getActionToFlushValidAction(s: BBC.Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>)
  requires GetActionToFlushValidStackSlots(s, stack, slots)
  decreases 0x1_0000_0000_0000_0000 - |stack|
  ensures ValidAction(s, getActionToFlush(s, stack, slots))
  {
    reveal_getActionToFlush();
    var action := getActionToFlush(s, stack, slots);

    if |stack| as uint64 == 40 {
      return;
    }

    var ref := stack[ |stack| as uint64 - 1];
    var node := s.cache[ref];

    if node.children.None? || |node.buckets| == MaxNumChildren() {
      getActionToSplitValidAction(s, stack, slots, |stack| as uint64 - 1);
      return;
    }

    var (slot, _) := biggestSlot(node.buckets);

    var childref := node.children.value[slot];
    lemmaChildInGraph(s, ref, childref);

    if childref !in s.cache {
      assert childref in s.ephemeralIndirectionTable.graph;
      assert childref in s.ephemeralIndirectionTable.locs;
      assert ValidAction(s, action);
      return;
    }
  
    var child := s.cache[childref];

    var childTotalWeight := WeightBucketList(child.buckets);

    if childTotalWeight + FlushTriggerWeight() <= MaxTotalBucketWeight() {
      assert ValidAction(s, action);
      return;
    } 

    var stack', slots' := getActionToFlushValidActionRec(s, stack, slots, slot, childref);

    getActionToFlushValidAction(s, stack', slots');
  }
}
