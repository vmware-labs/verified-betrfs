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

  function {:opaque} getActionToFlush(s: BBC.Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>) : (BBC.Variables, Action)
  requires |stack| <= 40
  requires ValidStackSlots(s, stack, slots)
  requires BBC.Inv(s)
  decreases 0x1_0000_0000_0000_0000 - |stack|
  {
    if |stack| as uint64 == 40 then (
      (s, ActionFail)
    ) else (
      var ref := stack[|stack| as uint64 - 1];
      var node := s.cache[ref];
      if node.children.None? || |node.buckets| == MaxNumChildren() then (
        (s, getActionToSplit(s, stack, slots, |stack| as uint64 - 1))
      ) else (
        var (slot, slotWeight) := biggestSlot(node.buckets);
        // TODO:
        //if slotWeight >= FlushTriggerWeight() as uint64 then (
        if |node.buckets| < 8 then (
          var childref := node.children.value[slot];
          if childref in s.cache then (
            var child := s.cache[childref];
            var s1 := s;
            // var s1 := s.(lru := LruModel.Use(s.lru, childref));
            // LruModel.LruUse(s.lru, childref);
            // assert IBlockCache(s) == IBlockCache(s1);

            var childTotalWeight: uint64 := WeightBucketList(child.buckets) as uint64;
            if childTotalWeight + FlushTriggerWeight() as uint64 <= MaxTotalBucketWeight() as uint64 then (
              // If there's room for FlushTriggerWeight() worth of stuff, then
              // we flush. We flush as much as we can (which will end up being at least
              // FlushTriggerWeight - max key weight - max message weight).
              if s1.totalCacheSize() <= MaxCacheSize() - 1 then (
                (s1, ActionFlush(ref, slot))
              ) else (
                (s1, ActionEvict)
              )
            ) else (
              getActionToFlush(s1, stack + [childref], slots + [slot])
            )
          ) else (
            if s.totalCacheSize() <= MaxCacheSize() - 1 then (
              (s, ActionPageIn(childref))
            ) else (
              (s, ActionEvict)
            )
          )
        ) else (
          (s, getActionToSplit(s, stack, slots, |stack| as uint64 - 1))
        )
      )
    )
  }

  lemma getActionToSplitValidAction(s: BBC.Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>, i: uint64)
  requires 0 <= i as int < |stack|
  requires BBC.Inv(s)
  requires ValidStackSlots(s, stack, slots)
  requires forall j | 0 <= j < |stack| :: stack[j] in s.ephemeralIndirectionTable.graph
  requires forall j | 0 <= j < |stack| - 1 :: s.cache[stack[j]].children.value[slots[j]] == stack[j+1]
  requires s.cache[stack[|stack| - 1]].children.Some? ==> |s.cache[stack[|stack| - 1]].buckets| >= 2
  requires i as int < |stack| - 1 ==> |s.cache[stack[i]].buckets| >= MaxNumChildren()
  ensures ValidAction(s, getActionToSplit(s, stack, slots, i))
  ensures var action := getActionToSplit(s, stack, slots, i);
      action.ActionGrow? || action.ActionRepivot? || action.ActionSplit? || action.ActionEvict?
  {
    reveal_getActionToSplit();
    var action := getActionToSplit(s, stack, slots, i);

    if i == 0 {
      //assert ValidAction(s, action);
    } else {
      if |s.cache[stack[i-1]].children.value| as uint64 < MaxNumChildren() as uint64 {
        /*if |s.cache[stack[i]].buckets| as uint64 == 1 {
          assert ValidAction(s, action);
        } else {
          assert ValidAction(s, action);
        }*/
      } else {
        getActionToSplitValidAction(s, stack, slots, i-1);
      }
    }
  }

  lemma getActionToFlushValidAction(s: BBC.Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>)
  requires |stack| <= 40
  requires ValidStackSlots(s, stack, slots)
  requires BBC.Inv(s)
  requires forall j | 0 <= j < |stack| :: stack[j] in s.ephemeralIndirectionTable.graph
  requires forall j | 0 <= j < |stack| - 1 :: s.cache[stack[j]].children.value[slots[j]] == stack[j+1]
  decreases 0x1_0000_0000_0000_0000 - |stack|
  ensures var (s', action) := getActionToFlush(s, stack, slots);
    && ValidAction(s', action)
    && s == s'
  {
    reveal_getActionToFlush();
    var action := getActionToFlush(s, stack, slots).1;

    if |stack| as uint64 == 40 {
    } else {
      var ref := stack[|stack| as uint64 - 1];
      var node := s.cache[ref];
      if node.children.None? || |node.buckets| == MaxNumChildren() {
        getActionToSplitValidAction(s, stack, slots, |stack| as uint64 - 1);
      } else {
        var (slot, slotWeight) := biggestSlot(node.buckets);
        //if slotWeight >= FlushTriggerWeight() as uint64 {
        if |node.buckets| < 8 {
          var childref := node.children.value[slot];
          lemmaChildInGraph(s, ref, childref);
          if childref in s.cache {
            var child := s.cache[childref];
            var s1 := s;
            var childTotalWeight: uint64 := WeightBucketList(child.buckets) as uint64;
            if childTotalWeight + FlushTriggerWeight() as uint64 <= MaxTotalBucketWeight() as uint64 {
              assert ValidAction(s1, action);
            } else {
              getActionToFlushValidAction(s1, stack + [childref], slots + [slot]);
            }
          } else {
            assert childref !in s.cache;
            assert childref in s.ephemeralIndirectionTable.graph;
            assert childref in s.ephemeralIndirectionTable.locs;
            assert ValidAction(s, action);
          }
        } else {
          getActionToSplitValidAction(s, stack, slots, |stack| as uint64 - 1);
        }
      }
    }
  }
}
