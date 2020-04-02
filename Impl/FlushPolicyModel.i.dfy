include "FlushModel.i.dfy"
include "GrowModel.i.dfy"
include "SplitModel.i.dfy"
include "LeafModel.i.dfy"
include "EvictModel.i.dfy"
include "../PivotBetree/Bounds.i.dfy"

module FlushPolicyModel {
  import opened StateModel
  import opened IOModel
  import opened BookkeepingModel
  import opened FlushModel
  import opened GrowModel
  import opened SplitModel
  import opened LeafModel
  import opened EvictModel
  import opened InterpretationDiskOps
  import opened DiskOpModel

  import opened Sequences

  import opened Bounds
  import opened NativeTypes
  import opened BucketsLib
  import opened BucketWeights

  datatype Action =
    | ActionPageIn(ref: BT.G.Reference)
    | ActionSplit(parentref: BT.G.Reference, slot: uint64)
    | ActionFlush(parentref: BT.G.Reference, slot: uint64)
    | ActionRepivot(ref: BT.G.Reference)
    | ActionGrow
    | ActionEvict
    | ActionFail

  function biggestSlotIterate(buckets: seq<Bucket>, j: uint64, bestIdx: uint64, bestWeight: uint64) : (res : (uint64, uint64))
  requires 0 <= bestIdx as int < |buckets|
  requires 0 <= bestWeight as int <= MaxTotalBucketWeight()
  requires 1 <= j as int <= |buckets| <= MaxNumChildren()
  requires forall i | 0 <= i < |buckets| :: WFBucket(buckets[i])
  requires WeightBucketList(buckets) <= MaxTotalBucketWeight()
  requires WeightBucket(buckets[bestIdx]) == bestWeight as int
  ensures 0 <= res.0 as int < |buckets|
  ensures 0 <= res.1 as int <= MaxTotalBucketWeight()
  ensures WeightBucket(buckets[res.0]) == res.1 as int
  decreases |buckets| - j as int
  {
    if j == |buckets| as uint64 then (
      (bestIdx, bestWeight)
    ) else (
      WeightBucketLeBucketList(buckets, j as int);

      var w := WeightBucket(buckets[j]) as uint64;
      if w > bestWeight then (
        biggestSlotIterate(buckets, j+1, j, w)
      ) else (
        biggestSlotIterate(buckets, j+1, bestIdx, bestWeight)
      )
    )
  }

  function biggestSlot(buckets: seq<Bucket>) : (res : (uint64, uint64))
  requires |buckets| > 0
  requires |buckets| <= MaxNumChildren()
  requires forall i | 0 <= i < |buckets| :: WFBucket(buckets[i])
  requires WeightBucketList(buckets) <= MaxTotalBucketWeight()
  ensures 0 <= res.0 as int < |buckets|
  ensures 0 <= res.1 as int <= MaxTotalBucketWeight()
  ensures WeightBucket(buckets[res.0]) == res.1 as int
  {
    WeightBucketLeBucketList(buckets, 0);
    biggestSlotIterate(buckets, 1, 0, WeightBucket(buckets[0]) as uint64)
  }

  predicate ValidStackSlots(k: Constants, s: BCVariables, stack: seq<BT.G.Reference>, slots: seq<uint64>)
  {
    && |stack| == |slots| + 1
    && s.Ready?
    && (forall j | 0 <= j < |stack| :: stack[j] in s.cache)
    && (forall j | 0 <= j < |stack| - 1 :: s.cache[stack[j]].children.Some?)
    && (forall j | 0 <= j < |stack| - 1 :: slots[j] as int < |s.cache[stack[j]].children.value| <= MaxNumChildren())
    && (forall j | 0 <= j < |stack| - 1 :: slots[j] as int < |s.cache[stack[j]].children.value| <= MaxNumChildren())
  }

  predicate ValidAction(k: Constants, s: BCVariables, action: Action)
  {
    && s.Ready?
    && (action.ActionPageIn? ==> (
      && action.ref in s.ephemeralIndirectionTable.graph
      && action.ref !in s.cache
      && action.ref in s.ephemeralIndirectionTable.locs
      && TotalCacheSize(s) <= MaxCacheSize() - 1
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
      && TotalCacheSize(s) <= MaxCacheSize() - 2
    ))
    && (action.ActionFlush? ==> (
      && TotalCacheSize(s) <= MaxCacheSize() - 1
    ))
    && (action.ActionGrow? ==> (
      && TotalCacheSize(s) <= MaxCacheSize() - 1
    ))
    && (action.ActionRepivot? ==> (
      && action.ref in s.ephemeralIndirectionTable.graph
      && action.ref in s.cache
      && s.cache[action.ref].children.None?
      && |s.cache[action.ref].buckets| == 1
    ))
  }

  function {:opaque} getActionToSplit(k: Constants, s: BCVariables, stack: seq<BT.G.Reference>, slots: seq<uint64>, i: uint64) : (action : Action)
  requires 0 <= i as int < |stack|
  requires WFBCVars(s)
  requires ValidStackSlots(k, s, stack, slots)
  {
    if i == 0 then
      // Can't split root until we grow it.
      if TotalCacheSize(s) <= MaxCacheSize() - 1 then (
        ActionGrow
      ) else (
        ActionEvict
      )
    else (
      if |s.cache[stack[i-1]].children.value| as uint64 < MaxNumChildren() as uint64 then (
        if |s.cache[stack[i]].buckets| as uint64 == 1 then (
          ActionRepivot(stack[i])
        ) else (
          if TotalCacheSize(s) <= MaxCacheSize() - 2 then (
            ActionSplit(stack[i-1], slots[i-1])
          ) else (
            ActionEvict
          )
        )
      ) else (
        getActionToSplit(k, s, stack, slots, i-1)
      )
    )
  }

  function {:opaque} getActionToFlush(k: Constants, s: BCVariables, stack: seq<BT.G.Reference>, slots: seq<uint64>) : (BCVariables, Action)
  requires |stack| <= 40
  requires ValidStackSlots(k, s, stack, slots)
  requires WFBCVars(s)
  decreases 0x1_0000_0000_0000_0000 - |stack|
  {
    if |stack| as uint64 == 40 then (
      (s, ActionFail)
    ) else (
      var ref := stack[|stack| as uint64 - 1];
      var node := s.cache[ref];
      if node.children.None? || |node.buckets| == MaxNumChildren() then (
        (s, getActionToSplit(k, s, stack, slots, |stack| as uint64 - 1))
      ) else (
        var (slot, slotWeight) := biggestSlot(node.buckets);
        // TODO:
        //if slotWeight >= FlushTriggerWeight() as uint64 then (
        if |node.buckets| < 8 then (
          var childref := node.children.value[slot];
          if childref in s.cache then (
            var child := s.cache[childref];
            var s1 := s.(lru := LruModel.Use(s.lru, childref));
            LruModel.LruUse(s.lru, childref);
            assert IBlockCache(s) == IBlockCache(s1);

            var childTotalWeight: uint64 := WeightBucketList(child.buckets) as uint64;
            if childTotalWeight + FlushTriggerWeight() as uint64 <= MaxTotalBucketWeight() as uint64 then (
              // If there's room for FlushTriggerWeight() worth of stuff, then
              // we flush. We flush as much as we can (which will end up being at least
              // FlushTriggerWeight - max key weight - max message weight).
              if TotalCacheSize(s1) <= MaxCacheSize() - 1 then (
                (s1, ActionFlush(ref, slot))
              ) else (
                (s1, ActionEvict)
              )
            ) else (
              getActionToFlush(k, s1, stack + [childref], slots + [slot])
            )
          ) else (
            if TotalCacheSize(s) <= MaxCacheSize() - 1 then (
              (s, ActionPageIn(childref))
            ) else (
              (s, ActionEvict)
            )
          )
        ) else (
          (s, getActionToSplit(k, s, stack, slots, |stack| as uint64 - 1))
        )
      )
    )
  }

  lemma getActionToSplitValidAction(k: Constants, s: BCVariables, stack: seq<BT.G.Reference>, slots: seq<uint64>, i: uint64)
  requires 0 <= i as int < |stack|
  requires BCInv(k, s)
  requires ValidStackSlots(k, s, stack, slots)
  requires forall j | 0 <= j < |stack| :: stack[j] in s.ephemeralIndirectionTable.graph
  requires forall j | 0 <= j < |stack| - 1 :: s.cache[stack[j]].children.value[slots[j]] == stack[j+1]
  requires s.cache[stack[|stack| - 1]].children.Some? ==> |s.cache[stack[|stack| - 1]].buckets| >= 2
  requires i as int < |stack| - 1 ==> |s.cache[stack[i]].buckets| >= MaxNumChildren()
  ensures ValidAction(k, s, getActionToSplit(k, s, stack, slots, i))
  ensures var action := getActionToSplit(k, s, stack, slots, i);
      action.ActionGrow? || action.ActionRepivot? || action.ActionSplit? || action.ActionEvict?
  {
    reveal_getActionToSplit();
    var action := getActionToSplit(k, s, stack, slots, i);

    if i == 0 {
      //assert ValidAction(k, s, action);
    } else {
      if |s.cache[stack[i-1]].children.value| as uint64 < MaxNumChildren() as uint64 {
        /*if |s.cache[stack[i]].buckets| as uint64 == 1 {
          assert ValidAction(k, s, action);
        } else {
          assert ValidAction(k, s, action);
        }*/
      } else {
        getActionToSplitValidAction(k, s, stack, slots, i-1);
      }
    }
  }

  lemma getActionToFlushValidAction(k: Constants, s: BCVariables, stack: seq<BT.G.Reference>, slots: seq<uint64>)
  requires |stack| <= 40
  requires ValidStackSlots(k, s, stack, slots)
  requires BCInv(k, s)
  requires forall j | 0 <= j < |stack| :: stack[j] in s.ephemeralIndirectionTable.graph
  requires forall j | 0 <= j < |stack| - 1 :: s.cache[stack[j]].children.value[slots[j]] == stack[j+1]
  decreases 0x1_0000_0000_0000_0000 - |stack|
  ensures var (s', action) := getActionToFlush(k, s, stack, slots);
    && WFBCVars(s')
    && IBlockCache(s) == IBlockCache(s')
    && ValidAction(k, s', action)
  {
    reveal_getActionToFlush();
    var action := getActionToFlush(k, s, stack, slots).1;

    if |stack| as uint64 == 40 {
    } else {
      var ref := stack[|stack| as uint64 - 1];
      var node := s.cache[ref];
      if node.children.None? || |node.buckets| == MaxNumChildren() {
        getActionToSplitValidAction(k, s, stack, slots, |stack| as uint64 - 1);
      } else {
        var (slot, slotWeight) := biggestSlot(node.buckets);
        //if slotWeight >= FlushTriggerWeight() as uint64 {
        if |node.buckets| < 8 {
          var childref := node.children.value[slot];
          lemmaChildInGraph(k, s, ref, childref);
          if childref in s.cache {
            var child := s.cache[childref];
            var s1 := s.(lru := LruModel.Use(s.lru, childref));
            LruModel.LruUse(s.lru, childref);
            var childTotalWeight: uint64 := WeightBucketList(child.buckets) as uint64;
            if childTotalWeight + FlushTriggerWeight() as uint64 <= MaxTotalBucketWeight() as uint64 {
              assert ValidAction(k, s1, action);
            } else {
              getActionToFlushValidAction(k, s1, stack + [childref], slots + [slot]);
            }
          } else {
            assert childref !in IBlockCache(s).cache;
            assert childref in IIndirectionTable(s.ephemeralIndirectionTable).graph;
            assert childref in IIndirectionTable(s.ephemeralIndirectionTable).locs;
            assert ValidAction(k, s, action);
          }
        } else {
          getActionToSplitValidAction(k, s, stack, slots, |stack| as uint64 - 1);
        }
      }
    }
  }

  predicate {:opaque} runFlushPolicy(k: Constants, s: BCVariables, io: IO,
      s': BCVariables, io': IO)
  requires BCInv(k, s)
  requires io.IOInit?
  requires s.Ready?
  requires |s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 3
  requires BT.G.Root() in s.cache
  {
    var s0 := s.(lru := LruModel.Use(s.lru, BT.G.Root()));
    LruModel.LruUse(s.lru, BT.G.Root());
    assert IBlockCache(s0) == IBlockCache(s);

    var (s1, action) := getActionToFlush(k, s0, [BT.G.Root()], []);
    getActionToFlushValidAction(k, s0, [BT.G.Root()], []);

    match action {
      case ActionPageIn(ref) => (
        (s', io') == PageInNodeReq(k, s1, io, ref)
      )
      case ActionSplit(parentref, slot) => (
        && s' == doSplit(k, s1, parentref, s1.cache[parentref].children.value[slot], slot as int)
        && io' == io
      )
      case ActionRepivot(ref) => (
        && s' == repivotLeaf(k, s1, ref, s1.cache[ref])
        && io' == io
      )
      case ActionFlush(parentref, slot) => (
        && s' == flush(k, s1, parentref, slot as int, 
            s1.cache[parentref].children.value[slot],
            s1.cache[s1.cache[parentref].children.value[slot]])
        && io' == io
      )
      case ActionGrow => (
        && s' == grow(k, s1)
        && io' == io
      )
      case ActionEvict => (
        EvictOrDealloc(k, s1, io, s', io')
      )
      case ActionFail => (
        && s' == s1
        && io' == io
      )
    }
  }

  lemma runFlushPolicyCorrect(k: Constants, s: BCVariables, io: IO, s': BCVariables, io': IO)
  requires BCInv(k, s)
  requires io.IOInit?
  requires s.Ready?
  requires BT.G.Root() in s.cache
  requires |s.ephemeralIndirectionTable.graph| <= IndirectionTableModel.MaxSize() - 3
  requires runFlushPolicy(k, s, io, s', io')
  ensures WFBCVars(s')
  ensures ValidDiskOp(diskOp(io'))
  ensures IDiskOp(diskOp(io')).jdop.NoDiskOp?
  ensures betree_next_dop(k, IBlockCache(s), IBlockCache(s'),
      IDiskOp(diskOp(io')).bdop)
  {
    var s0 := s.(lru := LruModel.Use(s.lru, BT.G.Root()));
    LruModel.LruUse(s.lru, BT.G.Root());
    assert IBlockCache(s0) == IBlockCache(s);
    var (s1, action) := getActionToFlush(k, s0, [BT.G.Root()], []);
    getActionToFlushValidAction(k, s0, [BT.G.Root()], []);

    reveal_runFlushPolicy();

    match action {
      case ActionPageIn(ref) => {
        PageInNodeReqCorrect(k, s1, io, ref);
      }
      case ActionSplit(parentref, slot) => {
        doSplitCorrect(k, s1, parentref, s1.cache[parentref].children.value[slot], slot as int);
      }
      case ActionRepivot(ref) => {
        repivotLeafCorrect(k, s1, ref, s1.cache[ref]);
      }
      case ActionFlush(parentref, slot) => {
        flushCorrect(k, s1, parentref, slot as int, 
            s1.cache[parentref].children.value[slot],
            s1.cache[s1.cache[parentref].children.value[slot]]);
      }
      case ActionGrow => {
        growCorrect(k, s1);
      }
      case ActionEvict => {
        EvictOrDeallocCorrect(k, s1, io, s', io');
      }
      case ActionFail => {
        assert noop(k, IBlockCache(s), IBlockCache(s1));
      }
    }
  }
}
