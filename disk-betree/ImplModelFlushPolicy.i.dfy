include "ImplModelFlush.i.dfy"
include "ImplModelGrow.i.dfy"
include "ImplModelSplit.i.dfy"
include "ImplModelLeaf.i.dfy"
include "Bounds.i.dfy"

module ImplModelFlushPolicy {
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelCache
  import opened ImplModelFlush
  import opened ImplModelGrow
  import opened ImplModelSplit
  import opened ImplModelLeaf

  import opened Sequences

  import opened Bounds
  import opened NativeTypes
  import opened BucketsLib
  import opened BucketWeights
  import KMTable

  datatype Action =
    | ActionPageIn(ref: BT.G.Reference)
    | ActionSplit(parentref: BT.G.Reference, slot: uint64)
    | ActionFlush(parentref: BT.G.Reference, slot: uint64)
    | ActionRepivot(ref: BT.G.Reference)
    | ActionGrow
    | ActionEvict
    | ActionFail

  function biggestSlotIterate(buckets: seq<KMTable.KMT>, j: uint64, bestIdx: uint64, bestWeight: uint64) : (res : (uint64, uint64))
  requires 0 <= bestIdx as int < |buckets|
  requires 0 <= bestWeight as int <= MaxTotalBucketWeight()
  requires 1 <= j as int <= |buckets| <= MaxNumChildren()
  requires forall i | 0 <= i < |buckets| :: |buckets[i].keys| == |buckets[i].values|
  requires WeightBucketList(KMTable.ISeq(buckets)) <= MaxTotalBucketWeight()
  requires WeightBucket(KMTable.I(buckets[bestIdx])) == bestWeight as int
  ensures 0 <= res.0 as int < |buckets|
  ensures 0 <= res.1 as int <= MaxTotalBucketWeight()
  ensures WeightBucket(KMTable.I(buckets[res.0])) == res.1 as int
  decreases |buckets| - j as int
  {
    if j == |buckets| as uint64 then (
      (bestIdx, bestWeight)
    ) else (
      WeightBucketLeBucketList(KMTable.ISeq(buckets), j as int);

      var w := WeightBucket(KMTable.I(buckets[j])) as uint64;
      if w > bestWeight then (
        biggestSlotIterate(buckets, j+1, j, w)
      ) else (
        biggestSlotIterate(buckets, j+1, bestIdx, bestWeight)
      )
    )
  }

  function biggestSlot(buckets: seq<KMTable.KMT>) : (res : (uint64, uint64))
  requires |buckets| > 0
  requires |buckets| <= MaxNumChildren()
  requires forall i | 0 <= i < |buckets| :: |buckets[i].keys| == |buckets[i].values|
  requires WeightBucketList(KMTable.ISeq(buckets)) <= MaxTotalBucketWeight()
  ensures 0 <= res.0 as int < |buckets|
  ensures 0 <= res.1 as int <= MaxTotalBucketWeight()
  ensures WeightBucket(KMTable.I(buckets[res.0])) == res.1 as int
  {
    WeightBucketLeBucketList(KMTable.ISeq(buckets), 0);
    biggestSlotIterate(buckets, 1, 0, WeightBucket(KMTable.I(buckets[0])) as uint64)
  }

  predicate ValidStackSlots(k: Constants, s: Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>)
  {
    && |stack| == |slots| + 1
    && s.Ready?
    && (forall j | 0 <= j < |stack| :: stack[j] in s.cache)
    && (forall j | 0 <= j < |stack| - 1 :: s.cache[stack[j]].children.Some?)
    && (forall j | 0 <= j < |stack| - 1 :: slots[j] as int < |s.cache[stack[j]].children.value| <= MaxNumChildren())
    && (forall j | 0 <= j < |stack| - 1 :: slots[j] as int < |s.cache[stack[j]].children.value| <= MaxNumChildren())
  }

  predicate ValidAction(k: Constants, s: Variables, action: Action)
  {
    && s.Ready?
    && (action.ActionPageIn? ==> (
      && action.ref in s.ephemeralIndirectionTable
      && action.ref !in s.cache
      && s.ephemeralIndirectionTable[action.ref].0.Some?
    ))
    && ((action.ActionSplit? || action.ActionFlush?) ==> (
      && action.parentref in s.ephemeralIndirectionTable
      && action.parentref in s.cache
      && s.cache[action.parentref].children.Some?
      && 0 <= action.slot as int < |s.cache[action.parentref].children.value|
      && s.cache[action.parentref].children.value[action.slot] in s.cache
      && s.cache[action.parentref].children.value[action.slot] in s.ephemeralIndirectionTable
    ))
    && (action.ActionSplit? ==> (
      && |s.cache[s.cache[action.parentref].children.value[action.slot]].buckets| >= 2
      && |s.cache[action.parentref].buckets| <= MaxNumChildren() - 1
    ))
    && (action.ActionRepivot? ==> (
      && action.ref != BT.G.Root()
      && action.ref in s.ephemeralIndirectionTable
      && action.ref in s.cache
      && s.cache[action.ref].children.None?
    ))
  }

  function method getActionToPageIn(cache: map<BT.G.Reference, Node>, ref: BT.G.Reference) : Action
  {
    // TODO eviction
    /*
    if |cache| >= MaxCacheSize() then
      ActionEvict
    else*/
      ActionPageIn(ref)
  }

  function {:opaque} getActionToSplit(k: Constants, s: Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>, i: uint64) : (action : Action)
  requires 0 <= i as int < |stack|
  requires WFVars(s)
  requires ValidStackSlots(k, s, stack, slots)
  {
    if i == 0 then
      // Can't split root until we grow it.
      ActionGrow
    else (
      if |s.cache[stack[i-1]].children.value| as uint64 < MaxNumChildren() as uint64 then (
        if |s.cache[stack[i]].buckets| as uint64 == 1 then (
          ActionRepivot(stack[i])
        ) else (
          ActionSplit(stack[i-1], slots[i-1])
        )
      ) else (
        getActionToSplit(k, s, stack, slots, i-1)
      )
    )
  }

  function {:opaque} getActionToFlush(k: Constants, s: Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>) : (action : Action)
  requires |stack| <= 40
  requires ValidStackSlots(k, s, stack, slots)
  requires WFVars(s)
  decreases 0x1_0000_0000_0000_0000 - |stack|
  {
    if |stack| as uint64 == 40 then (
      ActionFail
    ) else (
      var ref := stack[|stack| as uint64 - 1];
      var node := s.cache[ref];
      if node.children.None? || |node.buckets| == MaxNumChildren() then (
        getActionToSplit(k, s, stack, slots, |stack| as uint64 - 1)
      ) else (
        // TODO:
        var (slot, slotWeight) := biggestSlot(node.buckets);
        //if slotWeight >= FlushTriggerWeight() as uint64 then (
        if |node.buckets| < 8 then (
          var childref := node.children.value[slot];
          if childref in s.cache then (
            var child := s.cache[childref];
            var childTotalWeight: uint64 := WeightBucketList(KMTable.ISeq(child.buckets)) as uint64;
            if childTotalWeight + FlushTriggerWeight() as uint64 <= MaxTotalBucketWeight() as uint64 then (
              // If there's room for FlushTriggerWeight() worth of stuff, then
              // we flush. We flush as much as we can (which will end up being at least
              // FlushTriggerWeight - max key weight - max message weight).
              ActionFlush(ref, slot)
            ) else (
              getActionToFlush(k, s, stack + [childref], slots + [slot])
            )
          ) else (
            getActionToPageIn(s.cache, childref)
          )
        ) else (
          getActionToSplit(k, s, stack, slots, |stack| as uint64 - 1)
        )
      )
    )
  }

  lemma getActionToSplitValidAction(k: Constants, s: Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>, i: uint64)
  requires 0 <= i as int < |stack|
  requires Inv(k, s)
  requires ValidStackSlots(k, s, stack, slots)
  requires forall j | 0 <= j < |stack| :: stack[j] in s.ephemeralIndirectionTable
  requires forall j | 0 <= j < |stack| - 1 :: s.cache[stack[j]].children.value[slots[j]] == stack[j+1]
  requires forall j | 1 <= j < |stack| :: stack[j] != BT.G.Root()
  requires s.cache[stack[|stack| - 1]].children.Some? ==> |s.cache[stack[|stack| - 1]].buckets| >= 2
  requires i as int < |stack| - 1 ==> |s.cache[stack[i]].buckets| >= MaxNumChildren()
  ensures ValidAction(k, s, getActionToSplit(k, s, stack, slots, i))
  ensures var action := getActionToSplit(k, s, stack, slots, i);
      action.ActionGrow? || action.ActionRepivot? || action.ActionSplit?
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

  lemma getActionToFlushValidAction(k: Constants, s: Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>)
  requires |stack| <= 40
  requires ValidStackSlots(k, s, stack, slots)
  requires Inv(k, s)
  requires forall j | 0 <= j < |stack| :: stack[j] in s.ephemeralIndirectionTable
  requires forall j | 0 <= j < |stack| - 1 :: s.cache[stack[j]].children.value[slots[j]] == stack[j+1]
  requires forall j | 1 <= j < |stack| :: stack[j] != BT.G.Root()
  decreases 0x1_0000_0000_0000_0000 - |stack|
  ensures ValidAction(k, s, getActionToFlush(k, s, stack, slots))
  {
    reveal_getActionToFlush();
    var action := getActionToFlush(k, s, stack, slots);

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
            var childTotalWeight: uint64 := WeightBucketList(KMTable.ISeq(child.buckets)) as uint64;
            if childTotalWeight + FlushTriggerWeight() as uint64 <= MaxTotalBucketWeight() as uint64 {
              assert ValidAction(k, s, action);
            } else {
              assume childref != BT.G.Root(); // TODO we need a way to show this
              getActionToFlushValidAction(k, s, stack + [childref], slots + [slot]);
            }
          } else {
            assert childref !in IVars(s).cache;
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

  function {:opaque} runFlushPolicy(k: Constants, s: Variables, io: IO)
  : (Variables, IO)
  requires Inv(k, s)
  requires io.IOInit?
  requires s.Ready?
  requires BT.G.Root() in s.cache
  {
    var action := getActionToFlush(k, s, [BT.G.Root()], []);
    getActionToFlushValidAction(k, s, [BT.G.Root()], []);

    match action {
      case ActionPageIn(ref) => (
        PageInReq(k, s, io, ref)
      )
      case ActionSplit(parentref, slot) => (
        var s' := doSplit(k, s, parentref, s.cache[parentref].children.value[slot], slot as int);
        (s', io)
      )
      case ActionRepivot(ref) => (
        var s' := repivotLeaf(k, s, ref, s.cache[ref]);
        (s', io)
      )
      case ActionFlush(parentref, slot) => (
        var s' := flush(k, s, parentref, slot as int, 
            s.cache[parentref].children.value[slot],
            s.cache[s.cache[parentref].children.value[slot]]);
        (s', io)
      )
      case ActionGrow => (
        var s' := grow(k, s);
        (s', io)
      )
      case ActionEvict => (
        (s, io) // TODO
      )
      case ActionFail => (
        (s, io)
      )
    }
  }

  lemma runFlushPolicyCorrect(k: Constants, s: Variables, io: IO)
  requires Inv(k, s)
  requires io.IOInit?
  requires s.Ready?
  requires BT.G.Root() in s.cache
  ensures var (s', io') := runFlushPolicy(k, s, io);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    var action := getActionToFlush(k, s, [BT.G.Root()], []);
    getActionToFlushValidAction(k, s, [BT.G.Root()], []);

    reveal_runFlushPolicy();

    match action {
      case ActionPageIn(ref) => {
        PageInReqCorrect(k, s, io, ref);
      }
      case ActionSplit(parentref, slot) => {
        doSplitCorrect(k, s, parentref, s.cache[parentref].children.value[slot], slot as int);
      }
      case ActionRepivot(ref) => {
        repivotLeafCorrect(k, s, ref, s.cache[ref]);
      }
      case ActionFlush(parentref, slot) => {
        flushCorrect(k, s, parentref, slot as int, 
            s.cache[parentref].children.value[slot],
            s.cache[s.cache[parentref].children.value[slot]]);
      }
      case ActionGrow => {
        growCorrect(k, s);
      }
      case ActionEvict => {
        assert noop(k, IVars(s), IVars(s));
      }
      case ActionFail => {
        assert noop(k, IVars(s), IVars(s));
      }
    }
  }
}
