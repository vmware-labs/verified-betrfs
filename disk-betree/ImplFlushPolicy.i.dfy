include "ImplFlush.i.dfy"
include "ImplGrow.i.dfy"
include "ImplSplit.i.dfy"
include "ImplLeaf.i.dfy"
include "ImplModelFlushPolicy.i.dfy"

module ImplFlushPolicy {
  import opened Impl
  import opened ImplIO
  import opened ImplCache
  import opened ImplFlush
  import opened ImplGrow
  import opened ImplSplit
  import opened ImplLeaf
  import ImplModelFlushPolicy
  import opened ImplState

  import opened Sequences

  import opened Bounds
  import opened NativeTypes
  import opened BucketsLib
  import opened BucketWeights
  import KMTable

  method biggestSlot(buckets: seq<KMTable.KMTable>) returns (res : (uint64, uint64))
  requires forall i | 0 <= i < |buckets| :: KMTable.WF(buckets[i])
  requires ImplModelFlushPolicy.biggestSlot.requires(buckets)
  ensures res == ImplModelFlushPolicy.biggestSlot(buckets)
  {
    WeightBucketLeBucketList(KMTable.ISeq(buckets), 0);
    KMTable.kmtableWeightEq(buckets[0]);
    var j := 1;
    var bestIdx := 0;
    var bestWeight := KMTable.computeWeightKMTable(buckets[0]);
    while j < |buckets| as uint64
    invariant ImplModelFlushPolicy.biggestSlotIterate.requires(buckets, j, bestIdx, bestWeight)
    invariant ImplModelFlushPolicy.biggestSlotIterate(buckets, j, bestIdx, bestWeight) == ImplModelFlushPolicy.biggestSlot(buckets)
    {
      KMTable.kmtableWeightEq(buckets[j]);
      WeightBucketLeBucketList(KMTable.ISeq(buckets), j as int);
      var w := KMTable.computeWeightKMTable(buckets[j]);
      if w > bestWeight {
        bestIdx := j;
        bestWeight := w;
      }
      j := j + 1;
    }

    return (bestIdx, bestWeight);
  }

  method getActionToSplit(k: ImplConstants, s: ImplVariables, stack: seq<BT.G.Reference>, slots: seq<uint64>, i: uint64) returns (action : ImplModelFlushPolicy.Action)
  requires 0 <= i as int < |stack|
  requires Inv(k, s)
  requires ImplModelFlushPolicy.ValidStackSlots(Ic(k), IVars(s), stack, slots)
  ensures action == ImplModelFlushPolicy.getActionToSplit(Ic(k), IVars(s), stack, slots, i)
  {
    ImplModelFlushPolicy.reveal_getActionToSplit();

    if i == 0 {
      // Can't split root until we grow it.
      action := ImplModelFlushPolicy.ActionGrow;
    } else {
      if |s.cache[stack[i-1]].children.value| as uint64 < MaxNumChildren() as uint64 {
        if |s.cache[stack[i]].buckets| as uint64 == 1 {
          action := ImplModelFlushPolicy.ActionRepivot(stack[i]);
        } else {
          action := ImplModelFlushPolicy.ActionSplit(stack[i-1], slots[i-1]);
        }
      } else {
        action := getActionToSplit(k, s, stack, slots, i-1);
      }
    }
  }

  method getActionToFlush(k: ImplConstants, s: ImplVariables, stack: seq<BT.G.Reference>, slots: seq<uint64>) returns (action : ImplModelFlushPolicy.Action)
  requires |stack| <= 40
  requires ImplModelFlushPolicy.ValidStackSlots(Ic(k), IVars(s), stack, slots)
  requires Inv(k, s)
  decreases 0x1_0000_0000_0000_0000 - |stack|
  ensures action == ImplModelFlushPolicy.getActionToFlush(Ic(k), IVars(s), stack, slots)
  {
    if |stack| as uint64 == 40 {
      action := ImplModelFlushPolicy.ActionFail;
    } else {
      var ref := stack[|stack| as uint64 - 1];
      var node := s.cache[ref];
      if node.children.None? || |node.buckets| == MaxNumChildren() {
        action := getActionToSplit(k, s, stack, slots, |stack| as uint64 - 1);
      } else {
        var bs := biggestSlot(node.buckets);
        var (slot, slotWeight) := bs;
        // TODO partial flushes
        // with partial flushes, we can ensure that the node will either have a lot of children
        // or will have a flushable node.
        // As it stands, we'll always just flush.

        //if slotWeight >= FlushTriggerWeight() as uint64 then (
          var childref := node.children.value[slot];
          if childref in s.cache {
            var child := s.cache[childref];

            KMTable.kmtableSeqWeightEq(child.buckets);
            var childTotalWeight: uint64 := KMTable.computeWeightKMTableSeq(child.buckets);

            var extraRootWeight: uint64;
            if ref == BT.G.Root() {
              extraRootWeight := WeightBucket(s.rootBucket);
            } else {
              extraRootWeight := 0;
            }

            if slotWeight + childTotalWeight + extraRootWeight <= MaxTotalBucketWeight() as uint64 {
              action := ImplModelFlushPolicy.ActionFlush(ref, slot);
            } else {
              action := ImplModelFlushPolicy.getActionToFlush(k, s, stack + [childref], slots + [slot]);
            }
          } else {
            action := ImplModelFlushPolicy.getActionToPageIn(s.cache, childref);
          }
        //) else (
        //  getActionToSplit(k, s, stack, slots, |stack| as uint64 - 1)
        //)
      }
    }
  }

  /*
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
        //if slotWeight >= FlushTriggerWeight() as uint64 || |node.children.value| as uint64 < 2 {
          var childref := node.children.value[slot];
          lemmaChildInGraph(k, s, ref, childref);
          if childref in s.cache {
            var child := s.cache[childref];
            var childTotalWeight: uint64 := WeightBucketList(KMTable.ISeq(child.buckets)) as uint64;
            var extraRootWeight: uint64 := if ref == BT.G.Root() then WeightBucket(s.rootBucket) as uint64 else 0;
            if slotWeight + childTotalWeight + extraRootWeight <= MaxTotalBucketWeight() as uint64 {
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
        //} else {
        //  getActionToSplitValidAction(k, s, stack, slots, |stack| as uint64 - 1);
        //}
      }
    }
  }

  lemma getActionToFlushWeightBounds(k: Constants, s: Variables, stack: seq<BT.G.Reference>, slots: seq<uint64>)
  requires |stack| <= 40
  requires ValidStackSlots(k, s, stack, slots)
  requires Inv(k, s)
  requires forall j | 0 <= j < |stack| :: stack[j] in s.ephemeralIndirectionTable
  requires forall j | 0 <= j < |stack| - 1 :: s.cache[stack[j]].children.value[slots[j]] == stack[j+1]
  requires forall j | 1 <= j < |stack| :: stack[j] != BT.G.Root()
  decreases 0x1_0000_0000_0000_0000 - |stack|
  ensures var action := getActionToFlush(k, s, stack, slots);
      && ValidAction(k, s, action)
      && (action.ActionFlush? ==>
        && var parent := s.cache[action.parentref];
        && var child := s.cache[parent.children.value[action.slot]];
        (if action.parentref == BT.G.Root() then WeightBucket(s.rootBucket) else 0) +
        WeightBucketList(KMTable.ISeq(child.buckets)) +
        WeightBucket(KMTable.I(parent.buckets[action.slot])) <= MaxTotalBucketWeight()
      )
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
        //if slotWeight >= FlushTriggerWeight() as uint64 || |node.children.value| as uint64 < 2 {
          var childref := node.children.value[slot];
          lemmaChildInGraph(k, s, ref, childref);
          if childref in s.cache {
            var child := s.cache[childref];
            var childTotalWeight: uint64 := WeightBucketList(KMTable.ISeq(child.buckets)) as uint64;
            var extraRootWeight: uint64 := if ref == BT.G.Root() then WeightBucket(s.rootBucket) as uint64 else 0;
            if slotWeight + childTotalWeight + extraRootWeight <= MaxTotalBucketWeight() as uint64 {

              assert extraRootWeight as int == (if action.parentref == BT.G.Root() then WeightBucket(s.rootBucket) else 0);
              assert childTotalWeight as int == WeightBucketList(KMTable.ISeq(child.buckets));
              assert slotWeight as int == WeightBucket(KMTable.I(node.buckets[action.slot]));

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
        //} else {
        //  getActionToSplitValidAction(k, s, stack, slots, |stack| as uint64 - 1);
        //}
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
        getActionToFlushWeightBounds(k, s, [BT.G.Root()], []);
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
  */
}
