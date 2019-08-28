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
  requires Inv(k, s)
  requires ImplModelFlushPolicy.ValidStackSlots(Ic(k), IVars(s), stack, slots)
  decreases 0x1_0000_0000_0000_0000 - |stack|
  ensures action == ImplModelFlushPolicy.getActionToFlush(Ic(k), IVars(s), stack, slots)
  {
    ImplModelFlushPolicy.reveal_getActionToFlush();

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

            var extraRootWeight: uint64 := if ref == BT.G.Root() then s.rootBucketWeightBound else 0;

            if slotWeight + childTotalWeight + extraRootWeight <= MaxTotalBucketWeight() as uint64 {
              action := ImplModelFlushPolicy.ActionFlush(ref, slot);
            } else {
              action := getActionToFlush(k, s, stack + [childref], slots + [slot]);
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

  method runFlushPolicy(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s' : Variables)
  requires Inv(k, s)
  requires io.initialized()
  requires s.Ready?
  requires BT.G.Root() in s.cache
  modifies io
  modifies s.ephemeralIndirectionTable.Repr
  ensures WVars(s')
  ensures (IVars(s'), IIO(io)) == ImplModelFlushPolicy.runFlushPolicy(Ic(k), old(IVars(s)), old(IIO(io)))
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  {
    ImplModelFlushPolicy.reveal_runFlushPolicy();

    var action := getActionToFlush(k, s, [BT.G.Root()], []);
    ImplModelFlushPolicy.getActionToFlushValidAction(Ic(k), IVars(s), [BT.G.Root()], []);

    match action {
      case ActionPageIn(ref) => {
        s' := PageInReq(k, s, io, ref);
      }
      case ActionSplit(parentref, slot) => {
        s' := doSplit(k, s, parentref, s.cache[parentref].children.value[slot], slot as int);
      }
      case ActionRepivot(ref) => {
        s' := repivotLeaf(k, s, ref, s.cache[ref]);
      }
      case ActionFlush(parentref, slot) => {
        s' := flush(k, s, parentref, slot as int, 
            s.cache[parentref].children.value[slot],
            s.cache[s.cache[parentref].children.value[slot]]);
      }
      case ActionGrow => {
        s' := grow(k, s);
      }
      case ActionEvict => {
        s' := s;
      }
      case ActionFail => {
        s' := s;
      }
    }
  }
}
