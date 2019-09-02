include "ImplFlush.i.dfy"
include "ImplGrow.i.dfy"
include "ImplSplit.i.dfy"
include "ImplLeaf.i.dfy"
include "ImplEvict.i.dfy"
include "ImplModelFlushPolicy.i.dfy"

module ImplFlushPolicy {
  import opened Impl
  import opened ImplIO
  import opened ImplCache
  import opened ImplFlush
  import opened ImplGrow
  import opened ImplSplit
  import opened ImplLeaf
  import opened ImplEvict
  import ImplModelFlushPolicy
  import opened ImplState

  import opened Sequences

  import opened Bounds
  import opened NativeTypes
  import opened BucketsLib
  import opened BucketWeights
  import KMTable

  method biggestSlot(buckets: seq<KMTable.KMT>) returns (res : (uint64, uint64))
  requires forall i | 0 <= i < |buckets| :: KMTable.WF(buckets[i])
  requires ImplModelFlushPolicy.biggestSlot.requires(buckets)
  ensures res == ImplModelFlushPolicy.biggestSlot(buckets)
  {
    WeightBucketLeBucketList(KMTable.ISeq(buckets), 0);
    var j := 1;
    var bestIdx := 0;
    var bestWeight := KMTable.computeWeightKMT(buckets[0]);
    while j < |buckets| as uint64
    invariant ImplModelFlushPolicy.biggestSlotIterate.requires(buckets, j, bestIdx, bestWeight)
    invariant ImplModelFlushPolicy.biggestSlotIterate(buckets, j, bestIdx, bestWeight) == ImplModelFlushPolicy.biggestSlot(buckets)
    {
      WeightBucketLeBucketList(KMTable.ISeq(buckets), j as int);
      var w := KMTable.computeWeightKMT(buckets[j]);
      if w > bestWeight {
        bestIdx := j;
        bestWeight := w;
      }
      j := j + 1;
    }

    return (bestIdx, bestWeight);
  }

  function method TotalCacheSize(s: ImplVariables) : (res : int)
  requires s.Ready?
  {
    |s.cache| + |s.outstandingBlockReads|
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
      if TotalCacheSize(s) <= MaxCacheSize() - 1 {
        action := ImplModelFlushPolicy.ActionGrow;
      } else {
        action := ImplModelFlushPolicy.ActionEvict;
      }
    } else {
      if |s.cache[stack[i-1]].children.value| as uint64 < MaxNumChildren() as uint64 {
        if |s.cache[stack[i]].buckets| as uint64 == 1 {
          action := ImplModelFlushPolicy.ActionRepivot(stack[i]);
        } else {
          if TotalCacheSize(s) <= MaxCacheSize() - 2 {
            action := ImplModelFlushPolicy.ActionSplit(stack[i-1], slots[i-1]);
          } else {
            action := ImplModelFlushPolicy.ActionEvict;
          }
        }
      } else {
        action := getActionToSplit(k, s, stack, slots, i-1);
      }
    }
  }

  method getActionToFlush(k: ImplConstants, s: ImplVariables, stack: seq<BT.G.Reference>, slots: seq<uint64>) returns (s': ImplVariables, action : ImplModelFlushPolicy.Action)
  requires |stack| <= 40
  requires Inv(k, s)
  requires ImplModelFlushPolicy.ValidStackSlots(Ic(k), IVars(s), stack, slots)
  decreases 0x1_0000_0000_0000_0000 - |stack|
  ensures WVars(s')
  ensures s'.Ready?
  ensures s'.ephemeralIndirectionTable == s.ephemeralIndirectionTable
  ensures s'.frozenIndirectionTable == s.frozenIndirectionTable
  ensures (IVars(s'), action) == ImplModelFlushPolicy.getActionToFlush(Ic(k), old(IVars(s)), stack, slots)
  {
    ImplModelFlushPolicy.reveal_getActionToFlush();

    if |stack| as uint64 == 40 {
      action := ImplModelFlushPolicy.ActionFail;
      s' := s;
    } else {
      var ref := stack[|stack| as uint64 - 1];
      var node := s.cache[ref];
      if node.children.None? || |node.buckets| == MaxNumChildren() {
        action := getActionToSplit(k, s, stack, slots, |stack| as uint64 - 1);
        s' := s;
      } else {
        var bs := biggestSlot(node.buckets);
        var (slot, slotWeight) := bs;
        //if slotWeight >= FlushTriggerWeight() as uint64 then (
        if |node.buckets| < 8 {
          var childref := node.children.value[slot];
          if childref in s.cache {
            var child := s.cache[childref];

            var s1 := s.(lru := LruModel.Use(s.lru, childref));
            LruModel.LruUse(s.lru, childref);

            var childTotalWeight: uint64 := KMTable.computeWeightKMTSeq(child.buckets);

            if childTotalWeight + FlushTriggerWeight() as uint64 <= MaxTotalBucketWeight() as uint64 {
              if TotalCacheSize(s1) <= MaxCacheSize() - 1 {
                action := ImplModelFlushPolicy.ActionFlush(ref, slot);
                s' := s1;
              } else {
                action := ImplModelFlushPolicy.ActionEvict;
                s' := s1;
              }
            } else {
              s', action := getActionToFlush(k, s1, stack + [childref], slots + [slot]);
            }
          } else {
            if TotalCacheSize(s) <= MaxCacheSize() - 1 {
              action := ImplModelFlushPolicy.ActionPageIn(childref);
              s' := s;
            } else {
              action := ImplModelFlushPolicy.ActionEvict;
              s' := s;
            }
          }
        } else {
          action := getActionToSplit(k, s, stack, slots, |stack| as uint64 - 1);
          s' := s;
        }
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
  modifies if s.Ready? && s.frozenIndirectionTable.Some? then s.frozenIndirectionTable.value.Repr else {}
  ensures WVars(s')
  ensures ImplModelFlushPolicy.runFlushPolicy(Ic(k), old(IVars(s)), old(IIO(io)), IVars(s'), IIO(io))
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  {
    ImplModelFlushPolicy.reveal_runFlushPolicy();

    var s0 := s.(lru := LruModel.Use(s.lru, BT.G.Root()));
    LruModel.LruUse(s.lru, BT.G.Root());
    assert IM.IVars(IVars(s0)) == IM.IVars(IVars(s));

    var s1, action := getActionToFlush(k, s0, [BT.G.Root()], []);
    ImplModelFlushPolicy.getActionToFlushValidAction(Ic(k), IVars(s0), [BT.G.Root()], []);

    match action {
      case ActionPageIn(ref) => {
        s' := PageInReq(k, s1, io, ref);
      }
      case ActionSplit(parentref, slot) => {
        s' := doSplit(k, s1, parentref, s1.cache[parentref].children.value[slot], slot as int);
      }
      case ActionRepivot(ref) => {
        s' := repivotLeaf(k, s1, ref, s1.cache[ref]);
      }
      case ActionFlush(parentref, slot) => {
        s' := flush(k, s1, parentref, slot as int, 
            s1.cache[parentref].children.value[slot],
            s1.cache[s1.cache[parentref].children.value[slot]]);
      }
      case ActionGrow => {
        s' := grow(k, s1);
      }
      case ActionEvict => {
        s' := EvictOrDealloc(k, s1, io);
      }
      case ActionFail => {
        print "ActionFail\n";
        s' := s1;
      }
    }
  }
}
