include "FlushImpl.i.dfy"
include "GrowImpl.i.dfy"
include "SplitImpl.i.dfy"
include "LeafImpl.i.dfy"
include "EvictImpl.i.dfy"
include "FlushPolicyModel.i.dfy"

module FlushPolicyImpl {
  import opened IOImpl
  import opened BookkeepingImpl
  import opened FlushImpl
  import opened GrowImpl
  import opened SplitImpl
  import opened LeafImpl
  import opened EvictImpl
  import FlushPolicyModel
  import opened StateBCImpl
  import opened BucketImpl
  import opened DiskOpImpl
  import opened MainDiskIOHandler

  import opened LinearSequence_s
  import opened LinearSequence_i

  import IT = IndirectionTable

  import opened Sequences

  import opened Bounds
  import opened NativeTypes
  import opened BucketsLib
  import opened BucketWeights

  // temporarily moving method to cache
  // method biggestSlot(shared buckets: lseq<MutBucket>) returns (res : (uint64, uint64))
  // requires MutBucket.InvLseq(buckets)
  // requires FlushPolicyModel.biggestSlot.requires(MutBucket.ILseq(buckets))
  // ensures res == FlushPolicyModel.biggestSlot(MutBucket.ILseq(buckets))
  // {
  //   WeightBucketLeBucketList(MutBucket.ILseq(buckets), 0);
  //   var j := 1;
  //   var bestIdx := 0;
  //   var bestWeight := lseq_peek(buckets, 0).weight;

  //   while j < lseq_length_raw(buckets)
  //   invariant FlushPolicyModel.biggestSlotIterate.requires(MutBucket.ILseq(buckets), j, bestIdx, bestWeight)
  //   invariant FlushPolicyModel.biggestSlotIterate(MutBucket.ILseq(buckets), j, bestIdx, bestWeight) == FlushPolicyModel.biggestSlot(MutBucket.ILseq(buckets))
  //   {
  //     WeightBucketLeBucketList(MutBucket.ILseq(buckets), j as int);
  //     var w := lseq_peek(buckets, j).weight;
  //     if w > bestWeight {
  //       bestIdx := j;
  //       bestWeight := w;
  //     }
  //     j := j + 1;
  //   }
  //   return (bestIdx, bestWeight);
  // }

  method getActionToSplit(s: ImplVariables, stack: seq<BT.G.Reference>,
    slots: seq<uint64>, i: uint64)
  returns (action : FlushPolicyModel.Action)
  requires 0 <= i as int < |stack|
  requires Inv(s)
  requires FlushPolicyModel.ValidStackSlots(s.I(), stack, slots)
  ensures action == FlushPolicyModel.getActionToSplit(s.I(), stack, slots, i)
  {
    FlushPolicyModel.reveal_getActionToSplit();

    if i == 0 {
      // Can't split root until we grow it.
      if TotalCacheSize(s) <= MaxCacheSizeUint64() - 1 {
        action := FlushPolicyModel.ActionGrow;
      } else {
        action := FlushPolicyModel.ActionEvict;
      }
    } else {
      var _, nodePrevChildren := s.cache.GetNodeInfo(stack[i-1]);
      if |nodePrevChildren.value| as uint64 < MaxNumChildrenUint64() {
        var bucketslen := s.cache.GetNodeBucketsLen(stack[i]);
        if bucketslen == 1 {
          action := FlushPolicyModel.ActionRepivot(stack[i]);
        } else {
          if TotalCacheSize(s) <= MaxCacheSizeUint64() - 2 {
            action := FlushPolicyModel.ActionSplit(stack[i-1], slots[i-1]);
          } else {
            action := FlushPolicyModel.ActionEvict;
          }
        }
      } else {
        action := getActionToSplit(s, stack, slots, i-1);
      }
    }
  }

  method getActionToFlush(s: ImplVariables, stack: seq<BT.G.Reference>, slots: seq<uint64>)
  returns (action : FlushPolicyModel.Action)
  requires |stack| <= 40
  requires Inv(s)
  requires FlushPolicyModel.ValidStackSlots(s.I(), stack, slots)
  decreases 0x1_0000_0000_0000_0000 - |stack|
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures (s.I(), action) == FlushPolicyModel.getActionToFlush(old(s.I()), stack, slots)
  {
    FlushPolicyModel.reveal_getActionToFlush();

    if |stack| as uint64 == 40 {
      action := FlushPolicyModel.ActionFail;
    } else {
      var ref := stack[|stack| as uint64 - 1];
      var _, children := s.cache.GetNodeInfo(ref);
      var bucketslen := s.cache.GetNodeBucketsLen(ref);

      if children.None? || bucketslen == MaxNumChildrenUint64() {
        action := getActionToSplit(s, stack, slots, |stack| as uint64 - 1);
      } else {
        var bs:(uint64, uint64) := s.cache.NodeBiggestSlot(ref);
        var (slot, slotWeight) := bs;
        if bucketslen as uint64 < 8 {
          var childref := children.value[slot];
          var childincache := s.cache.InCache(childref);
          if childincache {
            s.lru.Use(childref);
            LruModel.LruUse(old(s.lru.Queue), childref);

            var childTotalWeight := s.cache.NodeBucketsWeight(childref);
            if childTotalWeight + FlushTriggerWeightUint64() <= MaxTotalBucketWeightUint64() {
              if TotalCacheSize(s) <= MaxCacheSizeUint64() - 1 {
                action := FlushPolicyModel.ActionFlush(ref, slot);
              } else {
                action := FlushPolicyModel.ActionEvict;
              }
            } else {
              action := getActionToFlush(s, stack + [childref], slots + [slot]);
            }
          } else {
            if TotalCacheSize(s) <= MaxCacheSizeUint64() - 1 {
              action := FlushPolicyModel.ActionPageIn(childref);
            } else {
              action := FlushPolicyModel.ActionEvict;
            }
          }
        } else {
          action := getActionToSplit(s, stack, slots, |stack| as uint64 - 1);
        }
      }
    }
  }

  method runFlushPolicy(s: ImplVariables, io: DiskIOHandler)
  requires Inv(s)
  requires io.initialized()
  requires s.ready
  requires BT.G.Root() in s.cache.I()
  requires io !in s.Repr()
  requires |s.ephemeralIndirectionTable.I().graph| <= IT.MaxSize() - 3
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures FlushPolicyModel.runFlushPolicy(old(s.I()), old(IIO(io)), s.I(), IIO(io))
  {
    FlushPolicyModel.reveal_runFlushPolicy();

    LruModel.LruUse(s.lru.Queue, BT.G.Root());
    s.lru.Use(BT.G.Root());
    assert SBCM.IBlockCache(s.I()) == SBCM.IBlockCache(old(s.I()));

    FlushPolicyModel.getActionToFlushValidAction(s.I(), [BT.G.Root()], []);
    var action := getActionToFlush(s, [BT.G.Root()], []);

    match action {
      case ActionPageIn(ref) => {
        PageInNodeReq(s, io, ref);
      }
      case ActionSplit(parentref, slot) => {
        var _, parent_children := s.cache.GetNodeInfo(parentref);
        doSplit(s, parentref, parent_children.value[slot], slot);
      }
      case ActionRepivot(ref) => {
        repivotLeaf(s, ref);
      }
      case ActionFlush(parentref, slot) => {
        var _, parent_children := s.cache.GetNodeInfo(parentref);
        var childref := parent_children.value[slot];
        flush(s, parentref, slot, childref);
      }
      case ActionGrow => {
        grow(s);
      }
      case ActionEvict => {
        EvictOrDealloc(s, io);
      }
      case ActionFail => {
        print "ActionFail\n";
      }
    }
  }
}
