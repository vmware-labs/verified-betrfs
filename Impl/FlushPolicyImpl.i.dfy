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
  import opened StateImpl
  import opened BucketImpl
  import opened DiskOpImpl
  import opened MainDiskIOHandler

  import opened LinearSequence_s
  import opened LinearSequence_i

  import opened Sequences

  import opened Bounds
  import opened NativeTypes
  import opened BucketsLib
  import opened BucketWeights

  method biggestSlot(shared buckets: lseq<MutBucket>) returns (res : (uint64, uint64))
  requires MutBucket.InvLseq(buckets)
  requires FlushPolicyModel.biggestSlot.requires(MutBucket.ILseq(buckets))
  ensures res == FlushPolicyModel.biggestSlot(old(MutBucket.ILseq(buckets)))
  {
    WeightBucketLeBucketList(MutBucket.ILseq(buckets), 0);
    var j := 1;
    var bestIdx := 0;
    var bestWeight := lseq_peek(buckets, 0).weight;

    while j < lseq_length_raw(buckets)
    invariant FlushPolicyModel.biggestSlotIterate.requires(MutBucket.ILseq(buckets), j, bestIdx, bestWeight)
    invariant FlushPolicyModel.biggestSlotIterate(MutBucket.ILseq(buckets), j, bestIdx, bestWeight) == FlushPolicyModel.biggestSlot(MutBucket.ILseq(buckets))
    {
      WeightBucketLeBucketList(MutBucket.ILseq(buckets), j as int);
      var w := lseq_peek(buckets, j).weight;
      if w > bestWeight {
        bestIdx := j;
        bestWeight := w;
      }
      j := j + 1;
    }
    return (bestIdx, bestWeight);
  }

  method getActionToSplit(s: ImplVariables, stack: seq<BT.G.Reference>, slots: seq<uint64>, i: uint64) returns (action : FlushPolicyModel.Action)
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
      var nodePrev := s.cache.GetOpt(stack[i-1]);
      var nodePrevChildren := nodePrev.value.GetChildren();
      if |nodePrevChildren.value| as uint64 < MaxNumChildrenUint64() {
        var nodeThis := s.cache.GetOpt(stack[i]);
        var bucketslen := nodeThis.value.GetBucketsLen();
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

  method getActionToFlush(s: ImplVariables, stack: seq<BT.G.Reference>, slots: seq<uint64>) returns (action : FlushPolicyModel.Action)
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
      var nodeOpt := s.cache.GetOpt(ref);
      var node := nodeOpt.value;
      var children := node.GetChildren();
      var bucketslen := node.GetBucketsLen();

      if children.None? || bucketslen == MaxNumChildrenUint64() {
        action := getActionToSplit(s, stack, slots, |stack| as uint64 - 1);
      } else {
        var bs:(uint64, uint64) := biggestSlot(node.box.Borrow().buckets);
        var (slot, slotWeight) := bs;
        if bucketslen as uint64 < 8 {
          var childref := children.value[slot];
          var childOpt := s.cache.GetOpt(childref);
          if childOpt.Some? {
            s.cache.LemmaNodeReprLeRepr(childref);
            var child := childOpt.value;
            assert MutBucket.InvLseq(child.Read().buckets);
            s.lru.Use(childref);
            assert MutBucket.InvLseq(child.Read().buckets);
            LruModel.LruUse(old(s.lru.Queue), childref);

            var childTotalWeight: uint64 := MutBucket.computeWeightOfSeq(child.box.Borrow().buckets);

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
  requires |s.ephemeralIndirectionTable.I().graph| <= IndirectionTableModel.MaxSize() - 3
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures FlushPolicyModel.runFlushPolicy(old(s.I()), old(IIO(io)), s.I(), IIO(io))
  {
    FlushPolicyModel.reveal_runFlushPolicy();

    LruModel.LruUse(s.lru.Queue, BT.G.Root());
    s.lru.Use(BT.G.Root());
    assert SM.IBlockCache(s.I()) == SM.IBlockCache(old(s.I()));

    FlushPolicyModel.getActionToFlushValidAction(s.I(), [BT.G.Root()], []);
    var action := getActionToFlush(s, [BT.G.Root()], []);

    match action {
      case ActionPageIn(ref) => {
        PageInNodeReq(s, io, ref);
      }
      case ActionSplit(parentref, slot) => {
        var parent := s.cache.GetOpt(parentref);
        var parent_children := parent.value.GetChildren();
        doSplit(s, parentref, parent_children.value[slot], slot);
      }
      case ActionRepivot(ref) => {
        var node := s.cache.GetOpt(ref);
        repivotLeaf(s, ref, node.value);
      }
      case ActionFlush(parentref, slot) => {
        var parent := s.cache.GetOpt(parentref);
        var parent_children := parent.value.GetChildren();
        var childref := parent_children.value[slot];
        var child := s.cache.GetOpt(childref);
        flush(s, parentref, slot, 
            parent_children.value[slot],
            child.value);
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
