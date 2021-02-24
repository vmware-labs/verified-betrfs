include "BookkeepingImpl.i.dfy"
// include "DeallocModel.i.dfy"

module DeallocImpl { 
  import opened IOImpl
  import opened BookkeepingImpl
  import opened DiskOpImpl
  // import DeallocModel
  import opened StateBCImpl
  import opened Bounds
  import opened MainDiskIOHandler

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import LruModel

  // import opened StateSectorModel
  import opened IOModel
  import opened DiskOpModel
  // import opened BookkeepingModel
  import opened ViewOp
  import opened InterpretationDiskOps

  import opened NativeTypes
  method Dealloc(linear inout s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  requires old_s.Inv()
  requires io.initialized()
  requires old_s.Ready?
  requires old_s.ephemeralIndirectionTable.deallocable(ref)

  modifies io
  ensures s.W()
  ensures s.Ready?
  ensures 
    var dop := diskOp(IIO(io));
    && ValidDiskOp(dop)
    && IDiskOp(dop).jdop.NoDiskOp?
    && (
      || BBC.Next(old_s.I(), s.I(), IDiskOp(dop).bdop, AdvanceOp(UI.NoOp, true))
      || BBC.Next(old_s.I(), s.I(), IDiskOp(dop).bdop, StatesInternalOp)
    )
  {
    var nop := false;

    if s.frozenIndirectionTable.lSome? {
      var b := s.frozenIndirectionTable.value.HasEmptyLoc(ref);
      if b {
        print "giving up; dealloc can't run because frozen isn't written";
        nop := true;
      }
    }

    if nop || BC.OutstandingRead(ref) in s.outstandingBlockReads.Values {
      print "giving up; dealloc can't dealloc because of outstanding read\n";
      assert IOModel.noop(s.I(), s.I());
  } else {
      lemmaIndirectionTableLocIndexValid(s, ref);
      assert BC.OutstandingBlockReadsDoesNotHaveRef(s.outstandingBlockReads, ref);

      var oldLoc := inout s.ephemeralIndirectionTable.RemoveRef(ref);

      inout s.lru.Remove(ref);
      inout s.cache.Remove(ref);

      if oldLoc.Some? {
        inout s.blockAllocator.MarkFreeEphemeral(oldLoc.value.addr / NodeBlockSizeUint64());
      }

      ghost var iDiskOp := IDiskOp(diskOp(IIO(io))).bdop;
      assert BC.Unalloc(old_s.I(), s.I(), iDiskOp, AdvanceOp(UI.NoOp, true), ref);
      assert BBC.BlockCacheMove(old_s.I(), s.I(), iDiskOp, AdvanceOp(UI.NoOp, true), BC.UnallocStep(ref));
      assert BBC.NextStep(old_s.I(), s.I(), iDiskOp, AdvanceOp(UI.NoOp, true), BBC.BlockCacheMoveStep(BC.UnallocStep(ref)));
    }
  }

  method FindDeallocable(shared s: ImplVariables) returns (ref: Option<Reference>)
  requires s.Inv()
  requires s.Ready?
  ensures 
      && (ref.Some? ==> ref.value in s.ephemeralIndirectionTable.graph)
      && (ref.Some? ==> s.ephemeralIndirectionTable.deallocable(ref.value))
      && (ref.None? ==> forall r | r in s.ephemeralIndirectionTable.graph :: !s.ephemeralIndirectionTable.deallocable(r))
  {
    // DeallocModel.reveal_FindDeallocable();
    ref := s.ephemeralIndirectionTable.FindDeallocable();
  }
}
