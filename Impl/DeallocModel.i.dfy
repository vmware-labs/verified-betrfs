include "BookkeepingModel.i.dfy"

module DeallocModel { 
  import opened StateModel
  import opened IOModel
  import opened DiskOpModel
  import opened BookkeepingModel
  import opened Bounds
  import opened ViewOp
  import opened InterpretationDiskOps

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened NativeTypes

  import LruModel

  predicate deallocable(s: BCVariables, ref: BT.G.Reference)
  {
    && s.Ready?
    && IndirectionTableModel.deallocable(s.ephemeralIndirectionTable, ref)
  }

  function {:opaque} Dealloc(k: Constants, s: BCVariables, io: IO, ref: BT.G.Reference)
  : (res : (BCVariables, IO))
  requires BCInv(k, s)
  requires io.IOInit?
  requires deallocable(s, ref)
  {
    if (
      && s.frozenIndirectionTable.Some?
      && IndirectionTableModel.HasEmptyLoc(s.frozenIndirectionTable.value, ref)
    ) then (
      (s, io)
    ) else if BC.OutstandingRead(ref) in s.outstandingBlockReads.Values then (
      (s, io)
    ) else (
      var (eph, oldLoc) := IndirectionTableModel.RemoveRef(s.ephemeralIndirectionTable, ref);

      lemmaIndirectionTableLocIndexValid(k, s, ref);

      var blockAllocator' := if oldLoc.Some?
        then BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / NodeBlockSize())
        else s.blockAllocator;

      var s' := s
        .(ephemeralIndirectionTable := eph)
        .(cache := MapRemove(s.cache, {ref}))
        .(lru := LruModel.Remove(s.lru, ref))
        .(blockAllocator := blockAllocator');
      (s', io)
    )
  }

  lemma DeallocCorrect(k: Constants, s: BCVariables, io: IO, ref: BT.G.Reference)
  requires BCInv(k, s)
  requires io.IOInit?
  requires deallocable(s, ref)
  ensures var (s', io') := Dealloc(k, s, io, ref);
      && WFBCVars(s')
      && ValidDiskOp(diskOp(io'))
      && IDiskOp(diskOp(io')).jdop.NoDiskOp?
      && (
        || BBC.Next(Ik(k).bc, IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, AdvanceOp(UI.NoOp, true))
        || BBC.Next(Ik(k).bc, IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, StatesInternalOp)
      )
  {
    reveal_Dealloc();
    var (s', io') := Dealloc(k, s, io, ref);

    LruModel.LruRemove(s.lru, ref);

    if (
      && s.frozenIndirectionTable.Some?
      && IndirectionTableModel.HasEmptyLoc(s.frozenIndirectionTable.value, ref)
    ) {
      assert noop(k, IBlockCache(s), IBlockCache(s'));
      return;
    }

    if BC.OutstandingRead(ref) in s.outstandingBlockReads.Values {
      assert noop(k, IBlockCache(s), IBlockCache(s'));
      return;
    }

    assert BC.OutstandingBlockReadsDoesNotHaveRef(s.outstandingBlockReads, ref);

    lemmaIndirectionTableLocIndexValid(k, s, ref);

    var (eph, oldLoc) := IndirectionTableModel.RemoveRef(s.ephemeralIndirectionTable, ref);

    var blockAllocator' := if oldLoc.Some?
      then BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / NodeBlockSize())
      else s.blockAllocator;

    freeIndirectionTableLocCorrect(k, s, s', ref,
      if oldLoc.Some?
      then Some(oldLoc.value.addr as int / NodeBlockSize())
      else None);
    reveal_ConsistentBitmap();

    assert WFBCVars(s');

    var iDiskOp := IDiskOp(diskOp(io)).bdop;
    assert BC.Unalloc(Ik(k).bc, IBlockCache(s), IBlockCache(s'), iDiskOp, AdvanceOp(UI.NoOp, true), ref);
    assert BBC.BlockCacheMove(Ik(k).bc, IBlockCache(s), IBlockCache(s'), iDiskOp, AdvanceOp(UI.NoOp, true), BC.UnallocStep(ref));
    //assert stepsBC(k, IBlockCache(s), IBlockCache(s'), AdvanceOp(UI.NoOp, true), io, BC.UnallocStep(ref));
    assert BBC.NextStep(Ik(k).bc, IBlockCache(s), IBlockCache(s'), iDiskOp, AdvanceOp(UI.NoOp, true), BBC.BlockCacheMoveStep(BC.UnallocStep(ref)));
  }

  function {:opaque} FindDeallocable(s: BCVariables)
  : (ref: Option<Reference>)
  requires WFBCVars(s)
  requires s.Ready?
  {
    IndirectionTableModel.FindDeallocable(s.ephemeralIndirectionTable)
  }

  lemma FindDeallocableCorrect(s: BCVariables)
  requires WFBCVars(s)
  requires s.Ready?
  ensures var ref := FindDeallocable(s);
      && (ref.Some? ==> ref.value in IIndirectionTable(s.ephemeralIndirectionTable).graph)
      && (ref.Some? ==> deallocable(s, ref.value))
      && (ref.None? ==> forall r | r in IIndirectionTable(s.ephemeralIndirectionTable).graph :: !deallocable(s, r))
  {
    reveal_FindDeallocable();
    IndirectionTableModel.FindDeallocableCorrect(s.ephemeralIndirectionTable);
  }
}
