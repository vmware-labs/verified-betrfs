// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "BookkeepingModel.i.dfy"

module DeallocModel { 
  import IT = IndirectionTable
  import opened StateBCModel
  import opened StateSectorModel
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
    && s.ephemeralIndirectionTable.deallocable(ref)
  }

  function {:opaque} Dealloc(s: BCVariables, io: IO, ref: BT.G.Reference)
  : (res : (BCVariables, IO))
  requires BCInv(s)
  requires io.IOInit?
  requires deallocable(s, ref)
  {
    if (
      && s.frozenIndirectionTable.Some?
      && s.frozenIndirectionTable.value.hasEmptyLoc(ref)
    ) then (
      (s, io)
    ) else if BC.OutstandingRead(ref) in s.outstandingBlockReads.Values then (
      (s, io)
    ) else (
      var (eph, oldLoc) := s.ephemeralIndirectionTable.removeRef(ref);

      lemmaIndirectionTableLocIndexValid(s, ref);

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

  lemma DeallocCorrect(s: BCVariables, io: IO, ref: BT.G.Reference)
  requires BCInv(s)
  requires io.IOInit?
  requires deallocable(s, ref)
  ensures var (s', io') := Dealloc(s, io, ref);
      && WFBCVars(s')
      && ValidDiskOp(diskOp(io'))
      && IDiskOp(diskOp(io')).jdop.NoDiskOp?
      && (
        || BBC.Next(IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, AdvanceOp(UI.NoOp, true))
        || BBC.Next(IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, StatesInternalOp)
      )
  {
    reveal_Dealloc();
    var (s', io') := Dealloc(s, io, ref);

    LruModel.LruRemove(s.lru, ref);

    if (
      && s.frozenIndirectionTable.Some?
      && s.frozenIndirectionTable.value.hasEmptyLoc(ref)
    ) {
      assert noop(IBlockCache(s), IBlockCache(s'));
      return;
    }

    if BC.OutstandingRead(ref) in s.outstandingBlockReads.Values {
      assert noop(IBlockCache(s), IBlockCache(s'));
      return;
    }

    assert BC.OutstandingBlockReadsDoesNotHaveRef(s.outstandingBlockReads, ref);

    lemmaIndirectionTableLocIndexValid(s, ref);

    var (eph, oldLoc) := s.ephemeralIndirectionTable.removeRef(ref);

    var blockAllocator' := if oldLoc.Some?
      then BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / NodeBlockSize())
      else s.blockAllocator;

    freeIndirectionTableLocCorrect(s, s', ref,
      if oldLoc.Some?
      then Some(oldLoc.value.addr as int / NodeBlockSize())
      else None);
    reveal_ConsistentBitmap();

    assert WFBCVars(s');

    var iDiskOp := IDiskOp(diskOp(io)).bdop;
    assert BC.Unalloc(IBlockCache(s), IBlockCache(s'), iDiskOp, AdvanceOp(UI.NoOp, true), ref);
    assert BBC.BlockCacheMove(IBlockCache(s), IBlockCache(s'), iDiskOp, AdvanceOp(UI.NoOp, true), BC.UnallocStep(ref));
    //assert stepsBC(IBlockCache(s), IBlockCache(s'), AdvanceOp(UI.NoOp, true), io, BC.UnallocStep(ref));
    assert BBC.NextStep(IBlockCache(s), IBlockCache(s'), iDiskOp, AdvanceOp(UI.NoOp, true), BBC.BlockCacheMoveStep(BC.UnallocStep(ref)));
  }

  function {:opaque} FindDeallocable(s: BCVariables)
  : (ref: Option<Reference>)
  requires WFBCVars(s)
  requires s.Ready?
  {
    s.ephemeralIndirectionTable.findDeallocable()
  }

  lemma FindDeallocableCorrect(s: BCVariables)
  requires WFBCVars(s)
  requires s.Ready?
  ensures var ref := FindDeallocable(s);
      && (ref.Some? ==> ref.value in s.ephemeralIndirectionTable.I().graph)
      && (ref.Some? ==> deallocable(s, ref.value))
      && (ref.None? ==> forall r | r in s.ephemeralIndirectionTable.I().graph :: !deallocable(s, r))
  {
    reveal_FindDeallocable();
  }
}
