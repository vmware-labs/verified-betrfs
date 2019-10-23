include "ImplModelCache.i.dfy"

module ImplModelDealloc { 
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelCache
  import opened Bounds

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened NativeTypes

  import LruModel

  predicate deallocable(s: Variables, ref: BT.G.Reference)
  {
    && s.Ready?
    && IndirectionTableModel.deallocable(s.ephemeralIndirectionTable, ref)
  }

  function {:opaque} Dealloc(k: Constants, s: Variables, io: IO, ref: BT.G.Reference)
  : (res : (Variables, IO))
  requires Inv(k, s)
  requires io.IOInit?
  requires deallocable(s, ref)
  {
    if (
      && s.frozenIndirectionTable.Some?
      && IndirectionTableModel.HasEmptyLoc(s.frozenIndirectionTable.value, ref)
    ) then (
      (s, io)
    ) else if !BC.OutstandingBlockReadsDoesNotHaveRef(s.outstandingBlockReads, ref) then (
      (s, io)
    ) else (
      var (eph, oldLoc) := IndirectionTableModel.RemoveRef(s.ephemeralIndirectionTable, ref);

      lemmaIndirectionTableLocIndexValid(k, s, ref);

      var blockAllocator' := if oldLoc.Some?
        then ImplModelBlockAllocator.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / BlockSize())
        else s.blockAllocator;

      var s' := s
        .(ephemeralIndirectionTable := eph)
        .(cache := MapRemove(s.cache, {ref}))
        .(lru := LruModel.Remove(s.lru, ref))
        .(blockAllocator := blockAllocator');
      (s', io)
    )
  }

  lemma DeallocCorrect(k: Constants, s: Variables, io: IO, ref: BT.G.Reference)
  requires Inv(k, s)
  requires io.IOInit?
  requires deallocable(s, ref)
  ensures var (s', io') := Dealloc(k, s, io, ref);
      && WFVars(s')
      &&  M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    reveal_Dealloc();
    var (s', io') := Dealloc(k, s, io, ref);

    LruModel.LruRemove(s.lru, ref);

    if (
      && s.frozenIndirectionTable.Some?
      && IndirectionTableModel.HasEmptyLoc(s.frozenIndirectionTable.value, ref)
    ) {
      assert noop(k, IVars(s), IVars(s'));
      return;
    }

    if !BC.OutstandingBlockReadsDoesNotHaveRef(s.outstandingBlockReads, ref) {
      assert noop(k, IVars(s), IVars(s'));
      return;
    }

    lemmaIndirectionTableLocIndexValid(k, s, ref);

    var (eph, oldLoc) := IndirectionTableModel.RemoveRef(s.ephemeralIndirectionTable, ref);

    var blockAllocator' := if oldLoc.Some?
      then ImplModelBlockAllocator.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / BlockSize())
      else s.blockAllocator;

    freeIndirectionTableLocCorrect(k, s, s', ref,
      if oldLoc.Some?
      then Some(oldLoc.value.addr as int / BlockSize())
      else None);
    reveal_ConsistentBitmap();

    assert WFVars(s');

    var iDiskOp := M.IDiskOp(diskOp(io));
    assert BC.Unalloc(Ik(k), IVars(s), IVars(s'), iDiskOp, ref);
    assert BBC.BlockCacheMove(Ik(k), IVars(s), IVars(s'), UI.NoOp, iDiskOp, BC.UnallocStep(ref));
    assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.UnallocStep(ref));
    // assert M.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, io.diskOp(), M.Step(BBC.BlockCacheMoveStep(BC.UnallocStep(ref))));
  }

  function {:opaque} FindDeallocable(s: Variables)
  : (ref: Option<Reference>)
  requires WFVars(s)
  requires s.Ready?
  {
    IndirectionTableModel.FindDeallocable(s.ephemeralIndirectionTable)
  }

  lemma FindDeallocableCorrect(s: Variables)
  requires WFVars(s)
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
