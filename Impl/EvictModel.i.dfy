include "DeallocModel.i.dfy"
include "SyncModel.i.dfy"

module EvictModel {
  import opened StateModel
  import opened IOModel
  import opened BookkeepingModel
  import opened DeallocModel
  import opened SyncModel
  import opened DiskOpModel
  import opened InterpretationDiskOps
  import opened ViewOp

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened Bounds

  import opened NativeTypes

  import LruModel

  function Evict(s: BCVariables, ref: BT.G.Reference) : (s' : BCVariables)
  requires s.Ready?
  requires ref in s.cache
  {
    s.(cache := MapRemove1(s.cache, ref))
     .(lru := LruModel.Remove(s.lru, ref))
  }

  predicate NeedToWrite(s: BCVariables, ref: BT.G.Reference)
  requires s.Ready?
  {
    || (
      && ref in s.ephemeralIndirectionTable.graph
      && ref !in s.ephemeralIndirectionTable.locs
    )
    || (
      && s.frozenIndirectionTable.Some?
      && ref in s.frozenIndirectionTable.value.graph
      && ref !in s.frozenIndirectionTable.value.locs
    )
  }

  predicate CanEvict(s: BCVariables, ref: BT.G.Reference)
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable.graph ==>
      ref in s.ephemeralIndirectionTable.locs
  {
    && (ref in s.ephemeralIndirectionTable.graph ==>
      && BC.OutstandingWrite(ref, s.ephemeralIndirectionTable.locs[ref]) !in s.outstandingBlockWrites.Values
    )
  }

  predicate EvictOrDealloc(s: BCVariables, io: IO,
      s': BCVariables, io': IO)
  requires BCInv(s)
  requires s.Ready?
  requires io.IOInit?
  requires |s.cache| > 0
  {
    var ref := FindDeallocable(s);
    FindDeallocableCorrect(s);

    if ref.Some? then (
      // If we can deallocate something, just do that.
      (s', io') == Dealloc(s, io, ref.value)
    ) else (
      var refOpt := LruModel.NextOpt(s.lru);
      if refOpt.None? then (
        && s' == s
        && io' == io
      ) else if NeedToWrite(s, refOpt.value) then (
        if && s.outstandingIndirectionTableWrite.None? then (
          && TryToWriteBlock(s, io, refOpt.value, s', io')
        ) else (
          && s' == s
          && io' == io
        )
      ) else if CanEvict(s, refOpt.value) then (
        && s' == Evict(s, refOpt.value)
        && io' == io
      ) else (
        && s' == s
        && io' == io
      )
    )
  }

  lemma EvictOrDeallocCorrect(s: BCVariables, io: IO,
      s': BCVariables, io': IO)
  requires EvictOrDealloc.requires(s, io, s', io')
  requires EvictOrDealloc(s, io, s', io')
  ensures WFBCVars(s')
  ensures ValidDiskOp(diskOp(io'))
  ensures IDiskOp(diskOp(io')).jdop.NoDiskOp?
  ensures
    || BBC.Next(IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, StatesInternalOp)
    || BBC.Next(IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, AdvanceOp(UI.NoOp, true))
  {
    var ref := FindDeallocable(s);
    FindDeallocableCorrect(s);

    if ref.Some? {
      DeallocCorrect(s, io, ref.value);
    } else {
      var refOpt := LruModel.NextOpt(s.lru);
      if refOpt.None? {
        assert noop(IBlockCache(s), IBlockCache(s));
      } else if (NeedToWrite(s, refOpt.value)) {
        if s.outstandingIndirectionTableWrite.None? {
          TryToWriteBlockCorrect(s, io, refOpt.value, s', io');
        } else {
          assert noop(IBlockCache(s), IBlockCache(s));
        }
      } else if CanEvict(s, refOpt.value) {
        LruModel.LruRemove(s.lru, refOpt.value);
        assert WFBCVars(s');
        assert stepsBC(IBlockCache(s), IBlockCache(s'), StatesInternalOp, io', BC.EvictStep(refOpt.value));
      } else {
        assert noop(IBlockCache(s), IBlockCache(s));
      }
    }
  }

  predicate {:opaque} PageInNodeReqOrMakeRoom(
      s: BCVariables, io: IO, ref: BT.G.Reference,
      s': BCVariables, io': IO)
  requires BCInv(s)
  requires s.Ready?
  requires io.IOInit?
  requires ref in s.ephemeralIndirectionTable.graph
  requires ref !in s.cache
  {
    if TotalCacheSize(s) <= MaxCacheSize() - 1 then (
      (s', io') == PageInNodeReq(s, io, ref)
    ) else if |s.cache| > 0 then (
      EvictOrDealloc(s, io, s', io')
    ) else (
      s' == s && io' == io
    )
  }

  lemma PageInNodeReqOrMakeRoomCorrect(
      s: BCVariables, io: IO, ref: BT.G.Reference,
      s': BCVariables, io': IO)
  requires PageInNodeReqOrMakeRoom.requires(s, io, ref, s', io')
  requires PageInNodeReqOrMakeRoom(s, io, ref, s', io')
  ensures WFBCVars(s')
  ensures ValidDiskOp(diskOp(io'))
  ensures IDiskOp(diskOp(io')).jdop.NoDiskOp?
  ensures
    || BBC.Next(IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, StatesInternalOp)
    || BBC.Next(IBlockCache(s), IBlockCache(s'), IDiskOp(diskOp(io')).bdop, AdvanceOp(UI.NoOp, true))
  {
    reveal_PageInNodeReqOrMakeRoom();

    if TotalCacheSize(s) <= MaxCacheSize() - 1 {
      PageInNodeReqCorrect(s, io, ref);
    } else if |s.cache| > 0 {
      EvictOrDeallocCorrect(s, io, s', io');
    } else {
      assert noop(IBlockCache(s), IBlockCache(s));
    }
  }
}
