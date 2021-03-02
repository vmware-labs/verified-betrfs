include "SyncImpl.i.dfy"
include "DeallocImpl.i.dfy"

module EvictImpl {
  import opened IOImpl
  import opened BookkeepingImpl
  import opened DeallocImpl
  import opened SyncImpl
  import opened DiskOpImpl
  import opened StateBCImpl
  import opened Bounds
  import opened MainDiskIOHandler

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened NativeTypes

  import LruModel

  import opened InterpretationDiskOps
  import opened ViewOp
  import opened DiskOpModel

  predicate needToWrite(s: ImplVariables, ref: BT.G.Reference)
  requires s.Ready?
  {
    || (
      && ref in s.ephemeralIndirectionTable.graph
      && ref !in s.ephemeralIndirectionTable.locs
    )
    || (
      && s.frozenIndirectionTable.lSome?
      && ref in s.frozenIndirectionTable.value.graph
      && ref !in s.frozenIndirectionTable.value.locs
    )
  }

  method NeedToWrite(shared s: ImplVariables, ref: BT.G.Reference)
  returns (b: bool)
  requires s.W() && s.Ready?
  ensures b == needToWrite(s, ref)
  {
    var eph := s.ephemeralIndirectionTable.GetEntry(ref);
    if eph.Some? && eph.value.loc.None? {
      return true;
    }

    if (s.frozenIndirectionTable.lSome?) {
      var fro := s.frozenIndirectionTable.value.GetEntry(ref);
      if fro.Some? && fro.value.loc.None? {
        return true;
      }
    }

    return false;
  }

  predicate canEvict(s: ImplVariables, ref: BT.G.Reference)
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable.graph ==>
      ref in s.ephemeralIndirectionTable.locs
  {
    && (ref in s.ephemeralIndirectionTable.graph ==>
      && BC.OutstandingWrite(ref, s.ephemeralIndirectionTable.locs[ref]) !in s.outstandingBlockWrites.Values
    )
  }

  method CanEvict(shared s: ImplVariables, ref: BT.G.Reference)
  returns (b: bool)
  requires s.W() && s.Ready?
  requires ref in s.ephemeralIndirectionTable.I().graph ==>
      ref in s.ephemeralIndirectionTable.I().locs
  ensures b == canEvict(s, ref)
  {
    var eph := s.ephemeralIndirectionTable.GetEntry(ref);
    if (eph.Some?) {
      return BC.OutstandingWrite(ref, eph.value.loc.value) !in s.outstandingBlockWrites.Values;
    } else {
      return true;
    }
  }

  method EvictOrDealloc(linear inout s: ImplVariables, io: DiskIOHandler)
  requires old_s.Inv() && old_s.Ready?
  requires io.initialized()
  requires |old_s.cache.I()| > 0
  modifies io
  ensures s.WFBCVars() && s.Ready?
  ensures ValidDiskOp(diskOp(IIO(io)))
  ensures IDiskOp(diskOp(IIO(io))).jdop.NoDiskOp?
  ensures
    || BBC.Next(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp)
    || BBC.Next(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, AdvanceOp(UI.NoOp, true))
  {
    var ref := FindDeallocable(s);

    if ref.Some? {
      Dealloc(inout s, io, ref.value);
    } else {
      var refOpt := s.lru.NextOpt();
      if refOpt.Some? {
        var ref := refOpt.value;
        var needToWrite := NeedToWrite(s, ref);
        if needToWrite {
          if s.outstandingIndirectionTableWrite.None? {
            TryToWriteBlock(inout s, io, ref);
          } else {
            assert IOModel.noop(s.I(), s.I());
          }
        } else {
          var canEvict := CanEvict(s, ref);
          if canEvict {
            LruModel.LruRemove(s.lru.Queue(), ref);
            inout s.lru.Remove(ref);
            inout s.cache.Remove(ref);
            assert IOModel.stepsBC(old_s.I(), s.I(), StatesInternalOp, IIO(io), BC.EvictStep(ref));
          } else {
            assert IOModel.noop(s.I(), s.I());
          }
        }
      } else {
        assert IOModel.noop(s.I(), s.I());
      }
    }
  }

  method PageInNodeReqOrMakeRoom(linear inout s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  requires old_s.Inv() && old_s.Ready?
  requires io.initialized()
  requires ref in old_s.ephemeralIndirectionTable.I().graph
  requires ref !in old_s.cache.I()
  modifies io
  ensures s.WFBCVars() && s.Ready?
  ensures ValidDiskOp(diskOp(IIO(io)))
  ensures IDiskOp(diskOp(IIO(io))).jdop.NoDiskOp?
  ensures
    || BBC.Next(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp)
    || BBC.Next(old_s.I(), s.I(), IDiskOp(diskOp(IIO(io))).bdop, AdvanceOp(UI.NoOp, true))
  {
    if s.TotalCacheSize() <= MaxCacheSizeUint64() - 1 {
      PageInNodeReq(inout s, io, ref);
      assert ValidDiskOp(diskOp(IIO(io)));
    } else {
      var c := CacheImpl.CacheCount(s.cache); 
      if c > 0 {
        EvictOrDealloc(inout s, io);
      } else {
        assert IOModel.noop(s.I(), s.I());
      }
    }
  }
}
