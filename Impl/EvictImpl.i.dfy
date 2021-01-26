include "EvictModel.i.dfy"
include "DeallocImpl.i.dfy"
include "SyncImpl.i.dfy"

module EvictImpl {
  import opened IOImpl
  import opened BookkeepingImpl
  import opened DeallocImpl
  import opened SyncImpl
  import EvictModel
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

  method Evict(linear inout s: ImplVariables, ref: BT.G.Reference)
  requires old_s.WF()
  requires old_s.Ready?
  requires ref in old_s.cache.I()
  ensures s.W()
  ensures s.Ready?
  ensures s.I() == EvictModel.Evict(old_s.I(), ref)
  {
    inout s.lru.Remove(ref);
    inout s.cache.Remove(ref);
    assert s.I().cache == EvictModel.Evict(old_s.I(), ref).cache;
  }

  method NeedToWrite(shared s: ImplVariables, ref: BT.G.Reference)
  returns (b: bool)
  requires s.WF()
  requires s.Ready?
  ensures b == EvictModel.NeedToWrite(s.I(), ref)
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

  method CanEvict(shared s: ImplVariables, ref: BT.G.Reference)
  returns (b: bool)
  requires s.WF()
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable.I().graph ==>
      ref in s.ephemeralIndirectionTable.I().locs
  ensures b == EvictModel.CanEvict(s.I(), ref)
  {
    var eph := s.ephemeralIndirectionTable.GetEntry(ref);
    if (eph.Some?) {
      return BC.OutstandingWrite(ref, eph.value.loc.value) !in s.outstandingBlockWrites.Values;
    } else {
      return true;
    }
  }

  method EvictOrDealloc(linear inout s: ImplVariables, io: DiskIOHandler)
  requires old_s.Inv()
  requires old_s.Ready?
  requires io.initialized()
  requires |old_s.cache.I()| > 0
  modifies io
  ensures s.W()
  ensures s.Ready?
  ensures EvictModel.EvictOrDealloc(old_s.I(), old(IIO(io)), s.I(), IIO(io))
  {
    var ref := FindDeallocable(s);
    DeallocModel.FindDeallocableCorrect(s.I());

    if ref.Some? {
      Dealloc(inout s, io, ref.value);
    } else {
      var refOpt := s.lru.NextOpt();
      if refOpt.None? {
      } else {
        var ref := refOpt.value;
        var needToWrite := NeedToWrite(s, ref);
        if needToWrite {
          if s.outstandingIndirectionTableWrite.None? {
            TryToWriteBlock(inout s, io, ref);
          }
        } else {
          var canEvict := CanEvict(s, ref);
          if canEvict {
            Evict(inout s, ref);
          }
        }
      }
    }
  }

  method PageInNodeReqOrMakeRoom(linear inout s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  requires old_s.Inv()
  requires old_s.Ready?
  requires io.initialized()
  requires ref in old_s.ephemeralIndirectionTable.I().graph
  requires ref !in old_s.cache.I()
  modifies io
  ensures s.W()
  ensures s.Ready?
  ensures EvictModel.PageInNodeReqOrMakeRoom(old_s.I(), old(IIO(io)), ref, s.I(), IIO(io))
  {
    EvictModel.reveal_PageInNodeReqOrMakeRoom();

    if s.TotalCacheSize() <= MaxCacheSizeUint64() - 1 {
      PageInNodeReq(inout s, io, ref);
    } else {
      var c := CacheImpl.CacheCount(s.cache); 
      if c > 0 {
        EvictOrDealloc(inout s, io);
      }
    }
  }
}
