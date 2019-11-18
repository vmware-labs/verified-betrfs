include "ImplModelEvict.i.dfy"
include "ImplDealloc.i.dfy"
include "ImplSync.i.dfy"
include "../lib/Base/NativeBenchmarking.s.dfy"

module ImplEvict {
  import opened Impl
  import opened ImplIO
  import opened ImplCache
  import opened ImplDealloc
  import opened ImplSync
  import ImplModelEvict
  import opened ImplState

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened NativeTypes
  import NativeBenchmarking

  import LruModel

  method Evict(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference)
  requires s.WF()
  requires s.ready
  requires ref in s.cache.I()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures s.I() == ImplModelEvict.Evict(Ic(k), old(s.I()), ref)
  {
    s.lru.Remove(ref);
    s.cache.Remove(ref);
    assert s.I().cache == ImplModelEvict.Evict(Ic(k), old(s.I()), ref).cache;
  }

  method NeedToWrite(s: ImplVariables, ref: BT.G.Reference)
  returns (b: bool)
  requires s.WF()
  requires s.ready
  ensures b == ImplModelEvict.NeedToWrite(s.I(), ref)
  {
    var eph := s.ephemeralIndirectionTable.GetEntry(ref);
    if eph.Some? && eph.value.loc.None? {
      return true;
    }

    if (s.frozenIndirectionTable != null) {
      var fro := s.frozenIndirectionTable.GetEntry(ref);
      if fro.Some? && fro.value.loc.None? {
        return true;
      }
    }

    return false;
  }

  method CanEvict(s: ImplVariables, ref: BT.G.Reference)
  returns (b: bool)
  requires s.WF()
  requires s.ready
  requires ref in s.ephemeralIndirectionTable.I().graph ==>
      ref in s.ephemeralIndirectionTable.I().locs
  ensures b == ImplModelEvict.CanEvict(s.I(), ref)
  {
    var eph := s.ephemeralIndirectionTable.GetEntry(ref);
    if (eph.Some?) {
      return BC.OutstandingWrite(ref, eph.value.loc.value) !in s.outstandingBlockWrites.Values;
    } else {
      return true;
    }
  }

  method EvictOrDealloc(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  requires Inv(k, s)
  requires s.ready
  requires io.initialized()
  requires |s.cache.I()| > 0
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures ImplModelEvict.EvictOrDealloc(Ic(k), old(s.I()), old(IIO(io)), s.I(), IIO(io))
  {
    NativeBenchmarking.start("FindDeallocable");
    var ref := FindDeallocable(s);
    NativeBenchmarking.end("FindDeallocable");
    ImplModelDealloc.FindDeallocableCorrect(s.I());

    if ref.Some? {
      NativeBenchmarking.start("dealloc");
      Dealloc(k, s, io, ref.value);
      NativeBenchmarking.end("dealloc");
    } else {
      var ref := s.lru.Next();
      if ref == BT.G.Root() {
      } else {
        var needToWrite := NeedToWrite(s, ref);
        if needToWrite {
          if s.outstandingIndirectionTableWrite.None? {
            NativeBenchmarking.start("write back for eviction");
            TryToWriteBlock(k, s, io, ref);
            NativeBenchmarking.end("write back for eviction");
          } else {
          }
        } else {
          var canEvict := CanEvict(s, ref);
          if canEvict {
            NativeBenchmarking.start("evict");
            Evict(k, s, ref);
            NativeBenchmarking.end("evict");
          } else {
          }
        }
      }
    }
  }
}
