include "ImplModelEvict.i.dfy"
include "ImplDealloc.i.dfy"
include "ImplSync.i.dfy"

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

  import LruModel

  method Evict(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference)
  requires s.WF()
  requires s.ready
  requires ref in s.cache.Contents
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures s.I() == ImplModelEvict.Evict(Ic(k), old(s.I()), ref)
  {
    s.lru.Remove(ref);
    var _ := s.cache.Remove(ref);
    assume s.cache.Contents == MapRemove1(old(s.cache.Contents), ref);
  }

  method NeedToWrite(s: ImplVariables, ref: BT.G.Reference)
  returns (b: bool)
  requires s.WF()
  requires s.ready
  ensures b == ImplModelEvict.NeedToWrite(s.I(), ref)
  {
    var eph := s.ephemeralIndirectionTable.Get(ref);
    if eph.Some? && eph.value.0.None? {
      return true;
    }

    if (s.frozenIndirectionTable != null) {
      var fro := s.frozenIndirectionTable.Get(ref);
      if fro.Some? && fro.value.0.None? {
        return true;
      }
    }

    return false;
  }

  method CanEvict(s: ImplVariables, ref: BT.G.Reference)
  returns (b: bool)
  requires s.WF()
  requires s.ready
  requires ref in s.ephemeralIndirectionTable.Contents ==>
      s.ephemeralIndirectionTable.Contents[ref].0.Some?
  ensures b == ImplModelEvict.CanEvict(s.I(), ref)
  {
    var eph := s.ephemeralIndirectionTable.Get(ref);
    if (eph.Some?) {
      return BC.OutstandingWrite(ref, eph.value.0.value) !in s.outstandingBlockWrites.Values;
    } else {
      return true;
    }
  }

  method EvictOrDealloc(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  requires Inv(k, s)
  requires s.ready
  requires io.initialized()
  requires |s.cache.Contents| > 0
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures ImplModelEvict.EvictOrDealloc(Ic(k), old(s.I()), old(IIO(io)), s.I(), IIO(io))
  {
    var ref := FindDeallocable(s);
    ImplModelDealloc.FindDeallocableCorrect(s.I());

    if ref.Some? {
      Dealloc(k, s, io, ref.value);
    } else {
      var ref := s.lru.Next();
      if ref == BT.G.Root() {
      } else {
        var needToWrite := NeedToWrite(s, ref);
        if needToWrite {
          if s.outstandingIndirectionTableWrite.None? {
            TryToWriteBlock(k, s, io, ref);
          } else {
          }
        } else {
          var canEvict := CanEvict(s, ref);
          if canEvict {
            Evict(k, s, ref);
          } else {
          }
        }
      }
    }
  }
}
