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
  returns (s' : ImplVariables)
  requires WFVars(s)
  requires s.Ready?
  requires ref in s.cache
  ensures WVars(s')
  ensures IVars(s') == ImplModelEvict.Evict(Ic(k), old(IVars(s)), ref)
  {
    s' := s.(cache := MapRemove1(s.cache, ref))
     .(lru := LruModel.Remove(s.lru, ref));
  }

  method NeedToWrite(s: ImplVariables, ref: BT.G.Reference)
  returns (b: bool)
  requires WFVars(s)
  requires s.Ready?
  ensures b == ImplModelEvict.NeedToWrite(IVars(s), ref)
  {
    var eph := s.ephemeralIndirectionTable.Get(ref);
    if eph.Some? && eph.value.0.None? {
      return true;
    }

    if (s.frozenIndirectionTable.Some?) {
      var fro := s.frozenIndirectionTable.value.Get(ref);
      if fro.Some? && fro.value.0.None? {
        return true;
      }
    }

    return false;
  }

  method CanEvict(s: ImplVariables, ref: BT.G.Reference)
  returns (b: bool)
  requires WFVars(s)
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable.Contents ==>
      s.ephemeralIndirectionTable.Contents[ref].0.Some?
  ensures b == ImplModelEvict.CanEvict(IVars(s), ref)
  {
    var eph := s.ephemeralIndirectionTable.Get(ref);
    if (eph.Some?) {
      return BC.OutstandingWrite(ref, eph.value.0.value) !in s.outstandingBlockWrites.Values;
    } else {
      return true;
    }
  }

  method EvictOrDealloc(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires Inv(k, s)
  requires s.Ready?
  requires io.initialized()
  requires |s.cache| > 0
  ensures WVars(s')
  ensures ImplModelEvict.EvictOrDealloc(Ic(k), old(IVars(s)), old(IIO(io)), IVars(s'), IIO(io))
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies io
  modifies s.ephemeralIndirectionTable.Repr
  modifies if s.Ready? && s.frozenIndirectionTable.Some? then s.frozenIndirectionTable.value.Repr else {}
  {
    var ref := FindDeallocable(s);
    ImplModelDealloc.FindDeallocableCorrect(IVars(s));

    if ref.Some? {
      s' := Dealloc(k, s, io, ref.value);
    } else {
      var ref := LruModel.Next(s.lru);
      if ref == BT.G.Root() {
        s' := s;
      } else {
        var needToWrite := NeedToWrite(s, ref);
        if needToWrite {
          if s.outstandingIndirectionTableWrite.None? {
            s' := TryToWriteBlock(k, s, io, ref);
          } else {
            s' := s;
          }
        } else {
          var canEvict := CanEvict(s, ref);
          if canEvict {
            s' := Evict(k, s, ref);
          } else {
            s' := s;
          }
        }
      }
    }
  }
}
