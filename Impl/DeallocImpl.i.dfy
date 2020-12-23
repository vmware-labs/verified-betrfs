include "BookkeepingImpl.i.dfy"
include "DeallocModel.i.dfy"

module DeallocImpl { 
  import opened IOImpl
  import opened BookkeepingImpl
  import opened DiskOpImpl
  import DeallocModel
  import opened StateBCImpl
  import opened Bounds
  import opened MainDiskIOHandler

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import LruModel

  import opened NativeTypes

  method Dealloc(s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  requires Inv(s)
  requires io.initialized()
  requires DeallocModel.deallocable(s.I(), ref)
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures (s.I(), IIO(io)) == DeallocModel.Dealloc(old(s.I()), old(IIO(io)), ref);
  {
    DeallocModel.reveal_Dealloc();

    if s.frozenIndirectionTable != null {
      var b := s.frozenIndirectionTable.HasEmptyLoc(ref);
      if b {
        print "giving up; dealloc can't run because frozen isn't written";
        return;
      }
    }

    if BC.OutstandingRead(ref) in s.outstandingBlockReads.Values {
      print "giving up; dealloc can't dealloc because of outstanding read\n";
      return;
    }

    BookkeepingModel.lemmaIndirectionTableLocIndexValid(s.I(), ref);

    var oldLoc := s.ephemeralIndirectionTable.RemoveRef(ref);

    s.lru.Remove(ref);
    s.cache.Remove(ref);

    if oldLoc.Some? {
      s.blockAllocator.MarkFreeEphemeral(oldLoc.value.addr / NodeBlockSizeUint64());
    }

    ghost var s1 := s.I();
    ghost var s2 := DeallocModel.Dealloc(old(s.I()), old(IIO(io)), ref).0;

    assert s1.cache == s2.cache;
  }

  method FindDeallocable(s: ImplVariables) returns (ref: Option<Reference>)
  requires s.WF()
  requires s.ready
  ensures ref == DeallocModel.FindDeallocable(s.I())
  {
    DeallocModel.reveal_FindDeallocable();
    ref := s.ephemeralIndirectionTable.FindDeallocable();
  }
}
