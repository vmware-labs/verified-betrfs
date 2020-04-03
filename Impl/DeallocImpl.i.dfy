include "BookkeepingImpl.i.dfy"
include "DeallocModel.i.dfy"

module DeallocImpl { 
  import opened IOImpl
  import opened BookkeepingImpl
  import opened DiskOpImpl
  import DeallocModel
  import opened StateImpl
  import opened Bounds
  import opened MainDiskIOHandler

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import LruModel

  import opened NativeTypes

  method Dealloc(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  requires Inv(k, s)
  requires io.initialized()
  requires DeallocModel.deallocable(s.I(), ref)
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures (s.I(), IIO(io)) == DeallocModel.Dealloc(Ic(k), old(s.I()), old(IIO(io)), ref);
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

    BookkeepingModel.lemmaIndirectionTableLocIndexValid(Ic(k), s.I(), ref);

    var oldLoc := s.ephemeralIndirectionTable.RemoveRef(ref);

    s.lru.Remove(ref);
    s.cache.Remove(ref);

    if oldLoc.Some? {
      s.blockAllocator.MarkFreeEphemeral(oldLoc.value.addr / NodeBlockSizeUint64());
    }

    ghost var s1 := s.I();
    ghost var s2 := DeallocModel.Dealloc(Ic(k), old(s.I()), old(IIO(io)), ref).0;

    //assert s1.persistentIndirectionTable == s2.persistentIndirectionTable;
    //assert s1.frozenIndirectionTable == s2.frozenIndirectionTable;
    //assert s1.ephemeralIndirectionTable == s2.ephemeralIndirectionTable;
    //assert s1.outstandingIndirectionTableWrite == s2.outstandingIndirectionTableWrite;
    //assert s1.outstandingBlockWrites == s2.outstandingBlockWrites;
    //assert s1.outstandingBlockReads == s2.outstandingBlockReads;
    assert s1.cache == s2.cache;
    //assert s1.lru == s2.lru;
    //assert s1 == s2;
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
