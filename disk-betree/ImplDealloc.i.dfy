include "ImplCache.i.dfy"
include "ImplModelDealloc.i.dfy"

module ImplDealloc { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache
  import ImplModelDealloc
  import opened ImplState
  import opened Bounds

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import LruModel

  import opened NativeTypes

  method Dealloc(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  requires Inv(k, s)
  requires io.initialized()
  requires ImplModelDealloc.deallocable(s.I(), ref)
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.ready
  ensures (s.I(), IIO(io)) == ImplModelDealloc.Dealloc(Ic(k), old(s.I()), old(IIO(io)), ref);
  {
    ImplModelDealloc.reveal_Dealloc();

    if s.frozenIndirectionTable != null {
      var lbaGraph := s.frozenIndirectionTable.Get(ref);
      if lbaGraph.Some? {
        var (lba, _) := lbaGraph.value;
        if lba.None? {
          print "giving up; dealloc can't dealloc because frozen isn't written\n";
          return;
        }
      }
    }

    if !BC.OutstandingBlockReadsDoesNotHaveRef(s.outstandingBlockReads, ref) {
      print "giving up; dealloc can't dealloc because of outstanding read\n";
      return;
    }

    ImplModelCache.lemmaIndirectionTableLocIndexValid(Ic(k), s.I(), ref);

    var oldEntry := s.ephemeralIndirectionTable.RemoveAndGet(ref);

    s.lru.Remove(ref);
    s.cache.Remove(ref);

    if oldEntry.Some? && oldEntry.value.0.Some? {
      s.blockAllocator.MarkFreeEphemeral(oldEntry.value.0.value.addr / BlockSizeUint64());
    }

    assume s.ephemeralIndirectionTable.Contents
        == MapRemove(old(s.ephemeralIndirectionTable.Contents), {ref});

    ghost var s1 := s.I();
    ghost var s2 := ImplModelDealloc.Dealloc(Ic(k), old(s.I()), old(IIO(io)), ref).0;

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
  ensures ref == ImplModelDealloc.FindDeallocable(s.I())
  {
  }
}
