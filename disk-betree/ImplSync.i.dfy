include "Impl.i.dfy"
include "ImplIO.i.dfy"
include "ImplDealloc.i.dfy"
include "ImplModelSync.i.dfy"
include "ImplModelCache.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"
include "../lib/Base/NativeBenchmarking.s.dfy"

// See dependency graph in MainImpl.dfy

module ImplSync { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache
  import opened ImplDealloc
  import opened Bounds
  import ImplModelSync
  import ImplModelCache
  import ImplModelDealloc
  import ImplModelBlockAllocator
  import opened ImplState
  import NativeBenchmarking

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes

  method AssignRefToLocEphemeral(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, loc: BC.Location)
  requires s.W()
  requires s.ready
  requires ImplModelBlockAllocator.Inv(s.blockAllocator.I())
  requires 0 <= loc.addr as int / BlockSize() < NumBlocks()
  modifies s.Repr()
  ensures s.W()
  ensures WellUpdated(s)
  ensures s.I() == ImplModelSync.AssignRefToLocEphemeral(Ic(k), old(s.I()), ref, loc)
  ensures s.ready
  {
    ImplModelSync.reveal_AssignRefToLocEphemeral();

    var table := s.ephemeralIndirectionTable;
    var added := table.AddLocIfPresent(ref, loc);
    if added {
      s.blockAllocator.MarkUsedEphemeral(loc.addr / BlockSizeUint64());
    }
  }

  method AssignRefToLocFrozen(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, loc: BC.Location)
  requires s.W()
  requires s.ready
  requires s.I().frozenIndirectionTable.Some? ==> s.I().blockAllocator.frozen.Some?
  requires ImplModelBlockAllocator.Inv(s.blockAllocator.I())
  requires 0 <= loc.addr as int / BlockSize() < NumBlocks()
  modifies s.Repr()
  ensures s.W()
  ensures WellUpdated(s)
  ensures s.I() == ImplModelSync.AssignRefToLocFrozen(Ic(k), old(s.I()), ref, loc)
  ensures s.ready
  {
    ImplModelSync.reveal_AssignRefToLocFrozen();

    if s.frozenIndirectionTable != null {
      var table := s.frozenIndirectionTable;
      var added := table.AddLocIfPresent(ref, loc);
      if added {
        s.blockAllocator.MarkUsedFrozen(loc.addr / BlockSizeUint64());
      }
    }
  }

  method AssignIdRefLocOutstanding(k: ImplConstants, s: ImplVariables, id: D.ReqId, ref: BT.G.Reference, loc: BC.Location)
  requires s.W()
  requires s.ready
  requires ImplModelBlockAllocator.Inv(s.I().blockAllocator)
  requires 0 <= loc.addr as int / BlockSize() < NumBlocks()
  modifies s.Repr()
  ensures s.W()
  ensures WellUpdated(s)
  ensures s.I() == ImplModelSync.AssignIdRefLocOutstanding(Ic(k), old(s.I()), id, ref, loc)
  ensures s.ready
  {
    ImplModelSync.reveal_AssignIdRefLocOutstanding();

    s.outstandingBlockWrites := s.outstandingBlockWrites[id := BC.OutstandingWrite(ref, loc)];
    s.blockAllocator.MarkUsedOutstanding(loc.addr / BlockSizeUint64());
  }

  method FindRefInFrozenWithNoLoc(s: ImplVariables) returns (ref: Option<Reference>)
  requires s.WF()
  requires s.ready
  requires s.frozenIndirectionTable != null
  ensures ref == ImplModelSync.FindRefInFrozenWithNoLoc(s.I())
  {
    assume false;
    var it := s.frozenIndirectionTable.t.IterStart();

    while it.next.Some?
    {
      var ref := it.next.value.0;
      var lbaGraph := it.next.value.1;
      var lba := lbaGraph.loc;
      if lba.None? {
        return Some(ref);
      }
      it := s.frozenIndirectionTable.t.IterInc(it);
    }
    assert forall r | r in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable)).graph
        :: r in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable)).locs;
    return None;
  }

  method {:fuel BC.GraphClosed,0} {:fuel BC.CacheConsistentWithSuccessors,0}
  syncNotFrozen(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  requires io.initialized()
  modifies io
  requires Inv(k, s)
  requires s.ready
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable == null
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), IIO(io)) == ImplModelSync.syncNotFrozen(Ic(k), old(s.I()), old(IIO(io)))
  {
    var foundDeallocable := FindDeallocable(s);
    ImplModelDealloc.FindDeallocableCorrect(s.I());
    if foundDeallocable.Some? {
      Dealloc(k, s, io, foundDeallocable.value);
      return;
    }

    var clonedEphemeralIndirectionTable := s.ephemeralIndirectionTable.Clone();

    s.frozenIndirectionTable := clonedEphemeralIndirectionTable;
    s.syncReqs := SyncReqs3to2(s.syncReqs);
    s.blockAllocator.CopyEphemeralToFrozen();

    return;
  }

  method TryToWriteBlock(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  requires s.ready
  requires Inv(k, s)
  requires io.initialized()
  requires ref in s.cache.I()
  requires io !in s.Repr()
  modifies s.Repr()
  modifies io
  ensures WellUpdated(s)
  ensures s.ready
  ensures ImplModelSync.TryToWriteBlock(Ic(k), old(s.I()), old(IIO(io)), ref, s.I(), IIO(io))
  {
    var nodeOpt := s.cache.GetOpt(ref);
    var node := nodeOpt.value;

    assert node.I() == s.cache.I()[ref];
    var id, loc := FindLocationAndRequestWrite(io, s, SectorBlock(node));

    if (id.Some?) {
      IM.reveal_ConsistentBitmap();

      AssignRefToLocEphemeral(k, s, ref, loc.value);
      AssignRefToLocFrozen(k, s, ref, loc.value);
      AssignIdRefLocOutstanding(k, s, id.value, ref, loc.value);
    } else {
      print "sync: giving up; write req failed\n";
    }

    assert ImplModelIO.FindLocationAndRequestWrite(old(IIO(io)), old(s.I()), old(IM.SectorBlock(s.cache.I()[ref])), id, loc, IIO(io));
    assert ImplModelSync.WriteBlockUpdateState(Ic(k), old(s.I()), ref, id, loc, s.I());
  }

  // TODO fix the name of this method
  method {:fuel BC.GraphClosed,0} syncFoundInFrozen(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: Reference)
  requires io.initialized()
  requires Inv(k, s)
  requires s.ready
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable != null
  requires ref in s.frozenIndirectionTable.I().graph
  requires ref !in s.frozenIndirectionTable.I().locs
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures ImplModelSync.syncFoundInFrozen(Ic(k), old(s.I()), old(IIO(io)), ref, s.I(), IIO(io))
  {
    assert ref in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable)).graph;
    assert ref !in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable)).locs;

    var ephemeralRef := s.ephemeralIndirectionTable.GetEntry(ref);
    if ephemeralRef.Some? && ephemeralRef.value.loc.Some? {
      // TODO we should be able to prove this is impossible as well
      print "sync: giving up; ref already in ephemeralIndirectionTable.locs but not frozen";
      return;
    }

    TryToWriteBlock(k, s, io, ref);
  }

  method {:fuel BC.GraphClosed,0} sync(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (wait: bool)
  requires Inv(k, s)
  requires io.initialized()
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures ImplModelSync.sync(Ic(k), old(s.I()), old(IIO(io)), s.I(), IIO(io))
  {
    ImplModelSync.reveal_sync();
    wait := false;

    if (!s.ready) {
      // TODO we could just do nothing here instead
      PageInIndirectionTableReq(k, s, io);
      return;
    }

    if (s.outstandingIndirectionTableWrite.Some?) {
      //print "sync: waiting; frozen table is currently being written\n";
      wait := true;
      return;
    }

    if (s.frozenIndirectionTable == null) {
      syncNotFrozen(k, s, io);
      return;
    }

    NativeBenchmarking.start("FindRefInFrozenWithNoLoc");
    var foundInFrozen := FindRefInFrozenWithNoLoc(s);
    NativeBenchmarking.end("FindRefInFrozenWithNoLoc");

    ImplModelSync.FindRefInFrozenWithNoLocCorrect(s.I());

    if foundInFrozen.Some? {
      syncFoundInFrozen(k, s, io, foundInFrozen.value);
      return;
    } else if (s.outstandingBlockWrites != map[]) {
      //print "sync: waiting; blocks are still being written\n";
      wait := true;
      return;
    } else {
      var id := RequestWrite(io, BC.IndirectionTableLocation(), SectorIndirectionTable(s.frozenIndirectionTable));
      if (id.Some?) {
        s.outstandingIndirectionTableWrite := id;
        return;
      } else {
        print "sync: giving up; write back indirection table failed (no id)\n";
        return;
      }
    }
  }

  // == pushSync ==

  method freeId<A>(syncReqs: MutableMap.ResizingHashMap<A>) returns (id: uint64)
  requires syncReqs.Inv()
  ensures id == ImplModelSync.freeId(syncReqs.I())
  {
    ImplModelSync.reveal_freeId();
    var maxId := syncReqs.MaxKey();
    if maxId == 0xffff_ffff_ffff_ffff {
      return 0;
    } else {
      return maxId + 1;
    }
  }

  method pushSync(k: ImplConstants, s: ImplVariables)
  returns (id: uint64)
  requires Inv(k, s)
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), id) == ImplModelSync.pushSync(Ic(k), old(s.I()))
  {
    id := freeId(s.syncReqs);
    if id != 0 && s.syncReqs.Count < 0x2000_0000_0000_0000 {
      s.syncReqs.Insert(id, BC.State3);
    } else {
      id := 0;
    }
  }

  // == popSync ==

  method popSync(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, id: uint64)
  returns (wait: bool, success: bool)
  requires Inv(k, s)
  requires io.initialized()
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures ImplModelSync.popSync(Ic(k), old(s.I()), old(IIO(io)), id, s.I(), success, IIO(io))
  {
    var g := s.syncReqs.Get(id);
    if (g.Some? && g.value == BC.State1) {
      success := true;
      wait := false;
      s.syncReqs.Remove(id);
    } else {
      success := false;
      wait := sync(k, s, io);
    }
  }
}
