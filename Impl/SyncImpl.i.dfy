include "IOImpl.i.dfy"
include "DeallocImpl.i.dfy"
include "SyncModel.i.dfy"
include "BookkeepingModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"

// See dependency graph in MainHandlers.dfy

module SyncImpl { 
  import opened IOImpl
  import opened BookkeepingImpl
  import opened DeallocImpl
  import opened Bounds
  import SyncModel
  import BookkeepingModel
  import DeallocModel
  import BlockAllocatorModel
  import opened StateImpl

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes

  method AssignRefToLocEphemeral(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, loc: BC.Location)
  requires s.W()
  requires s.ready
  requires BlockAllocatorModel.Inv(s.blockAllocator.I())
  requires 0 <= loc.addr as int / BlockSize() < NumBlocks()
  modifies s.Repr()
  ensures s.W()
  ensures WellUpdated(s)
  ensures s.I() == SyncModel.AssignRefToLocEphemeral(Ic(k), old(s.I()), ref, loc)
  ensures s.ready
  {
    SyncModel.reveal_AssignRefToLocEphemeral();

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
  requires BlockAllocatorModel.Inv(s.blockAllocator.I())
  requires 0 <= loc.addr as int / BlockSize() < NumBlocks()
  modifies s.Repr()
  ensures s.W()
  ensures WellUpdated(s)
  ensures s.I() == SyncModel.AssignRefToLocFrozen(Ic(k), old(s.I()), ref, loc)
  ensures s.ready
  {
    SyncModel.reveal_AssignRefToLocFrozen();

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
  requires BlockAllocatorModel.Inv(s.I().blockAllocator)
  requires 0 <= loc.addr as int / BlockSize() < NumBlocks()
  modifies s.Repr()
  ensures s.W()
  ensures WellUpdated(s)
  ensures s.I() == SyncModel.AssignIdRefLocOutstanding(Ic(k), old(s.I()), id, ref, loc)
  ensures s.ready
  {
    SyncModel.reveal_AssignIdRefLocOutstanding();

    s.outstandingBlockWrites := s.outstandingBlockWrites[id := BC.OutstandingWrite(ref, loc)];
    s.blockAllocator.MarkUsedOutstanding(loc.addr / BlockSizeUint64());
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
  ensures (s.I(), IIO(io)) == SyncModel.syncNotFrozen(Ic(k), old(s.I()), old(IIO(io)))
  {
    var foundDeallocable := FindDeallocable(s);
    DeallocModel.FindDeallocableCorrect(s.I());
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
  ensures SyncModel.TryToWriteBlock(Ic(k), old(s.I()), old(IIO(io)), ref, s.I(), IIO(io))
  {
    var nodeOpt := s.cache.GetOpt(ref);
    var node := nodeOpt.value;

    assert node.I() == s.cache.I()[ref];
    var id, loc := FindLocationAndRequestWrite(io, s, SectorBlock(node));

    if (id.Some?) {
      SM.reveal_ConsistentBitmap();

      AssignRefToLocEphemeral(k, s, ref, loc.value);
      AssignRefToLocFrozen(k, s, ref, loc.value);
      AssignIdRefLocOutstanding(k, s, id.value, ref, loc.value);
    } else {
      print "sync: giving up; write req failed\n";
    }

    assert IOModel.FindLocationAndRequestWrite(old(IIO(io)), old(s.I()), old(SM.SectorBlock(s.cache.I()[ref])), id, loc, IIO(io));
    assert SyncModel.WriteBlockUpdateState(Ic(k), old(s.I()), ref, id, loc, s.I());
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
  ensures SyncModel.syncFoundInFrozen(Ic(k), old(s.I()), old(IIO(io)), ref, s.I(), IIO(io))
  {
    assert ref in SM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable)).graph;
    assert ref !in SM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable)).locs;

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
  ensures SyncModel.sync(Ic(k), old(s.I()), old(IIO(io)), s.I(), IIO(io))
  {
    SyncModel.reveal_sync();
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
    var foundInFrozen := s.frozenIndirectionTable.FindRefWithNoLoc();

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
  ensures id == SyncModel.freeId(syncReqs.I())
  {
    SyncModel.reveal_freeId();
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
  ensures (s.I(), id) == SyncModel.pushSync(Ic(k), old(s.I()))
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
  ensures SyncModel.popSync(Ic(k), old(s.I()), old(IIO(io)), id, s.I(), success, IIO(io))
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
