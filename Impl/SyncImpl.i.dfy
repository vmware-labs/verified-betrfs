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
  import opened DiskLayout
  import SyncModel
  import BookkeepingModel
  import DeallocModel
  import BlockAllocatorModel
  import opened DiskOpImpl
  import opened StateImpl
  import opened MainDiskIOHandler

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes

  method AssignRefToLocEphemeral(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, loc: Location)
  requires s.W()
  requires s.ready
  requires BlockAllocatorModel.Inv(s.blockAllocator.I())
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
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
      s.blockAllocator.MarkUsedEphemeral(loc.addr / NodeBlockSizeUint64());
    }
  }

  method AssignRefToLocFrozen(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, loc: Location)
  requires s.W()
  requires s.ready
  requires s.I().frozenIndirectionTable.Some? ==> s.I().blockAllocator.frozen.Some?
  requires BlockAllocatorModel.Inv(s.blockAllocator.I())
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
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
        s.blockAllocator.MarkUsedFrozen(loc.addr / NodeBlockSizeUint64());
      }
    }
  }

  method AssignIdRefLocOutstanding(k: ImplConstants, s: ImplVariables, id: D.ReqId, ref: BT.G.Reference, loc: Location)
  requires s.W()
  requires s.ready
  requires BlockAllocatorModel.Inv(s.I().blockAllocator)
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  modifies s.Repr()
  ensures s.W()
  ensures WellUpdated(s)
  ensures s.I() == SyncModel.AssignIdRefLocOutstanding(Ic(k), old(s.I()), id, ref, loc)
  ensures s.ready
  {
    SyncModel.reveal_AssignIdRefLocOutstanding();

    if id in s.outstandingBlockWrites && s.outstandingBlockWrites[id].loc.addr / NodeBlockSizeUint64() < NumBlocksUint64() {
      s.blockAllocator.MarkFreeOutstanding(s.outstandingBlockWrites[id].loc.addr / NodeBlockSizeUint64());
    }
    s.outstandingBlockWrites := s.outstandingBlockWrites[id := BC.OutstandingWrite(ref, loc)];
    s.blockAllocator.MarkUsedOutstanding(loc.addr / NodeBlockSizeUint64());
  }

  method {:fuel BC.GraphClosed,0} {:fuel BC.CacheConsistentWithSuccessors,0}
  maybeFreeze(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (froze: bool)
  requires io.initialized()
  modifies io
  requires Inv(k, s)
  requires s.ready
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable == null
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), IIO(io), froze) == SyncModel.maybeFreeze(
      Ic(k), old(s.I()), old(IIO(io)))
  {
    var foundDeallocable := FindDeallocable(s);
    DeallocModel.FindDeallocableCorrect(s.I());
    if foundDeallocable.Some? {
      Dealloc(k, s, io, foundDeallocable.value);
      return false;
    }

    var clonedEphemeralIndirectionTable := s.ephemeralIndirectionTable.Clone();

    s.frozenIndirectionTable := clonedEphemeralIndirectionTable;
    s.blockAllocator.CopyEphemeralToFrozen();

    return true;
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
    var id, loc := FindLocationAndRequestWrite(io, s, SectorNode(node));

    if (id.Some?) {
      SM.reveal_ConsistentBitmap();

      AssignRefToLocEphemeral(k, s, ref, loc.value);
      AssignRefToLocFrozen(k, s, ref, loc.value);
      AssignIdRefLocOutstanding(k, s, id.value, ref, loc.value);
    } else {
      print "sync: giving up; write req failed\n";
    }

    assert IOModel.FindLocationAndRequestWrite(old(IIO(io)), old(s.I()), old(SM.SectorNode(s.cache.I()[ref])), id, loc, IIO(io));
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
  returns (froze: bool, wait: bool)
  requires Inv(k, s)
  requires io.initialized()
  requires io !in s.Repr()
  requires s.ready
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures SyncModel.sync(Ic(k), old(s.I()), old(IIO(io)), s.I(), IIO(io), froze)
  {
    SyncModel.reveal_sync();
    wait := false;
    froze := false;

    if s.frozenIndirectionTableLoc.Some? {
      //print "sync: waiting; frozen table is currently being written\n";
      wait := true;
      return;
    }

    if (s.frozenIndirectionTable == null) {
      froze := maybeFreeze(k, s, io);
      return;
    }
    var foundInFrozen := s.frozenIndirectionTable.FindRefWithNoLoc();

    assert Inv(k, s) by { StateModel.reveal_ConsistentBitmap(); }

    if foundInFrozen.Some? {
      syncFoundInFrozen(k, s, io, foundInFrozen.value);
      return;
    } else if (s.outstandingBlockWrites != map[]) {
      //print "sync: waiting; blocks are still being written\n";
      wait := true;
      return;
    } else {
      var id, loc := FindIndirectionTableLocationAndRequestWrite(
          io, s, SectorIndirectionTable(s.frozenIndirectionTable));
    
      if (id.Some?) {
        s.outstandingIndirectionTableWrite := id;
        s.frozenIndirectionTableLoc := loc;

        return;
      } else {
        print "sync: giving up; write back indirection table failed (no id)\n";
        return;
      }
    }
  }
}
