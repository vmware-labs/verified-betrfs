include "IOImpl.i.dfy"
include "DeallocImpl.i.dfy"
include "SyncModel.i.dfy"
include "BookkeepingModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sets.i.dfy"

// See dependency graph in MainHandlers.dfy

module SyncImpl { 
  import opened NodeImpl
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
  import opened MainDiskIOHandler

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets
  import opened BucketsLib
  import opened NativeTypes

  import opened StateBCImpl
  import opened StateSectorImpl
  import SBCM = StateBCModel
  import SSM = StateSectorModel

  method AssignRefToLocEphemeral(s: ImplVariables, ref: BT.G.Reference, loc: Location)
  requires s.W()
  requires s.ready
  requires BlockAllocatorModel.Inv(s.blockAllocator.I())
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  modifies s.Repr()
  ensures s.W()
  ensures WellUpdated(s)
  ensures s.I() == SyncModel.AssignRefToLocEphemeral(old(s.I()), ref, loc)
  ensures s.ready
  {
    SyncModel.reveal_AssignRefToLocEphemeral();

    var table := s.ephemeralIndirectionTable;
    var added := table.AddLocIfPresent(ref, loc);
    if added {
      s.blockAllocator.MarkUsedEphemeral(loc.addr / NodeBlockSizeUint64());
    }
  }

  method AssignRefToLocFrozen(s: ImplVariables, ref: BT.G.Reference, loc: Location)
  requires s.W()
  requires s.ready
  requires s.I().frozenIndirectionTable.Some? ==> s.I().blockAllocator.frozen.Some?
  requires BlockAllocatorModel.Inv(s.blockAllocator.I())
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  modifies s.Repr()
  ensures s.W()
  ensures WellUpdated(s)
  ensures s.I() == SyncModel.AssignRefToLocFrozen(old(s.I()), ref, loc)
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

  method AssignIdRefLocOutstanding(s: ImplVariables, id: D.ReqId, ref: BT.G.Reference, loc: Location)
  requires s.W()
  requires s.ready
  requires BlockAllocatorModel.Inv(s.I().blockAllocator)
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  modifies s.Repr()
  ensures s.W()
  ensures WellUpdated(s)
  ensures s.I() == SyncModel.AssignIdRefLocOutstanding(old(s.I()), id, ref, loc)
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
  maybeFreeze(s: ImplVariables, io: DiskIOHandler)
  returns (froze: bool)
  requires io.initialized()
  modifies io
  requires Inv(s)
  requires s.ready
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable == null
  requires io !in s.Repr()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), IIO(io), froze) == SyncModel.maybeFreeze(
      old(s.I()), old(IIO(io)))
  {
    var foundDeallocable := FindDeallocable(s);
    DeallocModel.FindDeallocableCorrect(s.I());
    if foundDeallocable.Some? {
      Dealloc(s, io, foundDeallocable.value);
      return false;
    }

    var clonedEphemeralIndirectionTable := s.ephemeralIndirectionTable.Clone();

    s.frozenIndirectionTable := clonedEphemeralIndirectionTable;
    s.blockAllocator.CopyEphemeralToFrozen();

    return true;
  }

  method TryToWriteBlock(s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  requires s.ready
  requires Inv(s)
  requires io.initialized()
  requires ref in s.cache.I()
  requires io !in s.Repr()
  modifies s.Repr()
  modifies io
  ensures WellUpdated(s)
  ensures s.ready
  ensures SyncModel.TryToWriteBlock(old(s.I()), old(IIO(io)), ref, s.I(), IIO(io))
  {
    linear var placeholder := Node.EmptyNode();
    linear var node := s.cache.ReplaceAndGet(ref, placeholder);
    linear var sector := SectorNode(node);
  
    assert |s.cache.I()| <= 0x10000;
    assert s.cache.ptr(ref).Some?;
    
    var id, loc := FindLocationAndRequestWrite(io, s, sector);
    ghost var s' := s.I();

    linear var SectorNode(n) := sector;
    linear var replaced:= s.cache.ReplaceAndGet(ref, n);
    var _ := FreeNode(replaced);

    assert IOModel.SimilarVariables(s', s.I());
    IOModel.SimilarVariablesGuarantees(old(IIO(io)), s', old(s.I()),
      old(SSM.SectorNode(s.cache.I()[ref])), id, loc, IIO(io));
    assert s.cache.I() == old(s.cache.I());

    if (id.Some?) {
      SBCM.reveal_ConsistentBitmap();

      AssignRefToLocEphemeral(s, ref, loc.value);
      AssignRefToLocFrozen(s, ref, loc.value);
      AssignIdRefLocOutstanding(s, id.value, ref, loc.value);
    } else {
      print "sync: giving up; write req failed\n";
    }
  
    assert IOModel.FindLocationAndRequestWrite(old(IIO(io)), old(s.I()),
      old(SSM.SectorNode(s.cache.I()[ref])), id, loc, IIO(io));
    assert SyncModel.WriteBlockUpdateState(old(s.I()), ref, id, loc, s.I());
  }

  // TODO fix the name of this method
  method {:fuel BC.GraphClosed,0} syncFoundInFrozen(s: ImplVariables, io: DiskIOHandler, ref: Reference)
  requires io.initialized()
  requires Inv(s)
  requires s.ready
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable != null
  requires ref in s.frozenIndirectionTable.I().graph
  requires ref !in s.frozenIndirectionTable.I().locs
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures SyncModel.syncFoundInFrozen(old(s.I()), old(IIO(io)), ref, s.I(), IIO(io))
  {
    assert ref in s.frozenIndirectionTable.I().graph;
    assert ref !in s.frozenIndirectionTable.I().locs;

    var ephemeralRef := s.ephemeralIndirectionTable.GetEntry(ref);
    if ephemeralRef.Some? && ephemeralRef.value.loc.Some? {
      // TODO we should be able to prove this is impossible as well
      print "sync: giving up; ref already in ephemeralIndirectionTable.locs but not frozen";
      return;
    }

    TryToWriteBlock(s, io, ref);
  }

  method {:fuel BC.GraphClosed,0} sync(s: ImplVariables, io: DiskIOHandler)
  returns (froze: bool, wait: bool)
  requires Inv(s)
  requires io.initialized()
  requires io !in s.Repr()
  requires s.ready
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures SyncModel.sync(old(s.I()), old(IIO(io)), s.I(), IIO(io), froze)
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
      froze := maybeFreeze(s, io);
      return;
    }
    var foundInFrozen := s.frozenIndirectionTable.FindRefWithNoLoc();

    assert Inv(s) by { SBCM.reveal_ConsistentBitmap(); }

    if foundInFrozen.Some? {
      syncFoundInFrozen(s, io, foundInFrozen.value);
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
