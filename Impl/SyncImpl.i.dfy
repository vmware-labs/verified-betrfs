// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

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
  import opened LinearOption
  import opened Maps
  import opened Sequences
  import opened Sets
  import opened BucketsLib
  import opened NativeTypes

  import opened StateBCImpl
  import opened StateSectorImpl
  import SBCM = StateBCModel
  import SSM = StateSectorModel
  import opened DiskOpModel
  import IOModel

  method AssignRefToLocEphemeral(linear inout s: ImplVariables, ref: BT.G.Reference, loc: Location)
  requires old_s.W()
  requires old_s.Ready?
  requires BlockAllocatorModel.Inv(old_s.blockAllocator.I())
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()

  ensures s.W()
  ensures s.I() == SyncModel.AssignRefToLocEphemeral(old_s.I(), ref, loc)
  ensures s.Ready?
  {
    SyncModel.reveal_AssignRefToLocEphemeral();

    var added := inout s.ephemeralIndirectionTable.AddLocIfPresent(ref, loc);
    if added {
      inout s.blockAllocator.MarkUsedEphemeral(loc.addr / NodeBlockSizeUint64());
    }
  }

  method AssignRefToLocFrozen(linear inout s: ImplVariables, ref: BT.G.Reference, loc: Location)
  requires old_s.W()
  requires old_s.Ready?
  requires old_s.I().frozenIndirectionTable.Some? ==> old_s.I().blockAllocator.frozen.Some?
  requires BlockAllocatorModel.Inv(old_s.blockAllocator.I())
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()

  ensures s.W()
  ensures s.I() == SyncModel.AssignRefToLocFrozen(old_s.I(), ref, loc)
  ensures s.Ready?
  {
    SyncModel.reveal_AssignRefToLocFrozen();

    if s.frozenIndirectionTable.lSome? {
      var added := inout s.frozenIndirectionTable.value.AddLocIfPresent(ref, loc);
      if added {
        inout s.blockAllocator.MarkUsedFrozen(loc.addr / NodeBlockSizeUint64());
      }
    }
  }

  method AssignIdRefLocOutstanding(linear inout s: ImplVariables, id: D.ReqId, ref: BT.G.Reference, loc: Location)
  requires old_s.W()
  requires old_s.Ready?
  requires BlockAllocatorModel.Inv(old_s.I().blockAllocator)
  requires 0 <= loc.addr as int / NodeBlockSize() < NumBlocks()
  ensures s.W()
  ensures s.I() == SyncModel.AssignIdRefLocOutstanding(old_s.I(), id, ref, loc)
  ensures s.Ready?
  {
    SyncModel.reveal_AssignIdRefLocOutstanding();

    if id in s.outstandingBlockWrites {
      var numBlocks := s.outstandingBlockWrites[id].loc.addr / NodeBlockSizeUint64();
      if numBlocks < NumBlocksUint64() {
        inout s.blockAllocator.MarkFreeOutstanding(numBlocks);
      }
    }
    inout s.outstandingBlockWrites := s.outstandingBlockWrites[id := BC.OutstandingWrite(ref, loc)];
    inout s.blockAllocator.MarkUsedOutstanding(loc.addr / NodeBlockSizeUint64());
  }

  method {:fuel BC.GraphClosed,0} {:fuel BC.CacheConsistentWithSuccessors,0}
  maybeFreeze(linear inout s: ImplVariables, io: DiskIOHandler)
  returns (froze: bool)
  requires io.initialized()
  requires old_s.Inv()
  requires old_s.Ready?
  requires old_s.outstandingIndirectionTableWrite.None?
  requires old_s.frozenIndirectionTable.lNone?

  modifies io

  ensures s.W()
  ensures (s.I(), IIO(io), froze) == SyncModel.maybeFreeze(
      old_s.I(), old(IIO(io)))
  {
    var foundDeallocable := FindDeallocable(s);
    DeallocModel.FindDeallocableCorrect(s.I());
    if foundDeallocable.Some? {
      Dealloc(inout s, io, foundDeallocable.value);
      froze := false;
    } else {
      // [yizhou7]: is there a better way to perfrom this kind of assignment?
      linear var Ready(
        persistentIndirectionTable,
        frozenIndirectionTable,
        ephemeralIndirectionTable,
        persistentIndirectionTableLoc,
        frozenIndirectionTableLoc,
        outstandingIndirectionTableWrite,
        outstandingBlockWrites,
        outstandingBlockReads,
        cache,
        lru,
        blockAllocator) := s;

      linear var clonedEphemeralIndirectionTable := ephemeralIndirectionTable.Clone();
      dispose_lnone(frozenIndirectionTable);
      frozenIndirectionTable := lSome(clonedEphemeralIndirectionTable);

      s := Ready(
        persistentIndirectionTable,
        frozenIndirectionTable,
        ephemeralIndirectionTable,
        persistentIndirectionTableLoc,
        frozenIndirectionTableLoc,
        outstandingIndirectionTableWrite,
        outstandingBlockWrites,
        outstandingBlockReads,
        cache,
        lru,
        blockAllocator);

      inout s.blockAllocator.CopyEphemeralToFrozen();
      froze := true;
    }
  }

  method TryToWriteBlock(linear inout s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  requires old_s.Ready?
  requires old_s.Inv()
  requires io.initialized()
  requires ref in old_s.cache.I()
  modifies io
  ensures s.W()
  ensures s.Ready?
  ensures SyncModel.TryToWriteBlock(old_s.I(), old(IIO(io)), ref, s.I(), IIO(io))
  {
    linear var placeholder := Node.EmptyNode();
    linear var node := inout s.cache.ReplaceAndGet(ref, placeholder);
    linear var sector := SectorNode(node);
  
    assert |s.cache.I()| <= 0x10000;
    assert s.cache.ptr(ref).Some?;
    
    var id, loc := FindLocationAndRequestWrite(io, s, sector);
    ghost var s' := s.I();

    linear var SectorNode(n) := sector;
    linear var replaced:= inout s.cache.ReplaceAndGet(ref, n);
    var _ := FreeNode(replaced);

    assert IOModel.SimilarVariables(s', s.I());
    IOModel.SimilarVariablesGuarantees(old(IIO(io)), s', old_s.I(),
      SSM.SectorNode(old_s.cache.I()[ref]), id, loc, IIO(io));
    assert s.cache.I() == old_s.cache.I();

    if (id.Some?) {
      SBCM.reveal_ConsistentBitmap();

      AssignRefToLocEphemeral(inout s, ref, loc.value);
      AssignRefToLocFrozen(inout s, ref, loc.value);
      AssignIdRefLocOutstanding(inout s, id.value, ref, loc.value);
    } else {
      print "sync: giving up; write req failed\n";
    }
  
    assert IOModel.FindLocationAndRequestWrite(old(IIO(io)), old_s.I(),
      SSM.SectorNode(old_s.cache.I()[ref]), id, loc, IIO(io));
    assert SyncModel.WriteBlockUpdateState(old_s.I(), ref, id, loc, s.I());
  }

  // TODO fix the name of this method
  method {:fuel BC.GraphClosed,0} syncFoundInFrozen(linear inout s: ImplVariables, io: DiskIOHandler, ref: Reference)
  requires io.initialized()
  requires old_s.Inv()
  requires old_s.Ready?
  requires old_s.outstandingIndirectionTableWrite.None?
  requires old_s.frozenIndirectionTable.lSome?
  requires ref in old_s.frozenIndirectionTable.value.I().graph
  requires ref !in old_s.frozenIndirectionTable.value.I().locs
  modifies io
  ensures s.W()
  ensures SyncModel.syncFoundInFrozen(old_s.I(), old(IIO(io)), ref, s.I(), IIO(io))
  {
    assert ref in s.frozenIndirectionTable.value.I().graph;
    assert ref !in s.frozenIndirectionTable.value.I().locs;

    var ephemeralRef := s.ephemeralIndirectionTable.GetEntry(ref);
    if ephemeralRef.Some? && ephemeralRef.value.loc.Some? {
      // TODO we should be able to prove this is impossible as well
      print "sync: giving up; ref already in ephemeralIndirectionTable.locs but not frozen";
    } else {
      TryToWriteBlock(inout s, io, ref);
    }
  }

  method {:fuel BC.GraphClosed,0} sync(linear inout s: ImplVariables, io: DiskIOHandler)
  returns (froze: bool, wait: bool)
  requires old_s.Inv()
  requires io.initialized()
  requires old_s.Ready?
  modifies io
  ensures s.W()
  ensures SyncModel.sync(old_s.I(), old(IIO(io)), s.I(), IIO(io), froze)
  {
    SyncModel.reveal_sync();
    wait := false;
    froze := false;

    if s.frozenIndirectionTableLoc.Some? {
      //print "sync: waiting; frozen table is currently being written\n";
      wait := true;
    } else if s.frozenIndirectionTable.lNone? {
      froze := maybeFreeze(inout s, io);
    } else {
      var foundInFrozen := inout s.frozenIndirectionTable.value.FindRefWithNoLoc();
      ghost var s0 := s;

      assert s0.Inv() by { SBCM.reveal_ConsistentBitmap(); }

      if foundInFrozen.Some? {
        syncFoundInFrozen(inout s, io, foundInFrozen.value);
      } else if (s.outstandingBlockWrites != map[]) {
        //print "sync: waiting; blocks are still being written\n";
        wait := true;
      } else {
        var id, loc := FindIndirectionTableLocationAndRequestWrite(
            io, s, SectorIndirectionTable(s.frozenIndirectionTable.value));

        if id.Some? {
          // assume IOModel.FindIndirectionTableLocationAndRequestWrite(
          //   IIO(old(io)), s0.I(), SSM.SectorIndirectionTable(s0.I().frozenIndirectionTable.value), id, loc, IIO(io));
          inout s.outstandingIndirectionTableWrite := id;
          inout s.frozenIndirectionTableLoc := loc;
        } else {
          print "sync: giving up; write back indirection table failed (no id)\n";
        }
      }
    }
  }
}
