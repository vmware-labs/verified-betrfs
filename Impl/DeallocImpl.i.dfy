// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

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

  method Dealloc(linear inout s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  requires old_s.Inv()
  requires io.initialized()
  requires DeallocModel.deallocable(old_s.I(), ref)
  modifies io
  ensures s.W()
  ensures s.Ready?
  ensures (s.I(), IIO(io)) == DeallocModel.Dealloc(old_s.I(), old(IIO(io)), ref);
  {
    DeallocModel.reveal_Dealloc();
    var nop := false;

    if s.frozenIndirectionTable.lSome? {
      var b := s.frozenIndirectionTable.value.HasEmptyLoc(ref);
      if b {
        print "giving up; dealloc can't run because frozen isn't written";
        nop := true;
      }
    }

    if nop || BC.OutstandingRead(ref) in s.outstandingBlockReads.Values {
      print "giving up; dealloc can't dealloc because of outstanding read\n";
    } else {
      BookkeepingModel.lemmaIndirectionTableLocIndexValid(s.I(), ref);

      var oldLoc := inout s.ephemeralIndirectionTable.RemoveRef(ref);

      inout s.lru.Remove(ref);
      inout s.cache.Remove(ref);

      if oldLoc.Some? {
        inout s.blockAllocator.MarkFreeEphemeral(oldLoc.value.addr / NodeBlockSizeUint64());
      }

      ghost var s1 := s.I();
      ghost var s2 := DeallocModel.Dealloc(old_s.I(), old(IIO(io)), ref).0;

      assert s1.cache == s2.cache;
    }
  }

  method FindDeallocable(shared s: ImplVariables) returns (ref: Option<Reference>)
  requires s.WF()
  requires s.Ready?
  ensures ref == DeallocModel.FindDeallocable(s.I())
  {
    DeallocModel.reveal_FindDeallocable();
    ref := s.ephemeralIndirectionTable.FindDeallocable();
  }
}
