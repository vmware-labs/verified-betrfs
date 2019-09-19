include "Impl.i.dfy"
include "ImplIO.i.dfy"
include "ImplDealloc.i.dfy"
include "ImplModelSync.i.dfy"
include "ImplModelCache.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Option.s.dfy"
include "../lib/Sets.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplSync { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache
  import opened ImplDealloc
  import ImplModelSync
  import ImplModelCache
  import ImplModelDealloc
  import opened ImplState

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes

  method AssignRefToLoc(table: MutIndirectionTable, ref: Reference, loc: BC.Location)
  requires table.Inv()
  ensures table.Inv()
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in table.Repr :: fresh(r) || r in old(table.Repr)
  modifies table.Repr
  ensures table.Contents == ImplModelSync.AssignRefToLoc(old(table.Contents), ref, loc)
  {
    ImplModelSync.reveal_AssignRefToLoc();
    var locGraph := table.Get(ref);
    if locGraph.Some? {
      var (oldloc, succ) := locGraph.value;
      if oldloc.None? {
        assume table.Count as nat < 0x10000000000000000 / 8;
        var _ := table.Insert(ref, (Some(loc), succ));
      }
    }
    //assert IIndirectionTable(table) ==
    //    old(BC.assignRefToLocation(IIndirectionTable(table), ref, loc));
  }

  method FindRefInFrozenWithNoLoc(s: ImplVariables) returns (ref: Option<Reference>)
  requires s.WF()
  requires s.ready
  requires s.frozenIndirectionTable != null
  ensures ref == ImplModelSync.FindRefInFrozenWithNoLoc(s.I())
  {
    assume false;
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var frozenTable := s.frozenIndirectionTable.ToMap();
    var frozenRefs := SetToSeq(frozenTable.Keys);

    assume |frozenRefs| < 0x1_0000_0000_0000_0000;

    var i: uint64 := 0;
    while i < |frozenRefs| as uint64
    invariant i as int <= |frozenRefs|
    invariant forall k : nat | k < i as nat :: (
        && frozenRefs[k] in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable)).graph
        && frozenRefs[k] in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable)).locs)
    {
      var ref := frozenRefs[i];
      var lbaGraph := s.frozenIndirectionTable.Get(ref);
      assert lbaGraph.Some?;
      var (lba, _) := lbaGraph.value;
      if lba.None? {
        return Some(ref);
      }
      i := i + 1;
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
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralGraph := map k | k in ephemeralTable :: ephemeralTable[k].1;
    var foundDeallocable := FindDeallocable(s);
    ImplModelDealloc.FindDeallocableCorrect(s.I());
    if foundDeallocable.Some? {
      Dealloc(k, s, io, foundDeallocable.value);
      return;
    }

    var clonedEphemeralIndirectionTable := s.ephemeralIndirectionTable.Clone();

    s.frozenIndirectionTable := clonedEphemeralIndirectionTable;
    s.syncReqs := BC.syncReqs3to2(s.syncReqs);

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
      AssignRefToLoc(s.ephemeralIndirectionTable, ref, loc.value);
      if (s.frozenIndirectionTable != null) {
        AssignRefToLoc(s.frozenIndirectionTable, ref, loc.value);
      }
      s.outstandingBlockWrites := s.outstandingBlockWrites[id.value := BC.OutstandingWrite(ref, loc.value)];
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
  requires ref in s.frozenIndirectionTable.Contents
  requires s.frozenIndirectionTable.Contents[ref].0.None?
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures ImplModelSync.syncFoundInFrozen(Ic(k), old(s.I()), old(IIO(io)), ref, s.I(), IIO(io))
  {
    assert ref in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable)).graph;
    assert ref !in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable)).locs;

    var ephemeralRef := s.ephemeralIndirectionTable.Get(ref);
    if ephemeralRef.Some? && ephemeralRef.value.0.Some? {
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
    var foundInFrozen := FindRefInFrozenWithNoLoc(s);
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

  method freeId<A>(syncReqs: map<int, A>) returns (id: int)
  ensures id == ImplModelSync.freeId(syncReqs)
  {
    ImplModelSync.reveal_freeId();

    var s := syncReqs.Keys;
    if (|s| == 0) {
      id := 0;
    } else {
      var maxId := MaximumInt(syncReqs.Keys);
      id := maxId + 1;
    }
  }

  method pushSync(k: ImplConstants, s: ImplVariables)
  returns (id: int)
  requires Inv(k, s)
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures (s.I(), id) == ImplModelSync.pushSync(Ic(k), old(s.I()))
  {
    id := freeId(s.syncReqs);
    s.syncReqs := s.syncReqs[id := BC.State3];
  }

  // == popSync ==

  method popSync(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, id: int)
  returns (wait: bool, success: bool)
  requires Inv(k, s)
  requires io.initialized()
  requires io !in s.Repr()
  modifies io
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures ImplModelSync.popSync(Ic(k), old(s.I()), old(IIO(io)), id, s.I(), success, IIO(io))
  {
    if (id in s.syncReqs && s.syncReqs[id] == BC.State1) {
      success := true;
      wait := false;
      s.syncReqs := MapRemove1(s.syncReqs, id);
    } else {
      success := false;
      wait := sync(k, s, io);
    }
  }
}
