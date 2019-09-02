include "Impl.i.dfy"
include "ImplIO.i.dfy"
include "ImplDealloc.i.dfy"
include "ImplModelSync.i.dfy"
include "ImplModelCache.i.dfy"
include "ImplFlushRootBucket.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Option.s.dfy"
include "../lib/Sets.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplSync { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache
  import opened ImplDealloc
  import opened ImplFlushRootBucket
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
  requires WFVars(s)
  requires s.Ready?
  requires s.frozenIndirectionTable.Some?
  ensures ref == ImplModelSync.FindRefInFrozenWithNoLoc(IVars(s))
  {
    assume false;
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var frozenTable := s.frozenIndirectionTable.value.ToMap();
    var frozenRefs := SetToSeq(frozenTable.Keys);

    assume |frozenRefs| < 0x1_0000_0000_0000_0000;

    var i: uint64 := 0;
    while i as int < |frozenRefs|
    invariant i as int <= |frozenRefs|
    invariant forall k : nat | k < i as nat :: (
        && frozenRefs[k] in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable.value)).graph
        && frozenRefs[k] in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable.value)).locs)
    {
      var ref := frozenRefs[i];
      var lbaGraph := s.frozenIndirectionTable.value.Get(ref);
      assert lbaGraph.Some?;
      var (lba, _) := lbaGraph.value;
      if lba.None? {
        return Some(ref);
      }
      i := i + 1;
    }
    assert forall r | r in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable.value)).graph
        :: r in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable.value)).locs;
    return None;
  }

  method {:fuel BC.GraphClosed,0} {:fuel BC.CacheConsistentWithSuccessors,0}
  syncNotFrozen(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.initialized()
  modifies io
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.rootBucket == TTT.EmptyTree
  requires s.frozenIndirectionTable.None?
  ensures WVars(s')
  ensures (IVars(s'), IIO(io)) == ImplModelSync.syncNotFrozen(Ic(k), old(IVars(s)), old(IIO(io)))
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s.Ready? ==> forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  {
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralGraph := map k | k in ephemeralTable :: ephemeralTable[k].1;
    var foundDeallocable := FindDeallocable(s);
    ImplModelDealloc.FindDeallocableCorrect(IVars(s));
    if foundDeallocable.Some? {
      s' := Dealloc(k, s, io, foundDeallocable.value);
      return;
    }

    var clonedEphemeralIndirectionTable := s.ephemeralIndirectionTable.Clone();

    s' := s
        .(frozenIndirectionTable := Some(clonedEphemeralIndirectionTable))
        .(syncReqs := BC.syncReqs3to2(s.syncReqs));

    return;
  }

  method TryToWriteBlock(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  returns (s': ImplVariables)
  requires s.Ready?
  requires Inv(k, s)
  requires io.initialized()
  requires ref in s.cache
  ensures WVars(s')
  ensures ImplModelSync.TryToWriteBlock(Ic(k), old(IVars(s)), old(IIO(io)), ref, IVars(s'), IIO(io))
  ensures s.Ready? ==> forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  modifies if s.Ready? && s.frozenIndirectionTable.Some? then s.frozenIndirectionTable.value.Repr else {}
  modifies io
  {
    var id, loc := FindLocationAndRequestWrite(io, s, SectorBlock(s.cache[ref]));

    if (id.Some?) {
      AssignRefToLoc(s.ephemeralIndirectionTable, ref, loc.value);
      if (s.frozenIndirectionTable.Some?) {
        AssignRefToLoc(s.frozenIndirectionTable.value, ref, loc.value);
      }
      s' := s
        .(outstandingBlockWrites := s.outstandingBlockWrites[id.value := BC.OutstandingWrite(ref, loc.value)]);
    } else {
      s' := s;
      print "sync: giving up; write req failed\n";
    }

    assert ImplModelIO.FindLocationAndRequestWrite(old(IIO(io)), old(IVars(s)), ISector(SectorBlock(s.cache[ref])), id, loc, IIO(io));
    assert ImplModelSync.WriteBlockUpdateState(Ic(k), old(IVars(s)), ref, id, loc, IVars(s'));
  }

  // TODO fix the name of this method
  method {:fuel BC.GraphClosed,0} syncFoundInFrozen(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: Reference)
  returns (s': ImplVariables)
  requires io.initialized()
  modifies io
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.rootBucket == TTT.EmptyTree
  requires s.frozenIndirectionTable.Some?
  requires ref in s.frozenIndirectionTable.value.Contents
  requires s.frozenIndirectionTable.value.Contents[ref].0.None?
  ensures WVars(s')
  ensures ImplModelSync.syncFoundInFrozen(Ic(k), old(IVars(s)), old(IIO(io)), ref, IVars(s'), IIO(io))
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s.Ready? ==> forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  modifies if s.Ready? then s.frozenIndirectionTable.value.Repr else {}
  {
    assert ref in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable.value)).graph;
    assert ref !in IM.IIndirectionTable(IIndirectionTable(s.frozenIndirectionTable.value)).locs;

    var ephemeralRef := s.ephemeralIndirectionTable.Get(ref);
    if ephemeralRef.Some? && ephemeralRef.value.0.Some? {
      // TODO we should be able to prove this is impossible as well
      s' := s;
      print "sync: giving up; ref already in ephemeralIndirectionTable.locs but not frozen";
      return;
    }

    s' := TryToWriteBlock(k, s, io, ref);
  }

  method {:fuel BC.GraphClosed,0} sync(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires io.initialized()
  modifies io
  requires Inv(k, s)
  ensures WVars(s')
  ensures ImplModelSync.sync(Ic(k), old(IVars(s)), old(IIO(io)), IVars(s'), IIO(io))
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s.Ready? ==> forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  modifies if s.Ready? && s.frozenIndirectionTable.Some? then s.frozenIndirectionTable.value.Repr else {}
  {
    ImplModelSync.reveal_sync();

    if (s.Unready?) {
      // TODO we could just do nothing here instead
      s' := PageInIndirectionTableReq(k, s, io);
      return;
    }

    if (s.outstandingIndirectionTableWrite.Some?) {
      s' := s;
      print "sync: giving up; frozen table is currently being written\n";
      return;
    }

    if (s.rootBucket != TTT.EmptyTree) {
      s' := flushRootBucket(k, s);
      return;
    }

    if (s.frozenIndirectionTable.None?) {
      s' := syncNotFrozen(k, s, io);
      return;
    }
    var foundInFrozen := FindRefInFrozenWithNoLoc(s);
    ImplModelSync.FindRefInFrozenWithNoLocCorrect(IVars(s));

    if foundInFrozen.Some? {
      s' := syncFoundInFrozen(k, s, io, foundInFrozen.value);
      return;
    } else if (s.outstandingBlockWrites != map[]) {
      s' := s;
      print "sync: giving up; blocks are still being written\n";
      return;
    } else {
      var id := RequestWrite(io, BC.IndirectionTableLocation(), SectorIndirectionTable(s.frozenIndirectionTable.value));
      if (id.Some?) {
        s' := s.(outstandingIndirectionTableWrite := id);
        return;
      } else {
        s' := s;
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
  returns (s': ImplVariables, id: int)
  requires Inv(k, s)
  ensures WVars(s')
  ensures (IVars(s'), id) == ImplModelSync.pushSync(Ic(k), old(IVars(s)))
  {
    id := freeId(s.syncReqs);
    s' := s.(syncReqs := s.syncReqs[id := BC.State3]);
  }

  // == popSync ==

  method popSync(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, id: int)
  returns (s': ImplVariables, success: bool)
  requires io.initialized()
  requires Inv(k, s)
  modifies io
  ensures WVars(s')
  ensures ImplModelSync.popSync(Ic(k), old(IVars(s)), old(IIO(io)), id, IVars(s'), success, IIO(io))
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s.Ready? ==> forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  modifies if s.Ready? && s.frozenIndirectionTable.Some? then s.frozenIndirectionTable.value.Repr else {}
  {
    if (id in s.syncReqs && s.syncReqs[id] == BC.State1) {
      success := true;
      s' := s.(syncReqs := MapRemove1(s.syncReqs, id));
    } else {
      success := false;
      s' := sync(k, s, io);
    }
  }
}
