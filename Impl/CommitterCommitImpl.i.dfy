include "CommitterImpl.i.dfy"
include "CommitterCommitModel.i.dfy"
include "DiskOpImpl.i.dfy"
include "IOImpl.i.dfy"

module CommitterCommitImpl {
  import opened NativeTypes
  import opened Options

  import opened DiskLayout
  import JC = JournalCache
  import opened Journal
  import opened JournalBytes
  import opened DiskOpImpl
  import opened MainDiskIOHandler
  import opened IOImpl
  import StateImpl
  import SectorType
  import MutableMapModel

  import opened CommitterImpl
  import CommitterCommitModel

  // TODO we could have these do the modification in-place instead.

  method SyncReqs2to1(m: MutableMap.ResizingHashMap<JC.SyncReqStatus>)
  returns (m' : MutableMap.ResizingHashMap<JC.SyncReqStatus>)
  requires m.Inv()
  ensures fresh(m'.Repr)
  ensures m'.Inv()
  ensures m'.I() == CommitterCommitModel.SyncReqs2to1(m.I())
  {
    CommitterCommitModel.reveal_SyncReqs2to1();
    var it := m.IterStart();
    var m0 := new MutableMap.ResizingHashMap(128);
    while !it.next.Done?
    invariant m.Inv()
    invariant fresh(m0.Repr)
    invariant m0.Inv()
    invariant MutableMapModel.WFIter(m.I(), it)
    invariant m0.Inv()
    invariant m0.I().contents.Keys == it.s
    invariant CommitterCommitModel.SyncReqs2to1(m.I()) == CommitterCommitModel.SyncReqs2to1Iterate(m.I(), it, m0.I())

    decreases it.decreaser
    {
      MutableMapModel.LemmaIterIndexLtCount(m.I(), it);
      MutableMapModel.CountBound(m.I());
      m0.Insert(it.next.key, (if it.next.value == JC.State2 then JC.State1 else it.next.value));
      it := m.IterInc(it);
    }
    m' := m0;
  }


  method SyncReqs3to2(m: MutableMap.ResizingHashMap<JC.SyncReqStatus>)
  returns (m' : MutableMap.ResizingHashMap<JC.SyncReqStatus>)
  requires m.Inv()
  ensures fresh(m'.Repr)
  ensures m'.Inv()
  ensures m'.I() == CommitterCommitModel.SyncReqs3to2(m.I())
  {
    CommitterCommitModel.reveal_SyncReqs3to2();
    var it := m.IterStart();
    var m0 := new MutableMap.ResizingHashMap(128);
    while !it.next.Done?
    invariant m.Inv()
    invariant fresh(m0.Repr)
    invariant m0.Inv()
    invariant MutableMapModel.WFIter(m.I(), it)
    invariant m0.Inv()
    invariant m0.I().contents.Keys == it.s
    invariant CommitterCommitModel.SyncReqs3to2(m.I()) == CommitterCommitModel.SyncReqs3to2Iterate(m.I(), it, m0.I())

    decreases it.decreaser
    {
      MutableMapModel.LemmaIterIndexLtCount(m.I(), it);
      MutableMapModel.CountBound(m.I());
      m0.Insert(it.next.key, (if it.next.value == JC.State3 then JC.State2 else it.next.value));
      it := m.IterInc(it);
    }
    m' := m0;
  }

  method WriteOutJournal(k: ImplConstants, cm: Committer, io: DiskIOHandler)
  requires io.initialized()
  requires cm.Inv()
  requires JournalistModel.I(cm.I().journalist).inMemoryJournalFrozen != []
        || JournalistModel.I(cm.I().journalist).inMemoryJournal != []
  requires io !in cm.Repr
  modifies cm.Repr
  modifies io
  ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
  ensures cm.W()
  ensures (cm.I(), IIO(io)) == CommitterCommitModel.WriteOutJournal(
      Ic(k), old(cm.I()), old(IIO(io)))
  {
    CommitterCommitModel.reveal_WriteOutJournal();
    cm.reveal_ReprInv();

    var writtenJournalLen := cm.journalist.getWrittenJournalLen();
    var doingFrozen := cm.journalist.hasFrozenJournal();

    var j;
    if doingFrozen {
      j := cm.journalist.packageFrozenJournal();
    } else {
      j := cm.journalist.packageInMemoryJournal();
    }

    var start := CommitterCommitModel.start_pos_add(
        cm.superblock.journalStart,
        writtenJournalLen);

    var len := |j| as uint64 / 4096;

    var contiguous := start + len <= NumJournalBlocks();

    if contiguous {
      var id := io.write(JournalPoint(start), j);
      cm.outstandingJournalWrites := cm.outstandingJournalWrites + {id};
    } else {
      var cut := (NumJournalBlocks() - start) * 4096;
      var id1, id2 := io.write2(
          JournalPoint(start), j[..cut],
          JournalPoint(0), j[cut..]);
      cm.outstandingJournalWrites := cm.outstandingJournalWrites + {id1, id2};
    }

    if doingFrozen {
      cm.frozenJournalPosition := cm.journalist.getWrittenJournalLen();
    } else {
      cm.syncReqs := SyncReqs3to2(cm.syncReqs);
    }

    cm.Repr := {cm} + cm.syncReqs.Repr + cm.journalist.Repr;
    cm.reveal_ReprInv();

    assert (cm.I(), IIO(io)) == CommitterCommitModel.WriteOutJournal(
        Ic(k), old(cm.I()), old(IIO(io)));
  }

  method writeOutSuperblockAdvanceLog(
      k: ImplConstants, cm: Committer, io: DiskIOHandler)
  requires io.initialized()
  requires cm.Inv()
  requires io !in cm.Repr
  requires cm.status == CommitterModel.StatusReady
  modifies cm.Repr
  modifies io
  ensures cm.W()
  ensures cm.Repr == old(cm.Repr)
  ensures CommitterCommitModel.writeOutSuperblockAdvanceLog(
      Ic(k), old(cm.I()), old(IIO(io)), cm.I(), IIO(io))
  {
    //CommitterCommitModel.reveal_writeOutSuperblockAdvanceLog();
    cm.reveal_ReprInv();

    var writtenJournalLen := cm.journalist.getWrittenJournalLen();

    var newSuperblock := SectorType.Superblock(
      JC.IncrementSuperblockCounter(cm.superblock.counter),
      cm.superblock.journalStart,
      writtenJournalLen,
      cm.superblock.indirectionTableLoc
    );

    assert JC.WFSuperblock(newSuperblock);

    var loc := if cm.whichSuperblock == 0 then Superblock2Location() else Superblock1Location();
    var id := RequestWrite(io, loc,
        StateImpl.SectorSuperblock(newSuperblock));

    cm.newSuperblock := Some(newSuperblock);
    cm.superblockWrite := Some(id);
    cm.commitStatus := JC.CommitAdvanceLog;

    cm.Repr := {cm} + cm.syncReqs.Repr + cm.journalist.Repr;
    cm.reveal_ReprInv();
  }
  
  method writeOutSuperblockAdvanceLocation(
      k: ImplConstants, cm: Committer, io: DiskIOHandler)
  requires io.initialized()
  requires cm.Inv()
  requires io !in cm.Repr
  requires cm.status == CommitterModel.StatusReady
  requires cm.frozenLoc.Some?
  modifies cm.Repr
  modifies io
  ensures cm.W()
  ensures cm.Repr == old(cm.Repr)
  ensures CommitterCommitModel.writeOutSuperblockAdvanceLocation(
      Ic(k), old(cm.I()), old(IIO(io)), cm.I(), IIO(io))
  {
    CommitterCommitModel.reveal_writeOutSuperblockAdvanceLocation();
    cm.reveal_ReprInv();

    var writtenJournalLen := cm.journalist.getWrittenJournalLen();

    var newSuperblock := SectorType.Superblock(
      JC.IncrementSuperblockCounter(cm.superblock.counter),
      CommitterCommitModel.start_pos_add(
          cm.superblock.journalStart,
          cm.frozenJournalPosition),
      writtenJournalLen - cm.frozenJournalPosition,
      cm.frozenLoc.value
    );

    assert JC.WFSuperblock(newSuperblock);

    var loc := if cm.whichSuperblock == 0 then Superblock2Location() else Superblock1Location();
    var id := RequestWrite(io, loc,
        StateImpl.SectorSuperblock(newSuperblock));

    cm.newSuperblock := Some(newSuperblock);
    cm.superblockWrite := Some(id);
    cm.commitStatus := JC.CommitAdvanceLocation;

    cm.Repr := {cm} + cm.syncReqs.Repr + cm.journalist.Repr;
    cm.reveal_ReprInv();
  }

  method freeze(k: ImplConstants, cm: Committer)
  requires cm.WF()
  modifies cm.Repr
  ensures cm.W()
  ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
  ensures cm.I() == CommitterCommitModel.freeze(Ic(k), old(cm.I()))
  {
    CommitterCommitModel.reveal_freeze();
    cm.reveal_ReprInv();

    var writtenJournalLen := cm.journalist.getWrittenJournalLen();

    cm.journalist.freeze();

    cm.frozenLoc := None;
    cm.frozenJournalPosition := writtenJournalLen;
    cm.isFrozen := true;
    cm.syncReqs := SyncReqs3to2(cm.syncReqs);

    cm.Repr := {cm} + cm.syncReqs.Repr + cm.journalist.Repr;
    cm.reveal_ReprInv();
  }

  method receiveFrozenLoc(
      k: ImplConstants, cm: Committer, loc: Location)
  requires cm.W()
  modifies cm.Repr
  ensures cm.W()
  ensures cm.Repr == old(cm.Repr)
  ensures cm.I() == CommitterCommitModel.receiveFrozenLoc(
        Ic(k), old(cm.I()), loc)
  {
    CommitterCommitModel.reveal_receiveFrozenLoc();
    cm.reveal_ReprInv();

    cm.frozenLoc := Some(loc);

    cm.reveal_ReprInv();
  }

  // == pushSync ==

  method freeId<A>(syncReqs: MutableMap.ResizingHashMap<A>) returns (id: uint64)
  requires syncReqs.Inv()
  ensures id == CommitterCommitModel.freeId(syncReqs.I())
  {
    CommitterCommitModel.reveal_freeId();
    var maxId := syncReqs.MaxKey();
    if maxId == 0xffff_ffff_ffff_ffff {
      return 0;
    } else {
      return maxId + 1;
    }
  }

  method pushSync(k: ImplConstants, cm: Committer)
  returns (id: uint64)
  requires cm.Inv()
  modifies cm.Repr
  ensures cm.W()
  ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
  ensures (cm.I(), id) == CommitterCommitModel.pushSync(
      Ic(k), old(cm.I()))
  {
    cm.reveal_ReprInv();

    id := freeId(cm.syncReqs);
    if id != 0 && cm.syncReqs.Count < 0x2000_0000_0000_0000 {
      cm.syncReqs.Insert(id, JC.State3);
    } else {
      id := 0;
    }

    cm.Repr := {cm} + cm.syncReqs.Repr + cm.journalist.Repr;
    cm.reveal_ReprInv();
  }

  // == popSync ==

  method popSync(k: ImplConstants, cm: Committer, id: uint64)
  requires cm.Inv()
  modifies cm.Repr
  ensures cm.W()
  ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
  ensures cm.I() == CommitterCommitModel.popSync(
      Ic(k), old(cm.I()), id)
  {
    CommitterCommitModel.reveal_popSync();
    cm.reveal_ReprInv();

    cm.syncReqs.Remove(id);

    cm.Repr := {cm} + cm.syncReqs.Repr + cm.journalist.Repr;
    cm.reveal_ReprInv();
  }

  // == AdvanceLog ==

  method tryAdvanceLog(k: ImplConstants, cm: Committer, io: DiskIOHandler)
  returns (wait: bool)
  requires cm.Inv()
  requires io.initialized()
  requires io !in cm.Repr
  requires cm.status == CommitterModel.StatusReady
  modifies cm.Repr
  modifies io
  ensures cm.W()
  ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
  ensures CommitterCommitModel.tryAdvanceLog(
      Ic(k), old(cm.I()), old(IIO(io)), cm.I(), IIO(io))
  {
    CommitterCommitModel.reveal_tryAdvanceLog();

    wait := false;

    var hasFrozen := cm.journalist.hasFrozenJournal();
    var hasInMem := cm.journalist.hasInMemoryJournal();
    if cm.superblockWrite.None? {
      if hasFrozen || hasInMem {
        WriteOutJournal(k, cm, io);
      } else if (cm.outstandingJournalWrites == {}) {
        writeOutSuperblockAdvanceLog(k, cm, io);
      } else {
        //print "tryAdvanceLog: doing nothing, has outstanding journal writes\n";
        wait := true;
      }
    } else {
      //print "tryAdvanceLog: doing nothing, has outstanding superblock writes\n";
      wait := true;
    }
  }

  method tryAdvanceLocation(k: ImplConstants, cm: Committer, io: DiskIOHandler)
  returns (wait: bool)
  requires cm.Inv()
  requires io.initialized()
  requires io !in cm.Repr
  requires cm.status == CommitterModel.StatusReady
  requires cm.frozenLoc.Some?
  modifies cm.Repr
  modifies io
  ensures cm.W()
  ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
  ensures CommitterCommitModel.tryAdvanceLocation(
      Ic(k), old(cm.I()), old(IIO(io)), cm.I(), IIO(io))
  {
    CommitterCommitModel.reveal_tryAdvanceLocation();

    wait := false;

    var hasFrozen := cm.journalist.hasFrozenJournal();
    var hasInMem := cm.journalist.hasInMemoryJournal();
    if cm.superblockWrite.None? {
      if hasFrozen || hasInMem {
        WriteOutJournal(k, cm, io);
      } else if (cm.outstandingJournalWrites == {}) {
        writeOutSuperblockAdvanceLocation(k, cm, io);
      } else {
        //print "tryAdvanceLocation: doing nothing, has outstanding journal writes\n";
        wait := true;
      }
    } else {
      //print "tryAdvanceLocation: doing nothing, has outstanding superblock writes\n";
      wait := true;
    }
  }

  method writeBackSuperblockResp(k: ImplConstants, cm: Committer)
  requires cm.Inv()
  modifies cm.Repr
  ensures cm.W()
  ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
  ensures cm.I() == CommitterCommitModel.writeBackSuperblockResp(
      Ic(k), old(cm.I()));
  {
    CommitterCommitModel.reveal_writeBackSuperblockResp();
    cm.reveal_ReprInv();

    if cm.status.StatusReady? && cm.commitStatus.CommitAdvanceLocation? {
      var writtenJournalLen := cm.journalist.getWrittenJournalLen();

      cm.superblockWrite := None;
      cm.superblock := cm.newSuperblock.value;
      cm.newSuperblock := None;
      cm.whichSuperblock := if cm.whichSuperblock == 0 then 1 else 0;
      cm.syncReqs := SyncReqs2to1(cm.syncReqs);
      cm.journalist.updateWrittenJournalLen(
            writtenJournalLen - cm.frozenJournalPosition);
      cm.frozenJournalPosition := 0;
      cm.frozenLoc := None;
      cm.isFrozen := false;
      cm.commitStatus := JC.CommitNone;
    } else if cm.status.StatusReady? && cm.commitStatus.CommitAdvanceLog? {
      cm.superblockWrite := None;
      cm.superblock := cm.newSuperblock.value;
      cm.newSuperblock := None;
      cm.whichSuperblock := if cm.whichSuperblock == 0 then 1 else 0;
      cm.syncReqs := SyncReqs2to1(cm.syncReqs);
      cm.commitStatus := JC.CommitNone;
    } else {
      print "writeBackSuperblockResp: didn't do anything\n";
    }

    cm.Repr := {cm} + cm.syncReqs.Repr + cm.journalist.Repr;
    cm.reveal_ReprInv();
  }
}
