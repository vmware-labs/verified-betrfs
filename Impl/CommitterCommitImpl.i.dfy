include "CommitterImpl.i.dfy"
include "CommitterCommitModel.i.dfy"
include "DiskOpImpl.i.dfy"

module CommitterCommitImpl {
  import opened NativeTypes
  import opened Options

  import opened DiskLayout
  import JC = JournalCache
  import opened Journal
  import opened JournalBytes
  import opened DiskOpImpl
  import opened MainDiskIOHandler
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
  modifies cm.Repr
  modifies io
  ensures cm.Repr == old(cm.Repr)
  ensures CommitterCommitModel.writeOutSuperblockAdvanceLog(
      Ic(k), old(cm.I()), old(IIO(io)), cm.I(), IIO(io))
  {
    CommitterCommitModel.reveal_writeOutSuperblockAdvanceLog();
    cm.reveal_ReprInv();

    var writtenJournalLen := cm.journalist.getWrittenJournalLen();

    var newSuperblock := SectorType.Superblock(
      JC.IncrementSuperblockCounter(cm.superblock.counter),
      cm.superblock.journalStart,
      writtenJournalLen,
      cm.superblock.indirectionTableLoc
    );

    var loc := if cm.whichSuperblock == 0 then Superblock2Location() else Superblock1Location();

    var id := RequestWrite(io, loc, SectorSuperblock(newSuperblock));

    && cm'.superblockWrite.Some?
    && var id := cm'.superblockWrite.value;

    && RequestWrite(io, loc, SectorSuperblock(newSuperblock),
        Some(id), io')
    && cm' == cm
      .(newSuperblock := Some(newSuperblock))
      .(superblockWrite := Some(id))
      .(commitStatus := JC.CommitAdvanceLog)


    cm.Repr := {cm} + cm.syncReqs.Repr + cm.journalist.Repr;
    cm.reveal_ReprInv();
  }
  
}
