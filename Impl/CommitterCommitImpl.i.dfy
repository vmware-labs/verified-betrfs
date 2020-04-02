include "CommitterImpl.i.dfy"
include "CommitterCommitModel.i.dfy"

module CommitterCommitImpl {
  import opened NativeTypes
  import opened Options

  import opened DiskLayout
  import JC = JournalCache
  import opened Journal
  import opened JournalBytes
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
  modifies cm.Repr
  ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
  ensures cm.Inv()
  ensures cm.I() == CommitterCommitModel.WriteOutJournal(
      k, old(cm.I()), IIO(io))
  /*{
    var writtenJournalLen :=
        JournalistModel.getWrittenJournalLen(cm.journalist);

    var doingFrozen :=
      JournalistModel.hasFrozenJournal(cm.journalist);

    var (journalist', j) :=
      if doingFrozen then
        JournalistModel.packageFrozenJournal(cm.journalist)
      else
        JournalistModel.packageInMemoryJournal(cm.journalist);

    var start := start_pos_add(
        cm.superblock.journalStart,
        writtenJournalLen);

    var len := |j| as uint64 / 4096;

    var contiguous := start + len <= NumJournalBlocks();

    var io' := if contiguous then
      IOReqWrite(io.id, D.ReqWrite(JournalPoint(start), j))
    else (
      var cut := (NumJournalBlocks() - start) * 4096;
      IOReqWrite2(io.id, io.id2,
          D.ReqWrite(JournalPoint(start), j[..cut]),
          D.ReqWrite(JournalPoint(0), j[cut..]))
    );

    var outstandingJournalWrites' := if contiguous
        then cm.outstandingJournalWrites + {io.id}
        else cm.outstandingJournalWrites + {io.id, io.id2};

    var frozenJournalPosition' := if doingFrozen
      then JournalistModel.getWrittenJournalLen(journalist')
      else cm.frozenJournalPosition;

    var syncReqs' := if doingFrozen
      then cm.syncReqs
      else SyncReqs3to2(cm.syncReqs);

    var cm' := cm
      .(outstandingJournalWrites := outstandingJournalWrites')
      .(journalist := journalist')
      .(frozenJournalPosition := frozenJournalPosition')
      .(syncReqs := syncReqs');

    (cm', io')
  }*/
}
