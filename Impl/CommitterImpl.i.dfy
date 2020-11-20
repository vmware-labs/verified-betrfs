include "../lib/DataStructures/LinearMutableMap.i.dfy"
include "CommitterModel.i.dfy"
include "JournalistImpl.i.dfy"
include "CommitterAppendModel.i.dfy"
include "CommitterReplayModel.i.dfy"
include "CommitterInitModel.i.dfy"
include "DiskOpImpl.i.dfy"
include "IOImpl.i.dfy"
include "CommitterCommitModel.i.dfy"

// for when you have commitment issues

module CommitterImpl {
  import JournalistModel
  import JC = JournalCache
  import opened SectorType
  import opened DiskLayout
  import opened Options
  import opened NativeTypes
  import LinearMutableMap
  import JournalistImpl
  import CommitterModel

  import opened KeyType
  import opened ValueType
  import opened Journal

  import opened DiskOpImpl

  import opened StateModel
  import CommitterReplayModel
  import CommitterAppendModel
  import CommitterInitModel
  import opened IOImpl
  import opened InterpretationDiskOps
  import opened MainDiskIOHandler
  import JournalistParsingImpl
  import CommitterCommitModel

  import StateImpl

  // TODO we could have these do the modification in-place instead.

  method SyncReqs2to1(linear m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
  returns (linear m' : LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
  requires m.Inv()
  ensures m'.Inv()
  ensures m' == CommitterCommitModel.SyncReqs2to1(m)
  {
    CommitterCommitModel.reveal_SyncReqs2to1();
    var it := LinearMutableMap.IterStart(m);
    linear var m0 := LinearMutableMap.Constructor(128);
    while !it.next.Done?
    invariant m.Inv()
    invariant m0.Inv()
    invariant LinearMutableMap.WFIter(m, it)
    invariant m0.Inv()
    invariant m0.contents.Keys == it.s
    invariant CommitterCommitModel.SyncReqs2to1(m) == CommitterCommitModel.SyncReqs2to1Iterate(m, it, m0)

    decreases it.decreaser
    {
      LinearMutableMap.LemmaIterIndexLtCount(m, it);
      LinearMutableMap.CountBound(m);
      m0 := LinearMutableMap.Insert(m0, it.next.key, (if it.next.value == JC.State2 then JC.State1 else it.next.value));
      it := LinearMutableMap.IterInc(m, it);
    }
    LinearMutableMap.Destructor(m);
    m' := m0;
  }

  method SyncReqs3to2(linear m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
  returns (linear m' : LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
  requires m.Inv()
  ensures m'.Inv()
  ensures m' == CommitterCommitModel.SyncReqs3to2(m)
  {
    CommitterCommitModel.reveal_SyncReqs3to2();
    var it := LinearMutableMap.IterStart(m);
    linear var m0 := LinearMutableMap.Constructor(128);
    while !it.next.Done?
    invariant m.Inv()
    invariant m0.Inv()
    invariant LinearMutableMap.WFIter(m, it)
    invariant m0.Inv()
    invariant m0.contents.Keys == it.s
    invariant CommitterCommitModel.SyncReqs3to2(m) == CommitterCommitModel.SyncReqs3to2Iterate(m, it, m0)

    decreases it.decreaser
    {
      LinearMutableMap.LemmaIterIndexLtCount(m, it);
      LinearMutableMap.CountBound(m);
      m0 := LinearMutableMap.Insert(m0, it.next.key, (if it.next.value == JC.State3 then JC.State2 else it.next.value));
      it := LinearMutableMap.IterInc(m, it);
    }
    LinearMutableMap.Destructor(m);
    m' := m0;
  }

  linear datatype Committer = Committer(
  status: CommitterModel.Status,
  linear journalist: JournalistImpl.Journalist,
  frozenLoc: Option<Location>,
  isFrozen: bool,
  frozenJournalPosition: uint64,
  superblockWrite: Option<JC.ReqId>,
  outstandingJournalWrites: set<JC.ReqId>,
  superblock: Superblock,
  newSuperblock: Option<Superblock>,
  whichSuperblock: uint64,
  commitStatus: JC.CommitStatus,
  journalFrontRead: Option<JC.ReqId>,
  journalBackRead: Option<JC.ReqId>,
  superblock1Read: Option<JC.ReqId>,
  superblock2Read: Option<JC.ReqId>,
  superblock1: JC.SuperblockReadResult,
  superblock2: JC.SuperblockReadResult,
  linear syncReqs: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
  {
    predicate W()
    {
      && this.syncReqs.Inv()
      && this.journalist.Inv()
    }

    function I() : CommitterModel.CM
    requires W()
    {
      CommitterModel.CM(
        status,
        journalist.I(),
        frozenLoc,
        isFrozen,
        frozenJournalPosition,
        superblockWrite,
        outstandingJournalWrites,
        superblock,
        newSuperblock,
        whichSuperblock,
        commitStatus,
        journalFrontRead,
        journalBackRead,
        superblock1Read,
        superblock2Read,
        superblock1,
        superblock2,
        syncReqs
      )
    }

    predicate WF()
    {
      && W()
      && CommitterModel.WF(I())
    }

    predicate Inv()
    {
      && W()
      && CommitterModel.Inv(I())
    }

    static method Constructor() returns (linear cm: Committer)
    ensures cm.Inv()
    ensures CommitterModel.I(cm.I())
        == JC.LoadingSuperblock(
            None, None,
            JC.SuperblockUnfinished,
            JC.SuperblockUnfinished,
            map[])
    {
      linear var j := JournalistImpl.Journalist.Constructor();
      linear var m := LinearMutableMap.Constructor(128);
      cm := Committer(
        CommitterModel.StatusLoadingSuperblock,
        j,
        None,
        false,
        0,
        None,
        {},
        Superblock(0, 0, 0, Location(0, 0)),
        None,
        0,
        JC.CommitStatus.CommitNone,
        None,
        None,
        None,
        None,
        JC.SuperblockUnfinished,
        JC.SuperblockUnfinished,
        m
      );
      assert CommitterModel.I(cm.I()) == JC.LoadingSuperblock(
            None, None,
            JC.SuperblockUnfinished,
            JC.SuperblockUnfinished,
            map[]);
    }

    linear inout method JournalAppend(key: Key, value: Value)
    requires old_self.Inv()
    requires old_self.status == CommitterModel.StatusReady
    requires JournalistModel.canAppend(
        old_self.journalist.I(), JournalInsert(key, value))
    ensures self.Inv()
    ensures self.I() == CommitterAppendModel.JournalAppend(
        old_self.I(), key, value)
    {
      CommitterAppendModel.reveal_JournalAppend();
      var je := JournalInsert(key, value);
      inout self.journalist.append(je);
    }

    linear inout method JournalReplayOne()
    requires old_self.Inv()
    requires old_self.status == CommitterModel.StatusReady
    requires !JournalistModel.isReplayEmpty(old_self.journalist.I())
    ensures self.Inv()
    ensures self.I() == CommitterReplayModel.JournalReplayOne(old_self.I())
    {
      CommitterReplayModel.reveal_JournalReplayOne();
      inout self.journalist.replayJournalPop();
    }

    linear inout method PageInSuperblockReq(io: DiskIOHandler, which: uint64)
    requires old_self.Inv()
    requires which == 0 || which == 1
    requires which == 0 ==> old_self.superblock1.SuperblockUnfinished?
    requires which == 1 ==> old_self.superblock2.SuperblockUnfinished?
    requires old_self.status.StatusLoadingSuperblock?
    requires io.initialized()
    modifies io
    ensures self.W()
    ensures (self.I(), IIO(io)) ==
        CommitterInitModel.PageInSuperblockReq(
            old_self.I(), old(IIO(io)), which)
    {
      CommitterInitModel.reveal_PageInSuperblockReq();

      if which == 0 {
        if self.superblock1Read.None? {
          var loc := Superblock1Location();
          var id := RequestRead(io, loc);
          inout self.superblock1Read := Some(id);
        } else {
          print "PageInSuperblockReq: doing nothing\n";
        }
      } else {
        if self.superblock2Read.None? {
            var loc := Superblock2Location();
            var id := RequestRead(io, loc);
            inout self.superblock2Read := Some(id);
        } else {
            print "PageInSuperblockReq: doing nothing\n";
        }
      }
    }
  
    linear inout method FinishLoadingSuperblockPhase()
    requires old_self.Inv()
    requires old_self.status.StatusLoadingSuperblock?
    requires old_self.superblock1.SuperblockSuccess?
    requires old_self.superblock2.SuperblockSuccess?

    ensures self.W()
    ensures self.I() ==
        CommitterInitModel.FinishLoadingSuperblockPhase(
            old_self.I());
    {
      CommitterInitModel.reveal_FinishLoadingSuperblockPhase();

      var idx := if JC.increments1(
          self.superblock1.value.counter, self.superblock2.value.counter)
          then 1 else 0;

      var sup := if idx == 1 then
        self.superblock2.value
      else
        self.superblock1.value;

      inout self.whichSuperblock := idx;
      inout self.superblock := sup;
      inout self.status := CommitterModel.StatusLoadingOther;
      inout self.journalFrontRead := None;
      inout self.journalBackRead := None;
    }

    linear inout method FinishLoadingOtherPhase()
    requires old_self.Inv()
    requires old_self.status.StatusLoadingOther?
    ensures self.W()
    ensures self.I() ==
        CommitterInitModel.FinishLoadingOtherPhase(
            old_self.I());
    {
      CommitterInitModel.reveal_FinishLoadingOtherPhase();

      var success := inout self.journalist.parseJournals();

      if success {
        inout self.status := CommitterModel.StatusReady;
        inout self.frozenLoc := None;
        inout self.isFrozen := false;
        inout self.frozenJournalPosition := 0;
        inout self.superblockWrite := None;
        inout self.outstandingJournalWrites := {};
        inout self.newSuperblock := None;
        inout self.commitStatus := JC.CommitNone;
        // [original] self.journalist.setWrittenJournalLen(self.superblock.journalLen);
        var len := self.superblock.journalLen;
        inout self.journalist.setWrittenJournalLen(len);
      } else {
        print "FinishLoadingOtherPhase: there is replay journal\n";
      }
    }

    shared method isReplayEmpty()
    returns (b : bool)
    requires this.WF()
    ensures b == CommitterInitModel.isReplayEmpty(this.I())
    {
      b := this.journalist.isReplayEmpty();
    }

    linear inout method PageInJournalReqFront(io: DiskIOHandler)
    requires old_self.WF()
    requires old_self.status.StatusLoadingOther?
    requires old_self.superblock.journalLen > 0
    requires io.initialized()
    modifies io
    ensures self.W()
    ensures (self.I(), IIO(io)) == CommitterInitModel.PageInJournalReqFront(
        old_self.I(), old(IIO(io)))
    {
      CommitterInitModel.reveal_PageInJournalReqFront();

      var len :=
        if self.superblock.journalStart + self.superblock.journalLen
            >= NumJournalBlocks()
        then
          NumJournalBlocks() - self.superblock.journalStart
        else
          self.superblock.journalLen;
      var loc := JournalRangeLocation(self.superblock.journalStart, len);
      var id := RequestRead(io, loc);
      inout self.journalFrontRead := Some(id);
      inout self.journalBackRead :=
          if self.journalBackRead == Some(id)
            then None else self.journalBackRead;
    }

    linear inout method PageInJournalReqBack(io: DiskIOHandler)
    requires old_self.WF()
    requires old_self.status.StatusLoadingOther?
    requires old_self.superblock.journalLen > 0
    requires old_self.superblock.journalStart + old_self.superblock.journalLen > NumJournalBlocks()
    requires io.initialized()
    modifies io
    ensures self.W()
    ensures (self.I(), IIO(io)) == CommitterInitModel.PageInJournalReqBack(
        old_self.I(), old(IIO(io)))
    {
      CommitterInitModel.reveal_PageInJournalReqBack();

      var len := self.superblock.journalStart + self.superblock.journalLen - NumJournalBlocks();
      var loc := JournalRangeLocation(0, len);
      var id := RequestRead(io, loc);
      inout self.journalBackRead := Some(id);
      inout self.journalFrontRead :=
          if self.journalFrontRead == Some(id)
            then None else self.journalFrontRead;
    }

    linear inout method PageInJournalResp(io: DiskIOHandler)
    requires old_self.WF()
    requires old_self.status.StatusLoadingOther?
    requires io.diskOp().RespReadOp?
    requires ValidDiskOp(io.diskOp())
    requires ValidJournalLocation(LocOfRespRead(io.diskOp().respRead))
    ensures self.W()
    ensures self.I() == CommitterInitModel.PageInJournalResp(
        old_self.I(), old(IIO(io)))
    {
      CommitterInitModel.reveal_PageInJournalResp();

      var id, addr, bytes := io.getReadResult();
      var jr := JournalistParsingImpl.computeJournalRangeOfByteSeq(bytes);
      if jr.Some? {
        assert |jr.value| <= NumJournalBlocks() as int by {
          reveal_ValidJournalLocation();
        }

        if self.journalFrontRead == Some(id) {
          inout self.journalist.setFront(jr.value);
          inout self.journalFrontRead := None;
        } else if self.journalBackRead == Some(id) {
          inout self.journalist.setBack(jr.value);
          inout self.journalBackRead := None;
        }
      }
    }

    linear inout method tryFinishLoadingOtherPhase(io: DiskIOHandler)
    requires old_self.Inv()
    requires old_self.status.StatusLoadingOther?
    requires io.initialized()
    modifies io
    ensures self.W()
    ensures (self.I(), IIO(io)) == CommitterInitModel.tryFinishLoadingOtherPhase(
        old_self.I(), old(IIO(io)))
    {
      CommitterInitModel.reveal_tryFinishLoadingOtherPhase();

      var hasFront := self.journalist.hasFront();
      var hasBack := self.journalist.hasBack();
      if self.superblock.journalLen > 0 && !self.journalFrontRead.Some? && !hasFront {
        inout self.PageInJournalReqFront(io);
      } else if self.superblock.journalStart + self.superblock.journalLen > NumJournalBlocks() && !self.journalBackRead.Some? && !hasBack {
        inout self.PageInJournalReqBack(io);
      } else if (self.superblock.journalLen > 0 ==> hasFront)
          && (self.superblock.journalStart + self.superblock.journalLen > NumJournalBlocks() ==> hasBack) {
        inout self.FinishLoadingOtherPhase();
      } else {
      }
    }

    linear inout method WriteOutJournal(io: DiskIOHandler)
    requires io.initialized()
    requires old_self.Inv()
    requires JournalistModel.I(old_self.I().journalist).inMemoryJournalFrozen != []
          || JournalistModel.I(old_self.I().journalist).inMemoryJournal != []
    modifies io
    ensures self.W()
    ensures (self.I(), IIO(io)) == CommitterCommitModel.WriteOutJournal(
        old_self.I(), old(IIO(io)))
    {
      CommitterCommitModel.reveal_WriteOutJournal();

      var writtenJournalLen := self.journalist.getWrittenJournalLen();
      var doingFrozen := self.journalist.hasFrozenJournal();

      var j;
      if doingFrozen {
        j := inout self.journalist.packageFrozenJournal();
      } else {
        j := inout self.journalist.packageInMemoryJournal();
      }

      var start := CommitterCommitModel.start_pos_add(
          self.superblock.journalStart,
          writtenJournalLen);

      var len := |j| as uint64 / 4096;

      var contiguous := start + len <= NumJournalBlocks();

      if contiguous {
        var id := io.write(JournalPoint(start), j);
        inout self.outstandingJournalWrites := self.outstandingJournalWrites + {id};
      } else {
        var cut := (NumJournalBlocks() - start) * 4096;
        var id1, id2 := io.write2(
            JournalPoint(start), j[..cut],
            JournalPoint(0), j[cut..]);
        inout self.outstandingJournalWrites := self.outstandingJournalWrites + {id1, id2};
      }

      if doingFrozen {
        inout self.frozenJournalPosition := self.journalist.getWrittenJournalLen();
      } else {
        // [yizhou7] FIXME: very inelegant to deconstruct and reconstruct
        linear var Committer(status,
            journalist,
            frozenLoc,
            isFrozen,
            frozenJournalPosition,
            superblockWrite,
            outstandingJournalWrites,
            superblock,
            newSuperblock,
            whichSuperblock,
            commitStatus,
            journalFrontRead,
            journalBackRead,
            superblock1Read,
            superblock2Read,
            superblock1,
            superblock2,
            syncReqs) := self;

        syncReqs := SyncReqs3to2(syncReqs);
        self := Committer(status,
            journalist,
            frozenLoc,
            isFrozen,
            frozenJournalPosition,
            superblockWrite,
            outstandingJournalWrites,
            superblock,
            newSuperblock,
            whichSuperblock,
            commitStatus,
            journalFrontRead,
            journalBackRead,
            superblock1Read,
            superblock2Read,
            superblock1,
            superblock2,
            syncReqs);
      }

      assert (self.I(), IIO(io)) == CommitterCommitModel.WriteOutJournal(
        old_self.I(), old(IIO(io)));
    }

    linear inout method writeOutSuperblockAdvanceLog(io: DiskIOHandler)
    requires io.initialized()
    requires old_self.Inv()
    requires old_self.status == CommitterModel.StatusReady
    modifies io
    ensures self.W()
    ensures CommitterCommitModel.writeOutSuperblockAdvanceLog(
        old_self.I(), old(IIO(io)), self.I(), IIO(io))
    {
      var writtenJournalLen := self.journalist.getWrittenJournalLen();
      var newSuperblock := SectorType.Superblock(
        JC.IncrementSuperblockCounter(self.superblock.counter),
        self.superblock.journalStart,
        writtenJournalLen,
        self.superblock.indirectionTableLoc
      );
      assert JC.WFSuperblock(newSuperblock);
      var loc := if self.whichSuperblock == 0 then Superblock2Location() else Superblock1Location();
      var id := RequestWrite(io, loc,
          StateImpl.SectorSuperblock(newSuperblock));
      inout self.newSuperblock := Some(newSuperblock);
      inout self.superblockWrite := Some(id);
      inout self.commitStatus := JC.CommitAdvanceLog;
    }

    linear inout method writeOutSuperblockAdvanceLocation(io: DiskIOHandler)
    requires io.initialized()
    requires old_self.Inv()
    requires old_self.status == CommitterModel.StatusReady
    requires old_self.frozenLoc.Some?
    modifies io
    ensures self.W()
    ensures CommitterCommitModel.writeOutSuperblockAdvanceLocation(
        old_self.I(), old(IIO(io)), self.I(), IIO(io))
    {
      CommitterCommitModel.reveal_writeOutSuperblockAdvanceLocation();
      var writtenJournalLen := self.journalist.getWrittenJournalLen();
      var newSuperblock := SectorType.Superblock(
        JC.IncrementSuperblockCounter(self.superblock.counter),
        CommitterCommitModel.start_pos_add(
            self.superblock.journalStart,
            self.frozenJournalPosition),
        writtenJournalLen - self.frozenJournalPosition,
        self.frozenLoc.value
      );
      assert JC.WFSuperblock(newSuperblock);
      var loc := if self.whichSuperblock == 0 then Superblock2Location() else Superblock1Location();
      var id := RequestWrite(io, loc,
          StateImpl.SectorSuperblock(newSuperblock));
      inout self.newSuperblock := Some(newSuperblock);
      inout self.superblockWrite := Some(id);
      inout self.commitStatus := JC.CommitAdvanceLocation;
    }

    linear inout method freeze()
    requires old_self.WF()
    ensures self.W()
    ensures self.I() == CommitterCommitModel.freeze(old_self.I())
    {
      CommitterCommitModel.reveal_freeze();
      var writtenJournalLen := self.journalist.getWrittenJournalLen();
      inout self.journalist.freeze();
      inout self.frozenLoc := None;
      inout self.frozenJournalPosition := writtenJournalLen;
      inout self.isFrozen := true;
      // inout self.syncReqs := SyncReqs3to2(self.syncReqs);

        // [yizhou7] FIXME: very inelegant to deconstruct and reconstruct
        linear var Committer(status,
            journalist,
            frozenLoc,
            isFrozen,
            frozenJournalPosition,
            superblockWrite,
            outstandingJournalWrites,
            superblock,
            newSuperblock,
            whichSuperblock,
            commitStatus,
            journalFrontRead,
            journalBackRead,
            superblock1Read,
            superblock2Read,
            superblock1,
            superblock2,
            syncReqs) := self;

        syncReqs := SyncReqs3to2(syncReqs);

        self := Committer(status,
            journalist,
            frozenLoc,
            isFrozen,
            frozenJournalPosition,
            superblockWrite,
            outstandingJournalWrites,
            superblock,
            newSuperblock,
            whichSuperblock,
            commitStatus,
            journalFrontRead,
            journalBackRead,
            superblock1Read,
            superblock2Read,
            superblock1,
            superblock2,
            syncReqs);

    }

    linear inout method receiveFrozenLoc(loc: Location)
    requires old_self.W()
    ensures self.W()
    ensures self.I() == CommitterCommitModel.receiveFrozenLoc(
          old_self.I(), loc)
    {
      CommitterCommitModel.reveal_receiveFrozenLoc();
      inout self.frozenLoc := Some(loc);
    }

    // == pushSync ==
    shared method freeId() returns (id: uint64)
    requires syncReqs.Inv()
    ensures id == CommitterCommitModel.freeId(syncReqs)
    {
      CommitterCommitModel.reveal_freeId();
      var maxId := LinearMutableMap.MaxKey(this.syncReqs);
      if maxId == 0xffff_ffff_ffff_ffff {
        return 0;
      } else {
        return maxId + 1;
      }
    }

    linear inout method pushSync()
    returns (id: uint64)
    requires old_self.Inv()
    ensures self.W()
    ensures (self.I(), id) == CommitterCommitModel.pushSync(
        old_self.I())
    {
      id := self.freeId();
      if id != 0 && self.syncReqs.count < 0x2000_0000_0000_0000 {
        LinearMutableMap.InOutInsert(inout self.syncReqs, id, JC.State3);
      } else {
        id := 0;
      }
    }

    // == popSync ==
    linear inout method popSync(id: uint64)
    requires old_self.Inv()
    ensures self.W()
    ensures self.I() == CommitterCommitModel.popSync(
        old_self.I(), id)
    {
      CommitterCommitModel.reveal_popSync();
      LinearMutableMap.InOutRemove(inout self.syncReqs, id);
    }

/*
    // == AdvanceLog ==
    method tryAdvanceLog(cm: Committer, io: DiskIOHandler)
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
        old(cm.I()), old(IIO(io)), cm.I(), IIO(io))
    {
      CommitterCommitModel.reveal_tryAdvanceLog();
      wait := false;
      var hasFrozen := cm.journalist.hasFrozenJournal();
      var hasInMem := cm.journalist.hasInMemoryJournal();
      if cm.superblockWrite.None? {
        if hasFrozen || hasInMem {
          WriteOutJournal(cm, io);
        } else if (cm.outstandingJournalWrites == {}) {
          writeOutSuperblockAdvanceLog(cm, io);
        } else {
          wait := true;
        }
      } else {
        wait := true;
      }
    }

    method tryAdvanceLocation(cm: Committer, io: DiskIOHandler)
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
        old(cm.I()), old(IIO(io)), cm.I(), IIO(io))
    {
      CommitterCommitModel.reveal_tryAdvanceLocation();
      wait := false;
      var hasFrozen := cm.journalist.hasFrozenJournal();
      var hasInMem := cm.journalist.hasInMemoryJournal();
      if cm.superblockWrite.None? {
        if hasFrozen || hasInMem {
          WriteOutJournal(cm, io);
        } else if (cm.outstandingJournalWrites == {}) {
          writeOutSuperblockAdvanceLocation(cm, io);
        } else {
          wait := true;
        }
      } else {
        wait := true;
      }
    }

    method writeBackSuperblockResp(cm: Committer)
    requires cm.Inv()
    modifies cm.Repr
    ensures cm.W()
    ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
    ensures cm.I() == CommitterCommitModel.writeBackSuperblockResp(
        old(cm.I()));
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
    */
  }
}
