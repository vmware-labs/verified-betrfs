include "../lib/DataStructures/LinearMutableMap.i.dfy"
include "JournalistImpl.i.dfy"
include "DiskOpImpl.i.dfy"
include "IOImpl.i.dfy"
include "../Versions/VOp.i.dfy"

// for when you have commitment issues

module CommitterImpl {
  import JC = JournalCache
  import opened SectorType
  import opened DiskLayout
  import opened Options
  import opened NativeTypes
  import LinearMutableMap
  import JournalistImpl

  import opened KeyType
  import opened ValueType
  import opened Journal

  import opened DiskOpImpl
  import opened IOImpl
  import opened InterpretationDiskOps
  import opened MainDiskIOHandler
  import JournalistParsingImpl

  import SSI = StateSectorImpl
  import opened ViewOp
  import opened DiskOpModel
  import opened JournalBytes
  import IOModel

  import SSM = StateSectorModel

  method SyncReqs2to1(linear inout m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
  requires old_m.Inv()
  ensures m.Inv()
  ensures JC.syncReqs2to1(old_m.contents) == m.contents
  {
    var it := LinearMutableMap.SimpleIterStart(m);

    var nextOut := LinearMutableMap.SimpleIterOutput(m, it);

    assert it.s == {};
    while !nextOut.Done?
    invariant m.Inv()
    invariant LinearMutableMap.WFSimpleIter(m, it)
    invariant nextOut == LinearMutableMap.SimpleIterOutput(m, it)
    invariant m.contents.Keys == old_m.contents.Keys
    invariant it.s <= m.contents.Keys
    invariant forall id | id in m.contents.Keys :: (
      ((id in it.s) ==> (m.contents[id] == (if old_m.contents[id] == JC.State2 then JC.State1 else old_m.contents[id]))))
    invariant forall id | id in m.contents.Keys :: (
      ((id !in it.s) ==> m.contents[id] == old_m.contents[id])
    )
    decreases it.decreaser
    {
      ghost var keySet := m.contents.Keys;
      LinearMutableMap.CountBound(m);

      var value := if nextOut.value == JC.State2 then JC.State1 else nextOut.value;

      ghost var prev_m := m;
      LinearMutableMap.UpdateByIter(inout m, it, value);

      // seems like this is the missing knowledge 
      // before and after the map update, the iterator has the same key
      // of course the values could be different
      assert LinearMutableMap.SimpleIterOutput(prev_m, it).key == 
        LinearMutableMap.SimpleIterOutput(m, it).key;

      it := LinearMutableMap.SimpleIterInc(m, it);
      nextOut := LinearMutableMap.SimpleIterOutput(m, it);
    }
  }

  method SyncReqs3to2(linear inout m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
  requires old_m.Inv()
  ensures m.Inv()
  ensures JC.syncReqs3to2(old_m.contents) == m.contents
  {
    var it := LinearMutableMap.SimpleIterStart(m);

    var nextOut := LinearMutableMap.SimpleIterOutput(m, it);

    assert it.s == {};
    while !nextOut.Done?
    invariant m.Inv()
    invariant LinearMutableMap.WFSimpleIter(m, it)
    invariant nextOut == LinearMutableMap.SimpleIterOutput(m, it)
    invariant m.contents.Keys == old_m.contents.Keys
    invariant it.s <= m.contents.Keys
    invariant forall id | id in m.contents.Keys :: (
      ((id in it.s) ==> (m.contents[id] == (if old_m.contents[id] == JC.State3 then JC.State2 else old_m.contents[id]))))
    invariant forall id | id in m.contents.Keys :: (
      ((id !in it.s) ==> m.contents[id] == old_m.contents[id])
    )
    decreases it.decreaser
    {
      ghost var keySet := m.contents.Keys;
      LinearMutableMap.CountBound(m);

      var value := if nextOut.value == JC.State3 then JC.State2 else nextOut.value;

      ghost var prev_m := m;
      LinearMutableMap.UpdateByIter(inout m, it, value);

      assert LinearMutableMap.SimpleIterOutput(prev_m, it).key == 
        LinearMutableMap.SimpleIterOutput(m, it).key;

      it := LinearMutableMap.SimpleIterInc(m, it);
      nextOut := LinearMutableMap.SimpleIterOutput(m, it);
    }
  }

  datatype Status =
    | StatusLoadingSuperblock
    | StatusLoadingOther
    | StatusReady

  linear datatype Committer = Committer(
  status: Status,

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
    predicate WF()
    {
      && syncReqs.Inv()
      && journalist.Inv()
      && (status == StatusLoadingSuperblock ==>
        && journalist.I().inMemoryJournalFrozen == []
        && journalist.I().inMemoryJournal == []
        && journalist.I().replayJournal == []
        && journalist.I().journalFront == None
        && journalist.I().journalBack == None
        && (superblock1.SuperblockSuccess? ==>
            JC.WFSuperblock(superblock1.value))
        && (superblock2.SuperblockSuccess? ==>
            JC.WFSuperblock(superblock2.value))
      )
      && (status == StatusLoadingOther ==>
        && journalist.I().inMemoryJournalFrozen == []
        && journalist.I().inMemoryJournal == []
        && journalist.I().replayJournal == []
        && JC.WFSuperblock(superblock)
      )
      && (status == StatusReady ==>
        && JC.WFSuperblock(superblock)
      )
    }

    function I() : JC.Variables
    requires WF()
    {
      match status {
        case StatusLoadingSuperblock =>
          JC.LoadingSuperblock(
            superblock1Read,
            superblock2Read,
            superblock1,
            superblock2,
            syncReqs.contents
          )
        case StatusLoadingOther =>
          JC.LoadingOther(
            superblock,
            whichSuperblock as int,
            journalFrontRead,
            journalBackRead,
            journalist.I().journalFront,
            journalist.I().journalBack,
            syncReqs.contents
          )
        case StatusReady =>
          JC.Ready(
            frozenLoc,
            isFrozen,
            frozenJournalPosition as int,
            superblockWrite,
            journalist.I().inMemoryJournalFrozen,
            journalist.I().inMemoryJournal,
            outstandingJournalWrites,
            journalist.I().writtenJournalLen,
            journalist.I().replayJournal,
            superblock,
            whichSuperblock as int,
            commitStatus,
            newSuperblock,
            syncReqs.contents
          )
      }
    }

    predicate Inv()
    {
      && WF()
      && JC.Inv(I())
    }

    static method Constructor() returns (linear self: Committer)
    ensures self.Inv()
    ensures self.I() == JC.LoadingSuperblock(
            None, None,
            JC.SuperblockUnfinished,
            JC.SuperblockUnfinished,
            map[])
    {
      linear var j := JournalistImpl.Journalist.Constructor();
      linear var m := LinearMutableMap.Constructor(128);
      self := Committer(
        StatusLoadingSuperblock,
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
      assert self.I() == JC.LoadingSuperblock(
            None, None,
            JC.SuperblockUnfinished,
            JC.SuperblockUnfinished,
            map[]);
    }

    linear inout method journalAppend(key: Key, value: Value)
    requires old_self.Inv()
    requires old_self.status == StatusReady
    requires old_self.journalist.canAppend(JournalInsert(key, value))

    // [yizhou7] addtional precondition
    requires old_self.I().replayJournal == []
    ensures self.Inv()
    ensures JC.Next(old_self.I(), self.I(), JournalDisk.NoDiskOp, AdvanceOp(UI.PutOp(key, value), false))
    {
      var je := JournalInsert(key, value);
      inout self.journalist.append(je);

      assert JC.Advance(old_self.I(), self.I(), JournalDisk.NoDiskOp, AdvanceOp(UI.PutOp(key, value), false));
      assert JC.NextStep(old_self.I(), self.I(), JournalDisk.NoDiskOp, AdvanceOp(UI.PutOp(key, value), false), JC.AdvanceStep);
    }

    linear inout method journalReplayOne(ghost je: JournalEntry)
    requires old_self.Inv()
    requires old_self.status == StatusReady
    requires old_self.I().replayJournal != []
    requires je == old_self.I().replayJournal[0]

    ensures self.Inv()
    ensures self.status == StatusReady
    ensures JC.Next(old_self.I(), self.I(), JournalDisk.NoDiskOp, AdvanceOp(UI.PutOp(je.key, je.value), true))
    {
      inout self.journalist.replayJournalPop();

      ghost var vop := AdvanceOp(UI.PutOp(je.key, je.value), true);
      assert JC.Replay(old_self.I(), self.I(), JournalDisk.NoDiskOp, vop);
      assert JC.NextStep(old_self.I(), self.I(), JournalDisk.NoDiskOp, vop, JC.ReplayStep);
    }

    linear inout method pageInSuperblockReq(io: DiskIOHandler, which: uint64)
    requires old_self.Inv()
    requires which == 0 || which == 1
    requires which == 0 ==> old_self.superblock1.SuperblockUnfinished?
    requires which == 1 ==> old_self.superblock2.SuperblockUnfinished?
    requires old_self.status.StatusLoadingSuperblock?
    requires io.initialized()
    modifies io
    ensures self.Inv()
    ensures && ValidDiskOp(diskOp(IIO(io)))
      && IDiskOp(diskOp(IIO(io))).bdop.NoDiskOp?
      && JC.Next(old_self.I(), self.I(), IDiskOp(diskOp(IIO(io))).jdop, JournalInternalOp)
    {
      var loc;
      ghost var step := false;

      if which == 0 {
        loc := Superblock1Location();

        if self.superblock1Read.None? {
          var id := RequestRead(io, loc);
          inout self.superblock1Read := Some(id);
          step := true;
        } else {
          print "PageInSuperblockReq: doing nothing\n";
        }
      } else {
        loc := Superblock2Location();

        if self.superblock2Read.None? {
          var id := RequestRead(io, loc);
          inout self.superblock2Read := Some(id);
          step := true;
        } else {
          print "PageInSuperblockReq: doing nothing\n";
        }
      }

      ghost var jdop := IDiskOp(diskOp(IIO(io))).jdop;

      if step {
        assert JC.PageInSuperblockReq(old_self.I(), self.I(), jdop, JournalInternalOp, which as int);
        assert JC.NextStep(old_self.I(), self.I(), jdop, JournalInternalOp, JC.PageInSuperblockReqStep(which as int));
      } else {
        assert JC.NoOp(old_self.I(), self.I(),jdop, JournalInternalOp);
        assert JC.NextStep(old_self.I(), self.I(), jdop, JournalInternalOp, JC.NoOpStep);
      }
    }
  
    linear inout method finishLoadingSuperblockPhase()
    requires old_self.Inv()
    requires old_self.status.StatusLoadingSuperblock?
    requires old_self.superblock1.SuperblockSuccess?
    requires old_self.superblock2.SuperblockSuccess?

    ensures self.Inv()
    ensures JC.Next(old_self.I(), self.I(), JournalDisk.NoDiskOp, SendPersistentLocOp(self.superblock.indirectionTableLoc))
    {
      var idx := if JC.increments1(
          self.superblock1.value.counter, self.superblock2.value.counter)
          then 1 else 0;

      var sup := if idx == 1 then
        self.superblock2.value
      else
        self.superblock1.value;

      inout self.whichSuperblock := idx;
      inout self.superblock := sup;
      inout self.status := StatusLoadingOther;
      inout self.journalFrontRead := None;
      inout self.journalBackRead := None;

      ghost var vop := SendPersistentLocOp(self.superblock.indirectionTableLoc);

      assert JC.FinishLoadingSuperblockPhase(old_self.I(), self.I(), JournalDisk.NoDiskOp, vop);
      assert JC.NextStep(old_self.I(), self.I(), JournalDisk.NoDiskOp, vop,JC.FinishLoadingSuperblockPhaseStep);
    }

    linear inout method FinishLoadingOtherPhase()
    requires old_self.Inv()
    requires old_self.status.StatusLoadingOther?

    // [yizhou7] additional preconditions
    requires JC.JournalFrontIntervalOfSuperblock(old_self.superblock).Some? ==>
          old_self.journalist.hasFront()
    requires JC.JournalBackIntervalOfSuperblock(old_self.superblock).Some? ==>
          old_self.journalist.hasBack()

    ensures self.Inv()
    ensures JC.Next(old_self.I(), self.I(), JournalDisk.NoDiskOp, JournalInternalOp)
    {
      var success := inout self.journalist.parseJournals();

      if success {
        inout self.status := StatusReady;
        inout self.frozenLoc := None;
        inout self.isFrozen := false;
        inout self.frozenJournalPosition := 0;
        inout self.superblockWrite := None;
        inout self.outstandingJournalWrites := {};
        inout self.newSuperblock := None;
        inout self.commitStatus := JC.CommitNone;
        var len := self.superblock.journalLen;
        inout self.journalist.setWrittenJournalLen(len);
      } else {
        print "FinishLoadingOtherPhase: there is replay journal\n";
      }

      assert JC.JournalFrontIntervalOfSuperblock(old_self.superblock).Some? <==>
          old_self.journalist.hasFront();
      assert JC.JournalBackIntervalOfSuperblock(old_self.superblock).Some? <==>
          old_self.journalist.hasBack();

      if success {
        ghost var s := old_self.I();
        ghost var fullRange := (
          if JC.JournalBackIntervalOfSuperblock(s.superblock).Some? then
            JournalRanges.JournalRangeConcat(s.journalFront.value, s.journalBack.value)
          else if JC.JournalFrontIntervalOfSuperblock(s.superblock).Some? then
            s.journalFront.value
          else
            JournalRanges.JournalRangeEmpty()
        );

        ghost var jm := old_self.journalist;

        assert fullRange ==
          (if jm.I().journalFront.Some? then jm.I().journalFront.value else []) +
          (if jm.I().journalBack.Some? then jm.I().journalBack.value else []);

        assert JC.FinishLoadingOtherPhase(old_self.I(), self.I(), JournalDisk.NoDiskOp, JournalInternalOp);
        assert JC.NextStep(old_self.I(), self.I(), JournalDisk.NoDiskOp, JournalInternalOp, JC.FinishLoadingOtherPhaseStep);
      } else {
        assert JC.NoOp(old_self.I(), self.I(), JournalDisk.NoDiskOp, JournalInternalOp);
        assert JC.NextStep(old_self.I(), self.I(), JournalDisk.NoDiskOp, JournalInternalOp, JC.NoOpStep);
      }
    }

    shared function method isReplayEmpty() : (b : bool)
    requires journalist.Inv()
    {
      journalist.isReplayEmpty()
    }

    linear inout method PageInJournalReqFront(io: DiskIOHandler)
    requires old_self.WF()
    requires old_self.status.StatusLoadingOther?
    requires old_self.superblock.journalLen > 0
    requires io.initialized()
    
    // [yizhou7] additional preconditions
    requires old_self.journalFrontRead.None?
    requires old_self.I().journalFront.None?

    modifies io
    ensures self.WF()
    ensures var dop := diskOp(IIO(io));
      && ValidDiskOp(dop)
      && IDiskOp(dop).bdop.NoDiskOp?
      && JC.Next(old_self.I(), self.I(), IDiskOp(dop).jdop, JournalInternalOp)
    {
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
      
      ghost var jdop := IDiskOp(diskOp(IIO(io))).jdop;

      assert JC.PageInJournalReq(old_self.I(), self.I(), jdop, JournalInternalOp, 0);
      assert JC.NextStep(old_self.I(), self.I(), jdop, JournalInternalOp, JC.PageInJournalReqStep(0));
    }
  
    linear inout method PageInJournalReqBack(io: DiskIOHandler)
    requires old_self.WF()
    requires old_self.status.StatusLoadingOther?
    requires old_self.superblock.journalLen > 0
    requires old_self.superblock.journalStart + old_self.superblock.journalLen > NumJournalBlocks()
    requires io.initialized()

    // [yizhou7] additional preconditions
    requires old_self.journalBackRead.None?
    requires old_self.I().journalBack.None?

    modifies io
    ensures self.WF()
    ensures var dop := diskOp(IIO(io));
      && ValidDiskOp(dop)
      && IDiskOp(dop).bdop.NoDiskOp?
      && JC.Next(old_self.I(), self.I(), IDiskOp(dop).jdop, JournalInternalOp)
    {
      var len := self.superblock.journalStart + self.superblock.journalLen - NumJournalBlocks();
      var loc := JournalRangeLocation(0, len);
      var id := RequestRead(io, loc);
      inout self.journalBackRead := Some(id);
      inout self.journalFrontRead :=
          if self.journalFrontRead == Some(id)
            then None else self.journalFrontRead;
      
      ghost var jdop := IDiskOp(diskOp(IIO(io))).jdop;

      assert JC.PageInJournalReq(old_self.I(), self.I(), jdop, JournalInternalOp, 1);
      assert JC.NextStep(old_self.I(), self.I(), jdop, JournalInternalOp, JC.PageInJournalReqStep(1));
    }

    linear inout method pageInJournalResp(io: DiskIOHandler)
    requires old_self.WF()
    requires old_self.status.StatusLoadingOther?
    requires io.diskOp().RespReadOp?
    requires ValidDiskOp(io.diskOp())
    requires ValidJournalLocation(LocOfRespRead(io.diskOp().respRead))
    ensures self.WF()
    ensures var dop := diskOp(IIO(io));
      && ValidDiskOp(dop)
      && IDiskOp(dop).bdop.NoDiskOp?
      && JC.Next(old_self.I(), self.I(), IDiskOp(dop).jdop, JournalInternalOp)
    {
      var id, addr, bytes := io.getReadResult();
      var jr := JournalistParsingImpl.computeJournalRangeOfByteSeq(bytes);
      ghost var jdop := IDiskOp(diskOp(IIO(io))).jdop;

      if jr.Some? {
        assert |jr.value| <= NumJournalBlocks() as int by {
          reveal_ValidJournalLocation();
        }

        if self.journalFrontRead == Some(id) {
          inout self.journalist.setFront(jr.value);
          inout self.journalFrontRead := None;

          assert JC.PageInJournalResp(old_self.I(), self.I(), jdop, JournalInternalOp, 0);
          assert JC.NextStep(old_self.I(), self.I(), jdop, JournalInternalOp, JC.PageInJournalRespStep(0));
        } else if self.journalBackRead == Some(id) {
          inout self.journalist.setBack(jr.value);
          inout self.journalBackRead := None;
          
          assert JC.PageInJournalResp(old_self.I(), self.I(), jdop, JournalInternalOp, 1);
          assert JC.NextStep(old_self.I(), self.I(), jdop, JournalInternalOp, JC.PageInJournalRespStep(1));
        } else {
          assert JC.NoOp(old_self.I(), self.I(), jdop, JournalInternalOp);
          assert JC.NextStep(old_self.I(), self.I(), jdop, JournalInternalOp, JC.NoOpStep);
        }
      } else {
        assert JC.NoOp(old_self.I(), self.I(), jdop, JournalInternalOp);
        assert JC.NextStep(old_self.I(), self.I(), jdop, JournalInternalOp, JC.NoOpStep);
      }
    }

    linear inout method tryFinishLoadingOtherPhase(io: DiskIOHandler)
    requires old_self.Inv()
    requires old_self.status.StatusLoadingOther?
    requires io.initialized()
    modifies io
    ensures self.WF()
    ensures var dop := diskOp(IIO(io));
      && ValidDiskOp(dop)
      && IDiskOp(dop).bdop.NoDiskOp?
      && JC.Next(old_self.I(), self.I(), IDiskOp(dop).jdop, JournalInternalOp)
    {
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
        ghost var jdop := IDiskOp(diskOp(IIO(io))).jdop;
        assert JC.NoOp(old_self.I(), self.I(), jdop, JournalInternalOp);
        assert JC.NextStep(old_self.I(), self.I(), jdop, JournalInternalOp, JC.NoOpStep);
      }
    }

    static function method start_pos_add(a: uint64, b: uint64) : uint64
    requires 0 <= a <= NumJournalBlocks()
    requires 0 <= b <= NumJournalBlocks()
    {
      if a + b >= NumJournalBlocks()
        then a + b - NumJournalBlocks()
        else a + b
    }

    linear inout method WriteOutJournal(io: DiskIOHandler)
    requires io.initialized()
    requires old_self.Inv()
    requires old_self.journalist.I().inMemoryJournalFrozen != []
          || old_self.journalist.I().inMemoryJournal != []

    // [yizhou7] additional precondition
    requires old_self.superblockWrite.None?

    modifies io
    ensures self.WF()
    ensures var dop := diskOp(IIO(io));
        && ValidDiskOp(dop)
        && IDiskOp(dop).bdop.NoDiskOp?
        && JC.Next(
          old_self.I(),
          self.I(),
          IDiskOp(dop).jdop,
          JournalInternalOp)
    {
      var writtenJournalLen := self.journalist.getWrittenJournalLen();
      var doingFrozen := self.journalist.hasFrozenJournal();

      var j;
      if doingFrozen {
        j := inout self.journalist.packageFrozenJournal();
      } else {
        j := inout self.journalist.packageInMemoryJournal();
      }

      var start := start_pos_add(
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
        SyncReqs3to2(inout self.syncReqs);
      }

      ghost var jr := JournalRangeOfByteSeq(j).value;
      assert |jr| == len as int;

      ghost var dop := diskOp(IIO(io));

      if contiguous {
        assert LocOfReqWrite(dop.reqWrite)
            == JournalRangeLocation(start, len);
        assert ValidDiskOp(dop);
      } else {
        assert LocOfReqWrite(dop.reqWrite1)
            == JournalRangeLocation(start, NumJournalBlocks() - start);
        assert LocOfReqWrite(dop.reqWrite2)
            == JournalRangeLocation(0, len - (NumJournalBlocks() - start));
        JournalBytesSplit(j, len as int,
            NumJournalBlocks() as int - start as int);
        assert ValidDiskOp(dop);
      }

      assert JC.WriteBackJournalReq(
          old_self.I(),
          self.I(),
          IDiskOp(dop).jdop,
          JournalInternalOp,
          jr);
      assert JC.NextStep(
          old_self.I(),
          self.I(),
          IDiskOp(dop).jdop,
          JournalInternalOp,
          JC.WriteBackJournalReqStep(jr));
    }

    linear inout method writeOutSuperblockAdvanceLog(io: DiskIOHandler)
    requires io.initialized()
    requires old_self.Inv()
    requires old_self.status == StatusReady

    // [yizhou7] additional preconditions
    requires old_self.commitStatus.CommitNone?
    requires old_self.outstandingJournalWrites == {}
    requires old_self.journalist.I().inMemoryJournalFrozen == []

    modifies io
    ensures self.WF()
    ensures var dop := diskOp(IIO(io));
        && ValidDiskOp(dop)
        && IDiskOp(dop).bdop.NoDiskOp?
        && JC.Next(old_self.I(), self.I(), IDiskOp(dop).jdop, JournalInternalOp)
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
          SSI.SectorSuperblock(newSuperblock));
      inout self.newSuperblock := Some(newSuperblock);
      inout self.superblockWrite := Some(id);
      inout self.commitStatus := JC.CommitAdvanceLog;

      assert ValidDiskOp(diskOp(IIO(io)));
      assert JC.WriteBackSuperblockReq_AdvanceLog(old_self.I(), self.I(), IDiskOp(diskOp(IIO(io))).jdop, JournalInternalOp);
      assert JC.NextStep(old_self.I(), self.I(), IDiskOp(diskOp(IIO(io))).jdop, JournalInternalOp, JC.WriteBackSuperblockReq_AdvanceLog_Step);
    }

    linear inout method writeOutSuperblockAdvanceLocation(io: DiskIOHandler)
    requires io.initialized()
    requires old_self.Inv()
    requires old_self.status == StatusReady
    requires old_self.frozenLoc.Some?

    // [yizhou7] additional preconditions
    requires old_self.commitStatus.CommitNone?
    requires old_self.outstandingJournalWrites == {}
    requires old_self.journalist.I().inMemoryJournalFrozen == []

    modifies io
    ensures self.WF()
    ensures var dop := diskOp(IIO(io));
        && ValidDiskOp(dop)
        && IDiskOp(dop).bdop.NoDiskOp?
        && JC.Next(old_self.I(), self.I(), IDiskOp(dop).jdop, JournalInternalOp)
    {
      var writtenJournalLen := self.journalist.getWrittenJournalLen();
      var newSuperblock := SectorType.Superblock(
        JC.IncrementSuperblockCounter(self.superblock.counter),
        start_pos_add(
            self.superblock.journalStart,
            self.frozenJournalPosition),
        writtenJournalLen - self.frozenJournalPosition,
        self.frozenLoc.value
      );
      assert JC.WFSuperblock(newSuperblock);
      var loc := if self.whichSuperblock == 0 then Superblock2Location() else Superblock1Location();
      var id := RequestWrite(io, loc,
          SSI.SectorSuperblock(newSuperblock));
      inout self.newSuperblock := Some(newSuperblock);
      inout self.superblockWrite := Some(id);
      inout self.commitStatus := JC.CommitAdvanceLocation;

      assert ValidDiskOp(diskOp(IIO(io)));
      assert JC.WriteBackSuperblockReq_AdvanceLocation(old_self.I(), self.I(), IDiskOp(diskOp(IIO(io))).jdop, JournalInternalOp);
      assert JC.NextStep(old_self.I(), self.I(), IDiskOp(diskOp(IIO(io))).jdop, JournalInternalOp, JC.WriteBackSuperblockReq_AdvanceLocation_Step);
    }

    linear inout method freeze()
    requires old_self.WF()

    // [yizhou7] additional preconditions
    requires old_self.superblockWrite.None?
    requires old_self.status == StatusReady
    requires old_self.frozenLoc != Some(old_self.superblock.indirectionTableLoc)
    requires old_self.journalist.I().replayJournal == []

    ensures self.WF()
    ensures JC.Next(old_self.I(), self.I(), JournalDisk.NoDiskOp, FreezeOp)
    {
      var writtenJournalLen := self.journalist.getWrittenJournalLen();
      inout self.journalist.freeze();
      inout self.frozenLoc := None;
      inout self.frozenJournalPosition := writtenJournalLen;
      inout self.isFrozen := true;
      SyncReqs3to2(inout self.syncReqs);

      assert JC.Freeze(old_self.I(), self.I(), JournalDisk.NoDiskOp,FreezeOp);
      assert JC.NextStep(old_self.I(), self.I(), JournalDisk.NoDiskOp, FreezeOp, JC.FreezeStep);
    }

    linear inout method receiveFrozenLoc(loc: Location)
    requires old_self.WF()

    // [yizhou7] additional preconditions
    requires old_self.status == StatusReady
    requires old_self.isFrozen
    requires !old_self.frozenLoc.Some?
    requires ValidIndirectionTableLocation(loc)

    ensures self.WF()
    ensures JC.Next(old_self.I(), self.I(), JournalDisk.NoDiskOp, SendFrozenLocOp(loc))
    {
      inout self.frozenLoc := Some(loc);

      assert JC.ReceiveFrozenLoc(old_self.I(), self.I(), JournalDisk.NoDiskOp, SendFrozenLocOp(loc));
      assert JC.NextStep(old_self.I(), self.I(), JournalDisk.NoDiskOp, SendFrozenLocOp(loc), JC.ReceiveFrozenLocStep);
    }

    // == pushSync ==
    shared method freeId() returns (id: uint64)
    requires syncReqs.Inv()
    ensures (id != 0) ==> (id !in syncReqs.contents)
    {
      var maxId := LinearMutableMap.MaxKey(this.syncReqs);
      if maxId == 0xffff_ffff_ffff_ffff {
        id := 0;
      } else {
        id := maxId + 1;
      }
    }

    linear inout method pushSync()
    returns (id: uint64)
    requires old_self.Inv()
    ensures self.WF()
    ensures JC.Next(old_self.I(), self.I(), JournalDisk.NoDiskOp, if id == 0 then JournalInternalOp else PushSyncOp(id as int))
    {
      id := self.freeId();
      if id != 0 && self.syncReqs.count < 0x2000_0000_0000_0000 {
        LinearMutableMap.Insert(inout self.syncReqs, id, JC.State3);

        assert JC.PushSyncReq(old_self.I(), self.I(), JournalDisk.NoDiskOp, PushSyncOp(id as int), id);
        assert JC.NextStep(old_self.I(), self.I(), JournalDisk.NoDiskOp, PushSyncOp(id as int),JC.PushSyncReqStep(id));
      } else {
        id := 0;

        assert JC.NoOp(old_self.I(), self.I(), JournalDisk.NoDiskOp, JournalInternalOp);
        assert JC.NextStep(old_self.I(), self.I(), JournalDisk.NoDiskOp, JournalInternalOp, JC.NoOpStep);
      }
    }

    // == popSync ==

    linear inout method popSync(id: uint64)
    requires old_self.Inv()

    // [yizhou7] additional preconditions
    requires id in old_self.syncReqs.contents
    requires old_self.syncReqs.contents[id] == JC.State1

    ensures self.WF()
    ensures JC.Next(old_self.I(), self.I(), JournalDisk.NoDiskOp,PopSyncOp(id as int))
    {
      LinearMutableMap.Remove(inout self.syncReqs, id);
      assert JC.PopSyncReq(old_self.I(), self.I(), JournalDisk.NoDiskOp, PopSyncOp(id as int), id);
      assert JC.NextStep(old_self.I(), self.I(), JournalDisk.NoDiskOp, PopSyncOp(id as int), JC.PopSyncReqStep(id));
    }

    linear inout method tryAdvanceLog(io: DiskIOHandler)
    returns (wait: bool)
    requires old_self.Inv()
    requires io.initialized()
    requires old_self.status == StatusReady
    modifies io
    ensures self.WF()
    ensures var dop := diskOp(IIO(io));
        && ValidDiskOp(dop)
        && IDiskOp(dop).bdop.NoDiskOp?
        && JC.Next(old_self.I(), self.I(), IDiskOp(dop).jdop, JournalInternalOp)
    {
      wait := false;
      var hasFrozen := self.journalist.hasFrozenJournal();
      var hasInMem := self.journalist.hasInMemoryJournal();
      if self.superblockWrite.None? {
        if hasFrozen || hasInMem {
          inout self.WriteOutJournal(io);
        } else if (self.outstandingJournalWrites == {}) {
          inout self.writeOutSuperblockAdvanceLog(io);
        } else {
          wait := true;

          assert JC.NoOp(old_self.I(), self.I(), JournalDisk.NoDiskOp, JournalInternalOp);
          assert JC.NextStep(old_self.I(), self.I(), JournalDisk.NoDiskOp, JournalInternalOp, JC.NoOpStep);
        }
      } else {
        wait := true;

        assert JC.NoOp(old_self.I(), self.I(), JournalDisk.NoDiskOp, JournalInternalOp);
        assert JC.NextStep(old_self.I(), self.I(), JournalDisk.NoDiskOp, JournalInternalOp, JC.NoOpStep);
      }
    }

    linear inout method tryAdvanceLocation(io: DiskIOHandler)
    returns (wait: bool)
    requires old_self.Inv()
    requires io.initialized()
    requires old_self.status == StatusReady
    requires old_self.frozenLoc.Some?
    modifies io
    ensures self.WF()
    ensures var dop := diskOp(IIO(io));
        && ValidDiskOp(dop)
        && IDiskOp(dop).bdop.NoDiskOp?
        && JC.Next(old_self.I(), self.I(), IDiskOp(dop).jdop, JournalInternalOp)
    {
      wait := false;
      var hasFrozen := self.journalist.hasFrozenJournal();
      var hasInMem := self.journalist.hasInMemoryJournal();
      if self.superblockWrite.None? {
        if hasFrozen || hasInMem {
          inout self.WriteOutJournal(io);
        } else if (self.outstandingJournalWrites == {}) {
          inout self.writeOutSuperblockAdvanceLocation(io);
        } else {
          wait := true;

          assert JC.NoOp(old_self.I(), self.I(), JournalDisk.NoDiskOp, JournalInternalOp);
          assert JC.NextStep(old_self.I(), self.I(), JournalDisk.NoDiskOp, JournalInternalOp, JC.NoOpStep);
        }
      } else {
        wait := true;

        assert JC.NoOp(old_self.I(), self.I(), JournalDisk.NoDiskOp, JournalInternalOp);
        assert JC.NextStep(old_self.I(), self.I(), JournalDisk.NoDiskOp, JournalInternalOp, JC.NoOpStep);
      }
    }

    linear inout method writeBackSuperblockResp(ghost io: IO)
    requires old_self.Inv()
    
    // [yizhou7] additional preconditions
    requires ValidDiskOp(diskOp(io))
    requires IDiskOp(diskOp(io)).jdop.RespWriteSuperblockOp?
    requires Some(io.id) == old_self.superblockWrite

    ensures self.WF()
    ensures JC.Next(old_self.I(), self.I(), IDiskOp(diskOp(io)).jdop, 
      if old_self.status.StatusReady? && old_self.commitStatus.CommitAdvanceLocation? then CleanUpOp else JournalInternalOp)
    {
      // CommitterCommitModel.SyncReqs2to1Correct(old_self.syncReqs);

      if self.status.StatusReady? && self.commitStatus.CommitAdvanceLocation? {
        var writtenJournalLen := self.journalist.getWrittenJournalLen();
        inout self.superblockWrite := None;
        inout self.superblock := self.newSuperblock.value;
        inout self.newSuperblock := None;
        inout self.whichSuperblock := if self.whichSuperblock == 0 then 1 else 0;
        SyncReqs2to1(inout self.syncReqs);
        var position := self.frozenJournalPosition;
        inout self.journalist.updateWrittenJournalLen(
              writtenJournalLen - position);
        inout self.frozenJournalPosition := 0;
        inout self.frozenLoc := None;
        inout self.isFrozen := false;
        inout self.commitStatus := JC.CommitNone;

        assert JC.WriteBackSuperblockResp(old_self.I(), self.I(), IDiskOp(diskOp(io)).jdop, CleanUpOp);
        assert JC.NextStep(old_self.I(), self.I(), IDiskOp(diskOp(io)).jdop, CleanUpOp,JC.WriteBackSuperblockRespStep);
      } else if self.status.StatusReady? && self.commitStatus.CommitAdvanceLog? {
        inout self.superblockWrite := None;
        inout self.superblock := self.newSuperblock.value;
        inout self.newSuperblock := None;
        inout self.whichSuperblock := if self.whichSuperblock == 0 then 1 else 0;
        SyncReqs2to1(inout self.syncReqs);
        inout self.commitStatus := JC.CommitNone;
        assert JC.WriteBackSuperblockResp(
          old_self.I(),
          self.I(),
          IDiskOp(diskOp(io)).jdop,
          JournalInternalOp);
        assert JC.NextStep(
          old_self.I(),
          self.I(),
          IDiskOp(diskOp(io)).jdop,
          JournalInternalOp,
          JC.WriteBackSuperblockRespStep);
      } else {
        print "writeBackSuperblockResp: didn't do anything\n";
        assert JC.NoOp(old_self.I(), self.I(), IDiskOp(diskOp(io)).jdop, JournalInternalOp);
        assert JC.NextStep(old_self.I(), self.I(), IDiskOp(diskOp(io)).jdop, JournalInternalOp, JC.NoOpStep);
      }
    }

    linear inout method writeBackJournalResp(io: DiskIOHandler)
    requires old_self.WF()
    requires io.diskOp().RespWriteOp?

    // [yizhou7] addtional preconditions
    requires ValidJournalLocation(LocOfRespWrite(diskOp(IIO(io)).respWrite))
    requires old_self.status.StatusReady?

    ensures self.WF()
    ensures JC.Next(old_self.I(), self.I(), IDiskOp(diskOp(IIO(io))).jdop, JournalInternalOp)

    {
      var id, addr, len := io.getWriteResult();
      ghost var contained := id in self.outstandingJournalWrites;
  
      inout self.outstandingJournalWrites :=
          self.outstandingJournalWrites - {id};

      ghost var jdop := IDiskOp(diskOp(IIO(io))).jdop;

      if contained {
        assert JC.WriteBackJournalResp(old_self.I(), self.I(), jdop, JournalInternalOp);
        assert JC.NextStep(old_self.I(), self.I(), jdop, JournalInternalOp, JC.WriteBackJournalRespStep);
      } else {
        assert JC.NoOp(old_self.I(), self.I(), jdop, JournalInternalOp);
        assert JC.NextStep(old_self.I(), self.I(), jdop, JournalInternalOp, JC.NoOpStep);
      }
    }

    linear inout method readSuperblockResp(io: DiskIOHandler, which: uint64)
    requires old_self.WF()
    requires io.diskOp().RespReadOp?

    // [yizhou7] addtional preconditions
    requires ValidDiskOp(diskOp(IIO(io)))
    requires diskOp(IIO(io)).RespReadOp?
    requires which == 0 || which == 1
    requires which == 0 ==>
      LocOfRespRead(diskOp(IIO(io)).respRead) == Superblock1Location()
    requires which == 1 ==>
      LocOfRespRead(diskOp(IIO(io)).respRead) == Superblock2Location()

    ensures self.WF()
    ensures JC.Next(old_self.I(), self.I(), IDiskOp(diskOp(IIO(io))).jdop, JournalInternalOp)
    {
      var id;
      linear var sector;
      id, sector := IOImpl.ReadSector(io);
      var res := (if sector.lSome? && sector.value.SectorSuperblock?
          then JC.SuperblockSuccess(sector.value.superblock)
          else JC.SuperblockCorruption);
      if which == 0 {
        if Some(id) == self.superblock1Read {
          inout self.superblock1 := res;
          inout self.superblock1Read := None;
        } else {
          print "readSuperblockResp did nothing\n";
        }
      } else {
        if Some(id) == self.superblock2Read {
          inout self.superblock2 := res;
          inout self.superblock2Read := None;
        } else {
          print "readSuperblockResp did nothing\n";
        }
      }
      linear match sector {
        case lSome(value) => value.Free();
        case lNone() => {}
      }

      IOModel.ReadSectorCorrect(IIO(io));
      ghost var dop := IDiskOp(diskOp(IIO(io))).jdop;

      assert dop.RespReadSuperblockOp?;
      assert dop.which == which as int;

      if old_self.status.StatusLoadingSuperblock?
          && (which == 0 ==> Some(dop.id) == old_self.superblock1Read)
          && (which == 1 ==> Some(dop.id) == old_self.superblock2Read)
      {
        assert JC.PageInSuperblockResp(old_self.I(), self.I(), dop, JournalInternalOp, which as int);
        assert JC.NextStep(old_self.I(), self.I(), dop, JournalInternalOp, JC.PageInSuperblockRespStep(which as int));
      } else {
        assert JC.NoOp(old_self.I(), self.I(), dop, JournalInternalOp);
        assert JC.NextStep(old_self.I(), self.I(), dop, JournalInternalOp, JC.NoOpStep);
      }
    }
  }
}
