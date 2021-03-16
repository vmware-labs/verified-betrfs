// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../BlockCacheSystem/JournalDisk.i.dfy"
include "JournalRange.i.dfy"
include "JournalInterval.i.dfy"
include "../Versions/VOp.i.dfy"

module JournalCache {
  import opened Maps
  import opened Options
  import opened NativeTypes
  import opened DiskLayout
  import opened Sequences
  import opened Journal
  import opened JournalRanges
  import opened JournalIntervals
  import opened SectorType
  import opened ViewOp

  import Disk = JournalDisk

  type ReqId = Disk.ReqId

  type DiskOp = Disk.DiskOp

  // BlockCache stuff

  datatype SyncReqStatus = State1 | State2 | State3

  datatype SuperblockReadResult =
      | SuperblockSuccess(value: Superblock)
      | SuperblockUnfinished
      | SuperblockCorruption

  datatype CommitStatus =
    | CommitNone
    | CommitAdvanceLog
    | CommitAdvanceLocation

  datatype Variables =
    | Ready(
        frozenLoc: Option<Location>,

        isFrozen: bool,
        ghost frozenJournalPosition: int,

        superblockWrite: Option<ReqId>,

        inMemoryJournalFrozen: seq<JournalEntry>,
        inMemoryJournal: seq<JournalEntry>,
        outstandingJournalWrites: set<ReqId>,
        ghost writtenJournalLen: int,

        replayJournal: seq<JournalEntry>,

        superblock: Superblock,
        ghost whichSuperblock: int,

        commitStatus: CommitStatus,
        newSuperblock: Option<Superblock>,

        syncReqs: map<uint64, SyncReqStatus>
      )

    | LoadingOther(
        superblock: Superblock,
        ghost whichSuperblock: int,

        journalFrontRead: Option<ReqId>,
        journalBackRead: Option<ReqId>,

        journalFront: Option<JournalRange>,
        journalBack: Option<JournalRange>,

        syncReqs: map<uint64, SyncReqStatus>
      )

    | LoadingSuperblock(
        outstandingSuperblock1Read: Option<ReqId>,
        outstandingSuperblock2Read: Option<ReqId>,
        superblock1: SuperblockReadResult,
        superblock2: SuperblockReadResult,

        syncReqs: map<uint64, SyncReqStatus>
      )

  function method IncrementSuperblockCounter(i: uint64) : uint64
  {
    if i == 0xffff_ffff_ffff_ffff then
      0
    else
      i + 1
  }

  predicate method increments1(i: uint64, j: uint64) {
    j == IncrementSuperblockCounter(i)
  }

  function SelectSuperblockIndex(
      superblock1: Superblock, 
      superblock2: Superblock) : int
  {
    if increments1(superblock1.counter, superblock2.counter) then
      1
    else
      0
  }

  function SelectSuperblock(
      superblock1: Superblock, 
      superblock2: Superblock) : Superblock
  {
    if SelectSuperblockIndex(superblock1, superblock2) == 1 then
      superblock2
    else
      superblock1
  }

  function syncReqs3to2(syncReqs: map<uint64, SyncReqStatus>) : map<uint64, SyncReqStatus>
  {
    map id | id in syncReqs :: (if syncReqs[id] == State3 then State2 else syncReqs[id])
  }

  function syncReqs2to1(syncReqs: map<uint64, SyncReqStatus>) : map<uint64, SyncReqStatus>
  {
    map id | id in syncReqs :: (if syncReqs[id] == State2 then State1 else syncReqs[id])
  }

  // Journal is written in a circular array, so to load the log
  // we may have to read back two chunks.

  function JournalFrontIntervalOfSuperblock(superblock: Superblock) : Option<JournalInterval>
  requires superblock.journalStart < NumJournalBlocks()
  {
    JournalFrontInterval(
      superblock.journalStart as int,
      superblock.journalLen as int)
  }

  function JournalBackIntervalOfSuperblock(superblock: Superblock) : Option<JournalInterval>
  requires superblock.journalStart < NumJournalBlocks()
  requires superblock.journalLen <= NumJournalBlocks()
  {
    JournalBackInterval(
      superblock.journalStart as int,
      superblock.journalLen as int)
  }

  predicate method WFSuperblock(superblock: Superblock)
  {
    && superblock.journalStart < NumJournalBlocks()
    && superblock.journalLen <= NumJournalBlocks()
    && ValidIndirectionTableLocation(superblock.indirectionTableLoc)
  }

  datatype JournalStep =
      | JSNew(entries: seq<JournalEntry>)
      | JSReplay(entries: seq<JournalEntry>)

  datatype Step =
    | WriteBackJournalReqStep(jr: JournalRange)
    | WriteBackJournalRespStep
    | WriteBackSuperblockReq_AdvanceLog_Step
    | WriteBackSuperblockReq_AdvanceLocation_Step
    | WriteBackSuperblockRespStep
    | PageInJournalReqStep(ghost which: int)
    | PageInJournalRespStep(ghost which: int)
    | PageInSuperblockReqStep(ghost which: int)
    | PageInSuperblockRespStep(ghost which: int)
    | FinishLoadingSuperblockPhaseStep
    | FinishLoadingOtherPhaseStep
    | FreezeStep
    | ReceiveFrozenLocStep
    | AdvanceStep
    | ReplayStep
    | PushSyncReqStep(id: uint64)
    | PopSyncReqStep(id: uint64)
    | NoOpStep

  predicate WriteBackJournalReq(s: Variables, s': Variables, dop: DiskOp, vop: VOp, jr: JournalRange)
  {
    && vop.JournalInternalOp?

    && s.Ready?

    && var j :=
        if s.inMemoryJournalFrozen == [] then
          s.inMemoryJournal
        else
          s.inMemoryJournalFrozen;

    && JournalRangeParses(jr, j)
    && JournalRangeLen(jr) + s.writtenJournalLen <= NumJournalBlocks() as int
    && JournalRangeLen(jr) > 0
    && s.superblockWrite.None?
    && s.superblock.journalStart < NumJournalBlocks()
    && 0 <= s.writtenJournalLen <= NumJournalBlocks() as int
    && var startPos := JournalPosAdd(
        s.superblock.journalStart as int,
        s.writtenJournalLen);

    && var writtenJournalLen' :=
        s.writtenJournalLen + JournalRangeLen(jr);

    && var frozenJournalPosition' := 
        if s.inMemoryJournalFrozen == [] then
          s.frozenJournalPosition
        else
          writtenJournalLen';

    && var inMemoryJournal' :=
        if s.inMemoryJournalFrozen == [] then
          []
        else
          s.inMemoryJournal;

    && var syncReqs' :=
        if s.inMemoryJournalFrozen == [] then
          syncReqs3to2(s.syncReqs)
        else
          s.syncReqs;

    && var inMemoryJournalFrozen' := [];

    && dop.ReqWriteJournalOp?
    && dop.reqWriteJournal.journal == jr
    && dop.reqWriteJournal.start == startPos
    && s' == s
        .(outstandingJournalWrites := s.outstandingJournalWrites + (if dop.id2.Some? then {dop.id1, dop.id2.value} else {dop.id1}))
        .(writtenJournalLen := writtenJournalLen')
        .(frozenJournalPosition := frozenJournalPosition')
        .(inMemoryJournal := inMemoryJournal')
        .(inMemoryJournalFrozen := inMemoryJournalFrozen')
        .(syncReqs := syncReqs')
  }

  predicate WriteBackJournalResp(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.JournalInternalOp?

    && s.Ready?
    && dop.RespWriteJournalOp?
    && dop.id in s.outstandingJournalWrites
    && s' == s
       .(outstandingJournalWrites := s.outstandingJournalWrites - {dop.id})
  }

  predicate WriteBackSuperblockReq_AdvanceLog(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.JournalInternalOp?

    && s.Ready?
    && dop.ReqWriteSuperblockOp?
    && s.commitStatus.CommitNone?
    && s.outstandingJournalWrites == {}
    && s.inMemoryJournalFrozen == []
    && dop.which == (if s.whichSuperblock == 0 then 1 else 0)
    && 0 <= s.writtenJournalLen <= NumJournalBlocks() as int
    && var newSuperblock := Superblock(
      IncrementSuperblockCounter(s.superblock.counter),
      s.superblock.journalStart,
      s.writtenJournalLen as uint64,
      s.superblock.indirectionTableLoc
    );
    && dop.reqWriteSuperblock.superblock == newSuperblock
    && s' == s
        .(newSuperblock := Some(newSuperblock))
        .(superblockWrite := Some(dop.id))
        .(commitStatus := CommitAdvanceLog)
  }

  predicate WriteBackSuperblockReq_AdvanceLocation(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.JournalInternalOp?

    && s.Ready?
    && dop.ReqWriteSuperblockOp?
    && s.frozenLoc.Some?
    && s.commitStatus.CommitNone?
    && s.outstandingJournalWrites == {}
    && s.inMemoryJournalFrozen == []
    && dop.which == (if s.whichSuperblock == 0 then 1 else 0)
    && 0 <= s.superblock.journalStart < NumJournalBlocks()
    && 0 <= s.frozenJournalPosition
         <= s.writtenJournalLen
         <= NumJournalBlocks() as int
    && var newSuperblock := Superblock(
      IncrementSuperblockCounter(s.superblock.counter),
      JournalPosAdd(
          s.superblock.journalStart as int,
          s.frozenJournalPosition) as uint64,
      (s.writtenJournalLen - s.frozenJournalPosition) as uint64,
      s.frozenLoc.value
    );
    && dop.reqWriteSuperblock.superblock == newSuperblock
    && s' == s
        .(newSuperblock := Some(newSuperblock))
        .(superblockWrite := Some(dop.id))
        .(commitStatus := CommitAdvanceLocation)
  }

  predicate WriteBackSuperblockResp(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && s.Ready?
    && dop.RespWriteSuperblockOp?
    && Some(dop.id) == s.superblockWrite
    && s.newSuperblock.Some?
    && s'.Ready?
    && (s.commitStatus.CommitAdvanceLocation? ==>
      && vop.CleanUpOp?
      && s' == s
          .(superblockWrite := None)
          .(superblock := s.newSuperblock.value)
          .(newSuperblock := None)
          .(whichSuperblock := if s.whichSuperblock == 0 then 1 else 0)
          .(syncReqs := syncReqs2to1(s.syncReqs))
          .(writtenJournalLen := s.writtenJournalLen - s.frozenJournalPosition)
          .(frozenJournalPosition := 0)
          .(frozenLoc := None)
          .(isFrozen := false)
          .(commitStatus := CommitNone)
    )
    && (s.commitStatus.CommitAdvanceLog? ==>
      && vop.JournalInternalOp?
      && s' == s
          .(superblockWrite := None)
          .(superblock := s.newSuperblock.value)
          .(newSuperblock := None)
          .(whichSuperblock := if s.whichSuperblock == 0 then 1 else 0)
          .(syncReqs := syncReqs2to1(s.syncReqs))
          .(commitStatus := CommitNone)
    )
  }

  predicate PageInJournalReq(s: Variables, s': Variables, dop: DiskOp, vop: VOp, which: int)
  {
    && vop.JournalInternalOp?

    && dop.ReqReadJournalOp?
    && s.LoadingOther?
    && (which == 0 || which == 1)
    && s.superblock.journalStart < NumJournalBlocks()
    && s.superblock.journalLen <= NumJournalBlocks()
    && (which == 0 ==>
      && JournalFrontIntervalOfSuperblock(s.superblock).Some?
      && dop.interval
          == JournalFrontIntervalOfSuperblock(s.superblock).value
      && s.journalFrontRead.None?
      && s.journalFront.None?
      && s' == s.(journalFrontRead := Some(dop.id))
                .(journalBackRead :=
                  if s.journalBackRead == Some(dop.id) then None else s.journalBackRead)
    )
    && (which == 1 ==>
      && JournalBackIntervalOfSuperblock(s.superblock).Some?
      && dop.interval
          == JournalBackIntervalOfSuperblock(s.superblock).value
      && s.journalBackRead.None?
      && s.journalBack.None?
      && s' == s.(journalBackRead := Some(dop.id))
                .(journalFrontRead :=
                  if s.journalFrontRead == Some(dop.id) then None else s.journalFrontRead)
    )
  }

  predicate PageInJournalResp(s: Variables, s': Variables, dop: DiskOp, vop: VOp, which: int)
  {
    && vop.JournalInternalOp?

    && dop.RespReadJournalOp?
    && s.LoadingOther?
    && dop.journal.Some?
    && (which == 0 || which == 1)
    && (which == 0 ==>
      && s.journalFrontRead == Some(dop.id)
      && s' == s
          .(journalFrontRead := None)
          .(journalFront := Some(dop.journal.value))
    )
    && (which == 1 ==>
      && s.journalBackRead == Some(dop.id)
      && s' == s
          .(journalBackRead := None)
          .(journalBack := Some(dop.journal.value))
    )
  }

  predicate PageInSuperblockReq(s: Variables, s': Variables, dop: DiskOp, vop: VOp, which: int)
  {
    && vop.JournalInternalOp?

    && dop.ReqReadSuperblockOp?
    && s.LoadingSuperblock?
    && dop.which == which
    && (which == 0 || which == 1)
    && (which == 0 ==> 
      && s.outstandingSuperblock1Read.None?
      && s.superblock1.SuperblockUnfinished?
      && s' == s.(outstandingSuperblock1Read := Some(dop.id))
    )
    && (which == 1 ==> 
      && s.outstandingSuperblock2Read.None?
      && s.superblock2.SuperblockUnfinished?
      && s' == s.(outstandingSuperblock2Read := Some(dop.id))
    )
  }

  predicate PageInSuperblockResp(s: Variables, s': Variables, dop: DiskOp, vop: VOp, which: int)
  {
    && vop.JournalInternalOp?

    && dop.RespReadSuperblockOp?
    && s.LoadingSuperblock?
    && var sup := (
        if dop.superblock.Some? &&
            WFSuperblock(dop.superblock.value) then
          SuperblockSuccess(dop.superblock.value)
        else
          SuperblockCorruption
    );
    && which == dop.which
    && (which == 0 || which == 1)
    && (which == 0 ==> 
      && s.outstandingSuperblock1Read == Some(dop.id)
      && s' == s
          .(outstandingSuperblock1Read := None)
          .(superblock1 := sup)
    )
    && (which == 1 ==> 
      && s.outstandingSuperblock2Read == Some(dop.id)
      && s' == s
          .(outstandingSuperblock2Read := None)
          .(superblock2 := sup)
    )
  }

  predicate FinishLoadingSuperblockPhase(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.SendPersistentLocOp?

    && dop.NoDiskOp?
    && s.LoadingSuperblock?
    // TODO account for case where one superblock or the other is corrupt
    && s.superblock1.SuperblockSuccess?
    && s.superblock2.SuperblockSuccess?
    && (s.superblock1.SuperblockSuccess?
        || s.superblock2.SuperblockSuccess?)
    //&& (s.superblock1.SuperblockSuccess? && s.superblock2.SuperblockSuccess? ==>
    && s' == LoadingOther(
        SelectSuperblock(s.superblock1.value, s.superblock2.value),
        SelectSuperblockIndex(s.superblock1.value, s.superblock2.value),
        None, None,
        None, None,
        s.syncReqs)
    && vop.loc == 
        SelectSuperblock(s.superblock1.value, s.superblock2.value).indirectionTableLoc
    /*)
    && (s.superblock1.SuperblockCorruption? ==>
      s' == LoadingOther(
        s.superblock2.value,
        1,
        None, None,
        None, None,
        s.syncReqs)
    )
    && (s.superblock2.SuperblockCorruption? ==>
      s' == LoadingOther(
        s.superblock1.value,
        0,
        None, None,
        None, None,
        s.syncReqs)
    )*/
  }

  predicate FinishLoadingOtherPhase(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.JournalInternalOp?

    && dop.NoDiskOp?
    && s.LoadingOther?
    && s.superblock.journalStart < NumJournalBlocks()
    && s.superblock.journalLen <= NumJournalBlocks()
    && (JournalFrontIntervalOfSuperblock(s.superblock).Some? ==> s.journalFront.Some?)
    && (JournalBackIntervalOfSuperblock(s.superblock).Some? ==> s.journalBack.Some?)

    && var fullRange := (
        if JournalBackIntervalOfSuperblock(s.superblock).Some? then
          JournalRangeConcat(s.journalFront.value, s.journalBack.value)
        else if JournalFrontIntervalOfSuperblock(s.superblock).Some? then
          s.journalFront.value
        else
          JournalRangeEmpty()
    );

    && s'.Ready?
    && s'.superblockWrite == None
    && s'.inMemoryJournalFrozen == []
    && s'.inMemoryJournal == []
    && s'.outstandingJournalWrites == {}
    && s'.writtenJournalLen == s.superblock.journalLen as int
    && JournalRangeParses(fullRange, s'.replayJournal)
    && s'.superblock == s.superblock
    && s'.whichSuperblock == s.whichSuperblock
    && s'.newSuperblock == None
    && s'.syncReqs == s.syncReqs
    && s'.isFrozen == false
    && s'.frozenLoc == None
    && s'.commitStatus == CommitNone
  }

  predicate Freeze(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.FreezeOp?

    && s.Ready?
    && dop.NoDiskOp?
    && s.superblockWrite.None?
    && s.frozenLoc != Some(s.superblock.indirectionTableLoc)
    && s.replayJournal == []
    && s' ==
        s.(frozenLoc := None)
         .(inMemoryJournalFrozen := s.inMemoryJournalFrozen + s.inMemoryJournal)
         .(inMemoryJournal := [])
         .(frozenJournalPosition := s.writtenJournalLen)
         .(syncReqs := syncReqs3to2(s.syncReqs))
         .(isFrozen := true)
  }

  predicate ReceiveFrozenLoc(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.SendFrozenLocOp?
    && dop.NoDiskOp?
    && s.Ready?
    && s.isFrozen
    && !s.frozenLoc.Some?
    && ValidIndirectionTableLocation(vop.loc)
    && s' == s.(frozenLoc := Some(vop.loc))
  }

  predicate Advance(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.AdvanceOp?
    && !vop.replay
    && dop.NoDiskOp?
    && var new_je := JournalEntriesForUIOp(vop.uiop);
    && s.Ready?
    && s.replayJournal == []
    && s' == s.(inMemoryJournal := s.inMemoryJournal + new_je)
  }

  predicate Replay(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && vop.AdvanceOp?
    && vop.replay
    && dop.NoDiskOp?
    && var replayed_je := JournalEntriesForUIOp(vop.uiop);
    && s.Ready?
    && s'.Ready?
    && s' == s.(replayJournal := s'.replayJournal)
    && s.replayJournal == replayed_je + s'.replayJournal
  }

  predicate PushSyncReq(s: Variables, s': Variables, dop: DiskOp, vop: VOp, id: uint64)
  {
    && vop.PushSyncOp?
    && vop.id == id as int

    && dop.NoDiskOp?
    && id !in s.syncReqs
    && s' == s.(syncReqs := s.syncReqs[id := State3])
  }

  predicate PopSyncReq(s: Variables, s': Variables, dop: DiskOp, vop: VOp, id: uint64)
  {
    && vop.PopSyncOp?
    && vop.id == id as int

    && dop.NoDiskOp?
    && id in s.syncReqs
    && s.syncReqs[id] == State1
    && s' == s.(syncReqs := MapRemove1(s.syncReqs, id))
  }

  predicate NoOp(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
  {
    && (vop.JournalInternalOp? || vop.StatesInternalOp?)

    && (
      || dop.NoDiskOp?
      || (
        && dop.RespReadSuperblockOp?
      )
      || (
        && dop.RespReadJournalOp?
      )
      || (
        && dop.RespWriteSuperblockOp?
        && !(s.Ready? && s.superblockWrite == Some(dop.id))
      )
      || (
        && dop.RespWriteJournalOp?
        && !(s.Ready? && dop.id in s.outstandingJournalWrites)
      )
    )
    && s' == s
  }

  predicate ValidJournalStep(s: Variables, js: JournalStep)
  {
    && s.Ready?
    && (js.JSReplay? ==>
      && IsPrefix(js.entries, s.replayJournal)
    )
    && (js.JSNew? ==>
      && s.replayJournal == []
    )
  }

  function DoJournalStep(s: Variables, js: JournalStep) : Variables
  requires ValidJournalStep(s, js)
  requires s.Ready?
  {
    match js {
      case JSReplay(entries) =>
        reveal_IsPrefix(); 
        s.(replayJournal := s.replayJournal[|entries|..])
      case JSNew(entries) =>
        s.(inMemoryJournal := s.inMemoryJournal + entries)
    }
  }

  predicate Init(s: Variables)
  {
    s == LoadingSuperblock(None, None, SuperblockUnfinished, SuperblockUnfinished, map[])
  }

  predicate NextStep(s: Variables, s': Variables, dop: DiskOp, vop: VOp, step: Step) {
    match step {
      case WriteBackJournalReqStep(jr: JournalRange) => WriteBackJournalReq(s, s', dop, vop, jr)
      case WriteBackJournalRespStep => WriteBackJournalResp(s, s', dop, vop)
      case WriteBackSuperblockReq_AdvanceLog_Step => WriteBackSuperblockReq_AdvanceLog(s, s', dop, vop)
      case WriteBackSuperblockReq_AdvanceLocation_Step => WriteBackSuperblockReq_AdvanceLocation(s, s', dop, vop)
      case WriteBackSuperblockRespStep => WriteBackSuperblockResp(s, s', dop, vop)
      case PageInJournalReqStep(which: int) => PageInJournalReq(s, s', dop, vop, which)
      case PageInJournalRespStep(which: int) => PageInJournalResp(s, s', dop, vop, which)
      case PageInSuperblockReqStep(which: int) => PageInSuperblockReq(s, s', dop, vop, which)
      case PageInSuperblockRespStep(which: int) => PageInSuperblockResp(s, s', dop, vop, which)
      case FinishLoadingSuperblockPhaseStep => FinishLoadingSuperblockPhase(s, s', dop, vop)
      case FinishLoadingOtherPhaseStep => FinishLoadingOtherPhase(s, s', dop, vop)
      case FreezeStep => Freeze(s, s', dop, vop)
      case ReceiveFrozenLocStep => ReceiveFrozenLoc(s, s', dop, vop)
      case AdvanceStep => Advance(s, s', dop, vop)
      case ReplayStep => Replay(s, s', dop, vop)
      case PushSyncReqStep(id: uint64) => PushSyncReq(s, s', dop, vop, id)
      case PopSyncReqStep(id: uint64) => PopSyncReq(s, s', dop, vop, id)
      case NoOpStep => NoOp(s, s', dop, vop)
    }
  }

  predicate Next(s: Variables, s': Variables, dop: DiskOp, vop: VOp) {
    exists step: Step :: NextStep(s, s', dop, vop, step)
  }

  predicate InvLoadingSuperblock(s: Variables)
  requires s.LoadingSuperblock?
  {
    && (s.superblock1.SuperblockSuccess? ==>
        && s.outstandingSuperblock1Read.None?
        && WFSuperblock(s.superblock1.value)
       )
    && (s.superblock2.SuperblockSuccess? ==>
        && s.outstandingSuperblock2Read.None?
        && WFSuperblock(s.superblock2.value)
       )
    && (s.superblock1.SuperblockCorruption? ==>
        && s.outstandingSuperblock1Read.None?
        )
    && (s.superblock2.SuperblockCorruption? ==>
        && s.outstandingSuperblock2Read.None?
        )
  }

  predicate InvLoadingOther(s: Variables)
  requires s.LoadingOther?
  {
    && WFSuperblock(s.superblock)
    && (s.whichSuperblock == 0 || s.whichSuperblock == 1)
    && (s.journalFrontRead.Some? ==>
      JournalFrontIntervalOfSuperblock(s.superblock).Some?)
    && (s.journalFront.Some? ==>
      JournalFrontIntervalOfSuperblock(s.superblock).Some?)
    && (s.journalBackRead.Some? ==>
      JournalBackIntervalOfSuperblock(s.superblock).Some?)
    && (s.journalBack.Some? ==>
      JournalBackIntervalOfSuperblock(s.superblock).Some?)
  }

  predicate InvReady(s: Variables)
  requires s.Ready?
  {
    && (s.superblockWrite.Some? <==> s.newSuperblock.Some?)
    && (s.superblockWrite.None? <==> s.commitStatus.CommitNone?)

    && (s.whichSuperblock == 0 || s.whichSuperblock == 1)

    && 0 <= s.writtenJournalLen <= NumJournalBlocks() as int
    && 0 <= s.superblock.journalLen as int <= s.writtenJournalLen

    && (s.isFrozen ==>
      && 0 <= s.frozenJournalPosition <= NumJournalBlocks() as int
      && s.superblock.journalLen as int <= s.writtenJournalLen
      && s.frozenJournalPosition <= s.writtenJournalLen
    )

    && (s.frozenLoc.Some? ==>
      && ValidIndirectionTableLocation(s.frozenLoc.value)
      && s.isFrozen
    )

    && WFSuperblock(s.superblock)
    && (s.commitStatus.CommitAdvanceLog? ==>
      && s.newSuperblock.Some?
      && s.newSuperblock.value.indirectionTableLoc == s.superblock.indirectionTableLoc
      && s.newSuperblock.value.journalStart == s.superblock.journalStart
      && s.newSuperblock.value.journalLen as int == s.writtenJournalLen
    )
    && (s.commitStatus.CommitAdvanceLocation? ==>
      && s.isFrozen
      && s.frozenLoc.Some?
      && s.newSuperblock.Some?
      && s.newSuperblock.value.journalStart as int == JournalPosAdd(s.superblock.journalStart as int, s.frozenJournalPosition)
      && s.newSuperblock.value.journalLen as int == s.writtenJournalLen - s.frozenJournalPosition
      && s.frozenJournalPosition as int + s.newSuperblock.value.journalLen as int
          <= s.writtenJournalLen
    )
    && (s.newSuperblock.Some? ==>
        && s.outstandingJournalWrites == {}

        && (
          || s.newSuperblock.value.indirectionTableLoc == s.superblock.indirectionTableLoc
          || (
            && s.frozenLoc.Some?
            && s.newSuperblock.value.indirectionTableLoc == s.frozenLoc.value
          )
        )

        && (s.commitStatus.CommitAdvanceLog?
            || s.commitStatus.CommitAdvanceLocation?)

        && WFSuperblock(s.newSuperblock.value)
        && s.newSuperblock.value.counter ==
            IncrementSuperblockCounter(s.superblock.counter)
        && s.inMemoryJournalFrozen == []
    )
    && (s.inMemoryJournalFrozen != [] ==>
      && s.frozenJournalPosition == s.writtenJournalLen
      && s.isFrozen
    )
  }

  predicate Inv(s: Variables)
  {
    && (s.LoadingSuperblock? ==> InvLoadingSuperblock(s))
    && (s.LoadingOther? ==> InvLoadingOther(s))
    && (s.Ready? ==> InvReady(s))
  }

  lemma InitImpliesInv(s: Variables)
    requires Init(s)
    ensures Inv(s)
  {
  }

  lemma WriteBackJournalReqStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp, jr: JournalRange)
    requires Inv(s)
    requires WriteBackJournalReq(s, s', dop, vop, jr)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma WriteBackJournalRespStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(s)
    requires WriteBackJournalResp(s, s', dop, vop)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma WriteBackSuperblockReq_AdvanceLog_StepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(s)
    requires WriteBackSuperblockReq_AdvanceLog(s, s', dop, vop)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma WriteBackSuperblockReq_AdvanceLocation_StepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(s)
    requires WriteBackSuperblockReq_AdvanceLocation(s, s', dop, vop)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma WriteBackSuperblockRespStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(s)
    requires WriteBackSuperblockResp(s, s', dop, vop)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      /*if s'.frozenIndirectionTable.Some? {
        if s.newSuperblock.value.indirectionTableLoc == s.superblock.indirectionTableLoc {
          assert s'.superblock.journalLen as int <= s'.frozenJournalPosition;
        } else {
          assert s'.superblock.journalLen as int <= s'.frozenJournalPosition;
        }
      }*/

      if s.commitStatus.CommitAdvanceLog? {
        assert InvReady(s');
      } else if s.commitStatus.CommitAdvanceLocation? {
        //assert s.isFrozen;
        //assert s.frozenJournalPosition <= s.writtenJournalLen;
        //assert s'.writtenJournalLen == s.writtenJournalLen - s.frozenJournalPosition;
        //assert 0 <= s'.writtenJournalLen;
        assert InvReady(s');
      }
    }
  }

  lemma PageInJournalReqStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp, which: int)
    requires Inv(s)
    requires PageInJournalReq(s, s', dop, vop, which)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma PageInJournalRespStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp, which: int)
    requires Inv(s)
    requires PageInJournalResp(s, s', dop, vop, which)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma PageInSuperblockReqStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp, which: int)
    requires Inv(s)
    requires PageInSuperblockReq(s, s', dop, vop, which)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma PageInSuperblockRespStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp, which: int)
    requires Inv(s)
    requires PageInSuperblockResp(s, s', dop, vop, which)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma FinishLoadingSuperblockPhaseStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(s)
    requires FinishLoadingSuperblockPhase(s, s', dop, vop)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma FinishLoadingOtherPhaseStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(s)
    requires FinishLoadingOtherPhase(s, s', dop, vop)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma FreezeStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(s)
    requires Freeze(s, s', dop, vop)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma ReceiveFrozenLocStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(s)
    requires ReceiveFrozenLoc(s, s', dop, vop)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma AdvanceStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(s)
    requires Advance(s, s', dop, vop)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma ReplayStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(s)
    requires Replay(s, s', dop, vop)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma PushSyncReqStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp, id: uint64)
    requires Inv(s)
    requires PushSyncReq(s, s', dop, vop, id)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma PopSyncReqStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp, id: uint64)
    requires Inv(s)
    requires PopSyncReq(s, s', dop, vop, id)
    ensures Inv(s')
  {
    if (s'.Ready?) {
      assert InvReady(s');
    }
  }

  lemma NextStepPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp, step: Step)
    requires Inv(s)
    requires NextStep(s, s', dop, vop, step)
    ensures Inv(s')
  {
    match step {
      case WriteBackJournalReqStep(jr: JournalRange) => WriteBackJournalReqStepPreservesInv(s, s', dop, vop, jr);
      case WriteBackJournalRespStep => WriteBackJournalRespStepPreservesInv(s, s', dop, vop);
      case WriteBackSuperblockReq_AdvanceLog_Step => WriteBackSuperblockReq_AdvanceLog_StepPreservesInv(s, s', dop, vop);
      case WriteBackSuperblockReq_AdvanceLocation_Step => WriteBackSuperblockReq_AdvanceLocation_StepPreservesInv(s, s', dop, vop);
      case WriteBackSuperblockRespStep => WriteBackSuperblockRespStepPreservesInv(s, s', dop, vop);
      case PageInJournalReqStep(which) => PageInJournalReqStepPreservesInv(s, s', dop, vop, which);
      case PageInJournalRespStep(which) => PageInJournalRespStepPreservesInv(s, s', dop, vop, which);
      case PageInSuperblockReqStep(which) => PageInSuperblockReqStepPreservesInv(s, s', dop, vop, which);
      case PageInSuperblockRespStep(which) => PageInSuperblockRespStepPreservesInv(s, s', dop, vop, which);
      case FinishLoadingSuperblockPhaseStep => FinishLoadingSuperblockPhaseStepPreservesInv(s, s', dop, vop);
      case FinishLoadingOtherPhaseStep => FinishLoadingOtherPhaseStepPreservesInv(s, s', dop, vop);
      case FreezeStep => FreezeStepPreservesInv(s, s', dop, vop);
      case ReceiveFrozenLocStep => ReceiveFrozenLocStepPreservesInv(s, s', dop, vop);
      case AdvanceStep => AdvanceStepPreservesInv(s, s', dop, vop);
      case ReplayStep => ReplayStepPreservesInv(s, s', dop, vop);
      case PushSyncReqStep(id) => PushSyncReqStepPreservesInv(s, s', dop, vop, id);
      case PopSyncReqStep(id) => PopSyncReqStepPreservesInv(s, s', dop, vop, id);
      case NoOpStep => { }
    }
  }

  lemma NextPreservesInv(s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(s)
    requires Next(s, s', dop, vop)
    ensures Inv(s')
  {
    var step :| NextStep(s, s', dop, vop, step);
    NextStepPreservesInv(s, s', dop, vop, step);
  }
}
