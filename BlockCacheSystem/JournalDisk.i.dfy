include "../lib/Base/Maps.i.dfy"
include "DiskLayout.i.dfy"
include "SectorType.i.dfy"
include "JournalInterval.i.dfy"

module JournalDisk {
  import opened NativeTypes
  import opened Maps
  import opened Options
  import opened DiskLayout
  import opened SectorType
  import opened JournalRanges
  import opened JournalIntervals
  import opened PivotBetreeGraph
  import opened Sequences

  type ReqId = uint64

  datatype ReqWriteSuperblock = ReqWriteSuperblock(superblock: Superblock)
  datatype ReqWriteJournal = ReqWriteJournal(ghost start: int, journal: JournalRange)

  datatype ReqWriteSuperblockId = ReqWriteSuperblockId(id: ReqId, req: ReqWriteSuperblock)

  datatype DiskOp =
    | ReqReadSuperblockOp(id: ReqId, ghost which: int)
    | ReqReadJournalOp(id: ReqId, interval: JournalInterval)

    | ReqWriteSuperblockOp(id: ReqId, ghost which: int, reqWriteSuperblock: ReqWriteSuperblock)
    | ReqWriteJournalOp(id1: ReqId, id2: Option<ReqId>, reqWriteJournal: ReqWriteJournal)

    | RespReadSuperblockOp(id: ReqId, ghost which: int, superblock: Option<Superblock>)
    | RespReadJournalOp(id: ReqId, journal: Option<JournalRange>)

    | RespWriteSuperblockOp(id: ReqId, ghost which: int)
    | RespWriteJournalOp(id: ReqId)

    | NoDiskOp

  datatype Variables = Variables(
    ghost reqReadSuperblock1: set<ReqId>,
    ghost reqReadSuperblock2: set<ReqId>,
    ghost reqReadJournals: map<ReqId, JournalInterval>,

    ghost reqWriteSuperblock1: Option<ReqWriteSuperblockId>,
    ghost reqWriteSuperblock2: Option<ReqWriteSuperblockId>,
    ghost reqWriteJournals: map<ReqId, JournalInterval>,

    // The disk:
    ghost superblock1: Option<Superblock>,
    ghost superblock2: Option<Superblock>,
    ghost journal: seq<Option<JournalBlock>>
  )

  predicate Init(s: Variables)
  {
    && s.reqReadSuperblock1 == {}
    && s.reqReadSuperblock2 == {}
    && s.reqReadJournals == map[]

    && s.reqWriteSuperblock1 == None
    && s.reqWriteSuperblock2 == None
    && s.reqWriteJournals == map[]

    && |s.journal| == NumJournalBlocks() as int
  }

  ///////// RecvRead

  predicate RecvReadSuperblock(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadSuperblockOp?
    && dop.id !in s.reqReadSuperblock1
    && dop.id !in s.reqReadSuperblock2
    && (dop.which == 0 || dop.which == 1)
    && (dop.which == 0 ==>
      s' == s.(reqReadSuperblock1 := s.reqReadSuperblock1 + {dop.id}))
    && (dop.which == 1 ==>
      s' == s.(reqReadSuperblock2 := s.reqReadSuperblock2 + {dop.id}))
  }

  predicate RecvReadJournal(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadJournalOp?
    && dop.id !in s.reqReadJournals
    && ContiguousJournalInterval(dop.interval)
    && s' == s.(reqReadJournals := s.reqReadJournals[dop.id := dop.interval])
  }

  ///////// RecvWrite

  predicate RecvWriteSuperblock(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteSuperblockOp?
    && (s.reqWriteSuperblock1.Some? ==> s.reqWriteSuperblock1.value.id != dop.id)
    && (s.reqWriteSuperblock2.Some? ==> s.reqWriteSuperblock2.value.id != dop.id)
    && (dop.which == 0 || dop.which == 1)
    && (dop.which == 0 ==>
      s' == s.(reqWriteSuperblock1 := Some(ReqWriteSuperblockId(dop.id, dop.reqWriteSuperblock)))
    )
    && (dop.which == 1 ==>
      s' == s.(reqWriteSuperblock2 := Some(ReqWriteSuperblockId(dop.id, dop.reqWriteSuperblock)))
    )
  }

  predicate ValidJournalInterval(interval: JournalInterval)
  {
    && 0 <= interval.start < NumJournalBlocks() as int
    && 0 <= interval.len <= NumJournalBlocks() as int
  }

  predicate RecvWriteJournal(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteJournalOp?
    && dop.id1 !in s.reqWriteJournals.Keys
    && (dop.id2.Some? ==> dop.id2.value !in s.reqWriteJournals.Keys)
    && var interval := JournalInterval(dop.reqWriteJournal.start, |dop.reqWriteJournal.journal|);
    && JournalUpdate(s.journal, s'.journal, interval, dop.reqWriteJournal.journal)
    && (interval.start + interval.len <= NumJournalBlocks() as int ==>
      && dop.id2.None?
      && s' == s.(reqWriteJournals := s.reqWriteJournals[dop.id1 := interval])
                .(journal := s'.journal)
    )
    && (interval.start + interval.len > NumJournalBlocks() as int ==>
      && dop.id2.Some?
      && dop.id2.value != dop.id1
      && var interval1 := JournalInterval(interval.start, NumJournalBlocks() as int - interval.start);
      && var interval2 := JournalInterval(0, interval.len - (NumJournalBlocks() as int - interval.start));
      && s' == s.(reqWriteJournals := s.reqWriteJournals[dop.id1 := interval1][dop.id2.value := interval2])
                .(journal := s'.journal)
    )
  }

  ///////// AckRead

  predicate AckReadSuperblock(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadSuperblockOp?
    && (dop.which == 0 || dop.which == 1)
    && (dop.which == 0 ==>
      && dop.id in s.reqReadSuperblock1
      && (dop.superblock.Some? ==> dop.superblock == s.superblock1)
      && s' == s.(reqReadSuperblock1 := s.reqReadSuperblock1 - {dop.id})
    )
    && (dop.which == 1 ==>
      && dop.id in s.reqReadSuperblock2
      && (dop.superblock.Some? ==> dop.superblock == s.superblock2)
      && s' == s.(reqReadSuperblock2 := s.reqReadSuperblock2 - {dop.id})
    )
  }

  predicate AckReadJournal(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadJournalOp?
    && dop.id in s.reqReadJournals
    && var ind := s.reqReadJournals[dop.id];
    && 0 <= ind.start <= ind.start + ind.len <= NumJournalBlocks() as int
    && ind.start < NumJournalBlocks() as int
    && (dop.journal.Some? ==>
      && Disk_HasJournalRange(s.journal, ind)
      && dop.journal.value == Disk_JournalRange(s.journal, ind)
    )
    && s' == s.(reqReadJournals := MapRemove1(s.reqReadJournals, dop.id))
  }

  ///////// AckWrite

  predicate AckWriteSuperblock(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteSuperblockOp?
    && (dop.which == 0 || dop.which == 1)
    && (dop.which == 0 ==>
      && s.reqWriteSuperblock1.Some?
      && dop.id == s.reqWriteSuperblock1.value.id
      && Some(s.reqWriteSuperblock1.value.req.superblock) == s.superblock1
      && s' == s.(reqWriteSuperblock1 := None)
    )
    && (dop.which == 1 ==>
      && s.reqWriteSuperblock2.Some?
      && dop.id == s.reqWriteSuperblock2.value.id
      && Some(s.reqWriteSuperblock2.value.req.superblock) == s.superblock2
      && s' == s.(reqWriteSuperblock2 := None)
    )
  }

  predicate AckWriteJournal(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteJournalOp?
    && dop.id in s.reqWriteJournals
    && s' == s.(reqWriteJournals := MapRemove1(s.reqWriteJournals, dop.id))
  }

  //// Stutter

  predicate Stutter(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.NoDiskOp?
    && s' == s
  }

  predicate Next(s: Variables, s': Variables, dop: DiskOp) {
    && (dop.ReqReadSuperblockOp? ==> RecvReadSuperblock(s, s', dop))
    && (dop.ReqReadJournalOp? ==> RecvReadJournal(s, s', dop))

    && (dop.ReqWriteSuperblockOp? ==> RecvWriteSuperblock(s, s', dop))
    && (dop.ReqWriteJournalOp? ==> RecvWriteJournal(s, s', dop))

    && (dop.RespReadSuperblockOp? ==> AckReadSuperblock(s, s', dop))
    && (dop.RespReadJournalOp? ==> AckReadJournal(s, s', dop))

    && (dop.RespWriteSuperblockOp? ==> AckWriteSuperblock(s, s', dop))
    && (dop.RespWriteJournalOp? ==> AckWriteJournal(s, s', dop))

    && (dop.NoDiskOp? ==> Stutter(s, s', dop))
  }

  datatype InternalStep =
  | ProcessWriteSuperblockStep(ghost which: int)

  predicate ProcessWriteSuperblock(s: Variables, s': Variables, which: int)
  {
    && (which == 0 || which == 1)
    && (which == 0 ==>
      && s.reqWriteSuperblock1.Some?
      && s' == s.(superblock1 := Some(s.reqWriteSuperblock1.value.req.superblock))
    )
    && (which == 1 ==>
      && s.reqWriteSuperblock2.Some?
      && s' == s.(superblock2 := Some(s.reqWriteSuperblock2.value.req.superblock))
    )
  }

  predicate NextInternalStep(s: Variables, s': Variables, step: InternalStep)
  {
    match step {
      case ProcessWriteSuperblockStep(which) => ProcessWriteSuperblock(s, s', which)
    }
  }

  predicate NextInternal(s: Variables, s': Variables)
  {
    exists step :: NextInternalStep(s, s', step)
  }

  predicate JournalUntouched(
    i: int, 
    reqWriteJournals: map<ReqId, JournalInterval>)
  {
    forall id | id in reqWriteJournals ::
        !InCyclicRange(i, reqWriteJournals[id])
  }

  predicate havocJournal(
    journal: seq<Option<JournalBlock>>,
    journal': seq<Option<JournalBlock>>,
    reqWriteJournals: map<ReqId, JournalInterval>)
  {
    && |journal'| == |journal|
    && forall i | 0 <= i < |journal| ::
        JournalUntouched(i, reqWriteJournals) ==>
            journal[i] == journal'[i]
  }

  predicate Crash(s: Variables, s': Variables)
  {
    && s'.reqReadSuperblock1 == {}
    && s'.reqReadSuperblock2 == {}
    && s'.reqReadJournals == map[]

    && s'.reqWriteSuperblock1 == None
    && s'.reqWriteSuperblock2 == None
    && s'.reqWriteJournals == map[]

    && s'.superblock1 == s.superblock1
    && s'.superblock2 == s.superblock2
    && havocJournal(s.journal, s'.journal, s.reqWriteJournals)
  }
}
