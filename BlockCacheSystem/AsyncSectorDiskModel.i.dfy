include "../MapSpec/MapSpec.s.dfy"
include "../lib/Base/Maps.s.dfy"
include "../PivotBetree/Bounds.i.dfy"
include "DiskLayout.i.dfy"
include "SectorType.i.dfy"
include "JournalInterval.i.dfy"

//
// An AsyncSectorDiskModel allows concurrent outstanding I/Os to a disk where each "sector"
// is some higher-level Node datatype. A later refinement step shows how to marshall and align
// these Nodes to the byte-ranges of the (trusted) AsyncDiskModel.
//
// TODO disallow concurrent spatially-overlapping writes/reads

module AsyncSectorDiskModelTypes {
  datatype AsyncSectorDiskModelConstants<M,D> = AsyncSectorDiskModelConstants(machine: M, disk: D)
  datatype AsyncSectorDiskModelVariables<M,D> = AsyncSectorDiskModelVariables(machine: M, disk: D)
}

// A disk, processing stuff in its queue, doing its thing.
module AsyncSectorDisk {
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

  datatype ReqReadJournal = ReqReadJournal(interval: JournalInterval)
  datatype ReqReadIndirectionTable = ReqReadIndirectionTable(loc: Location)
  datatype ReqReadNode = ReqReadNode(loc: Location)

  datatype ReqWriteSuperblock = ReqWriteSuperblock(superblock: Superblock)
  datatype ReqWriteJournal = ReqWriteJournal(start: int, journal: JournalRange)
  datatype ReqWriteIndirectionTable = ReqWriteIndirectionTable(loc: Location, indirectionTable: IndirectionTable)
  datatype ReqWriteNode = ReqWriteNode(loc: Location, node: Node)

  datatype ReqWriteSuperblockId = ReqWriteSuperblockId(id: ReqId, req: ReqWriteSuperblock)

  datatype DiskOp =
    | ReqReadSuperblockOp(id: ReqId, which: int)
    | ReqReadJournalOp(id: ReqId, reqReadJournal: ReqReadJournal)
    | ReqReadIndirectionTableOp(id: ReqId, reqReadIndirectionTable: ReqReadIndirectionTable)
    | ReqReadNodeOp(id: ReqId, reqReadNode: ReqReadNode)

    | ReqWriteSuperblockOp(id: ReqId, which: int, reqWriteSuperblock: ReqWriteSuperblock)
    | ReqWriteJournalOp(id: ReqId, reqWriteJournal: ReqWriteJournal)
    | ReqWriteIndirectionTableOp(id: ReqId, reqWriteIndirectionTable: ReqWriteIndirectionTable)
    | ReqWriteNodeOp(id: ReqId, reqWriteNode: ReqWriteNode)

    | RespReadSuperblockOp(id: ReqId, which: int, superblock: Option<Superblock>)
    | RespReadJournalOp(id: ReqId, journal: Option<JournalRange>)
    | RespReadIndirectionTableOp(id: ReqId, indirectionTable: Option<IndirectionTable>)
    | RespReadNodeOp(id: ReqId, node: Option<Node>)

    | RespWriteSuperblockOp(id: ReqId, which: int)
    | RespWriteJournalOp(id: ReqId)
    | RespWriteIndirectionTableOp(id: ReqId)
    | RespWriteNodeOp(id: ReqId)

    | NoDiskOp

  datatype Constants = Constants()
  datatype Variables = Variables(
    reqReadSuperblock1: Option<ReqId>,
    reqReadSuperblock2: Option<ReqId>,
    reqReadJournals: map<ReqId, ReqReadJournal>,
    reqReadIndirectionTables: map<ReqId, ReqReadIndirectionTable>,
    reqReadNodes: map<ReqId, ReqReadNode>,

    reqWriteSuperblock1: Option<ReqId>,
    reqWriteSuperblock2: Option<ReqId>,
    reqWriteJournals: map<ReqId, JournalInterval>,
    reqWriteIndirectionTables: map<ReqId, Location>,
    reqWriteNodes: map<ReqId, Location>,

    // The disk:
    superblock1: Option<Superblock>,
    superblock2: Option<Superblock>,
    journal: seq<Option<JournalBlock>>,
    indirectionTables: imap<Location, IndirectionTable>,
    nodes: imap<Location, Node>
  )

  predicate Init(k: Constants, s: Variables)
  {
    && s.reqReadSuperblock1 == None
    && s.reqReadSuperblock2 == None
    && s.reqReadJournals == map[]
    && s.reqReadIndirectionTables == map[]
    && s.reqReadNodes == map[]

    && s.reqWriteSuperblock1 == None
    && s.reqWriteSuperblock2 == None
    && s.reqWriteJournals == map[]
    && s.reqWriteIndirectionTables == map[]
    && s.reqWriteNodes == map[]
  }

  ///////// RecvRead

  predicate RecvReadSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadSuperblockOp?
    && Some(dop.id) != s.reqReadSuperblock1
    && Some(dop.id) != s.reqReadSuperblock2
    && (dop.which == 0 || dop.which == 1)
    && (dop.which == 0 ==>
      s' == s.(reqReadSuperblock1 := Some(dop.id)))
    && (dop.which == 1 ==>
      s' == s.(reqReadSuperblock2 := Some(dop.id)))
  }

  predicate RecvReadJournal(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadJournalOp?
    && dop.id !in s.reqReadJournals
    && ContiguousJournalInterval(dop.reqReadJournal.interval)
    && s' == s.(reqReadJournals := s.reqReadJournals[dop.id := dop.reqReadJournal])
  }

  predicate RecvReadIndirectionTable(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadIndirectionTableOp?
    && dop.id !in s.reqReadIndirectionTables
    && s' == s.(reqReadIndirectionTables := s.reqReadIndirectionTables[dop.id := dop.reqReadIndirectionTable])
  }

  predicate RecvReadNode(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadNodeOp?
    && dop.id !in s.reqReadNodes
    && s' == s.(reqReadNodes := s.reqReadNodes[dop.id := dop.reqReadNode])
  }

  ///////// RecvWrite

  predicate RecvWriteSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteSuperblockOp?
    && (s.reqWriteSuperblock1.Some? ==> s.reqWriteSuperblock1.value != dop.id)
    && (s.reqWriteSuperblock2.Some? ==> s.reqWriteSuperblock2.value != dop.id)
    && (dop.which == 0 || dop.which == 1)
    && (dop.which == 0 ==>
      s' == s.(reqWriteSuperblock1 := Some(dop.id))
             .(superblock1 := Some(dop.reqWriteSuperblock.superblock))
    )
    && (dop.which == 1 ==>
      s' == s.(reqWriteSuperblock2 := Some(dop.id))
             .(superblock2 := Some(dop.reqWriteSuperblock.superblock))
    )
  }

  predicate ValidJournalInterval(interval: JournalInterval)
  {
    && 0 <= interval.start < NumJournalBlocks() as int
    && 0 <= interval.len <= NumJournalBlocks() as int
  }

  predicate RecvWriteJournal(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteJournalOp?
    && dop.id !in s.reqWriteJournals
    && var interval := JournalInterval(dop.reqWriteJournal.start, |dop.reqWriteJournal.journal|);
    && JournalUpdate(s.journal, s'.journal, interval, dop.reqWriteJournal.journal)
    && s' == s.(reqWriteJournals := s.reqWriteJournals[dop.id := interval])
              .(journal := s'.journal)
  }

  predicate DiskMapUpdate<T>(disk: imap<Location, T>, disk': imap<Location, T>, updateLoc: Location, t: T)
  {
    && updateLoc in disk'
    && disk'[updateLoc] == t
    && (forall loc | loc in disk && !overlap(loc, updateLoc) :: loc in disk' && disk'[loc] == disk[loc])
    && (forall loc | loc in disk' && !overlap(loc, updateLoc) :: loc in disk)
  }

  predicate RecvWriteIndirectionTable(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteIndirectionTableOp?
    && dop.id !in s.reqWriteIndirectionTables
    && DiskMapUpdate(s.indirectionTables, s'.indirectionTables, dop.reqWriteIndirectionTable.loc, dop.reqWriteIndirectionTable.indirectionTable)
    && s' == s.(reqWriteIndirectionTables := s.reqWriteIndirectionTables[dop.id := dop.reqWriteIndirectionTable.loc])
              .(indirectionTables := s'.indirectionTables)
  }

  predicate RecvWriteNode(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteNodeOp?
    && dop.id !in s.reqWriteNodes
    && DiskMapUpdate(s.nodes, s'.nodes, dop.reqWriteNode.loc, dop.reqWriteNode.node)
    && s' == s.(reqWriteNodes := s.reqWriteNodes[dop.id := dop.reqWriteNode.loc])
              .(nodes := s'.nodes)
  }

  ///////// AckRead

  predicate AckReadSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadSuperblockOp?
    && (dop.which == 0 || dop.which == 1)
    && (dop.which == 0 ==>
      && s.reqReadSuperblock1.Some?
      && dop.id == s.reqReadSuperblock1.value
      && (dop.superblock.Some? ==> dop.superblock == s.superblock1)
      && s' == s.(reqReadSuperblock1 := None)
    )
    && (dop.which == 1 ==>
      && s.reqReadSuperblock2.Some?
      && dop.id == s.reqReadSuperblock2.value
      && (dop.superblock.Some? ==> dop.superblock == s.superblock2)
      && s' == s.(reqReadSuperblock2 := None)
    )
  }

  function {:opaque} journalRead(a: seq<Option<JournalBlock>>) : Option<seq<JournalBlock>>
  {
    if a == [] then Some([]) else (
      var p := journalRead(DropLast(a));
      if p.Some? && Last(a).Some? then
        Some(p.value + [Last(a).value])
      else
        None
    )
  }

  predicate AckReadJournal(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadJournalOp?
    && dop.id in s.reqReadJournals
    && var ind := s.reqReadJournals[dop.id].interval;
    && 0 <= ind.start <= ind.start + ind.len <= |s.journal|
    && (dop.journal.Some? ==>
      dop.journal == journalRead(s.journal[ind.start .. ind.start + ind.len]))
    && s' == s.(reqReadJournals := MapRemove1(s.reqReadJournals, dop.id))
  }

  predicate AckReadIndirectionTable(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadIndirectionTableOp?
    && dop.id in s.reqReadIndirectionTables
    && var req := s.reqReadIndirectionTables[dop.id];
    && (dop.indirectionTable.Some? ==>
      dop.indirectionTable == ImapLookupOption(s.indirectionTables, req.loc))
    && s' == s.(reqReadIndirectionTables := MapRemove1(s.reqReadIndirectionTables, dop.id))
  }

  predicate AckReadNode(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadNodeOp?
    && dop.id in s.reqReadNodes
    && var req := s.reqReadNodes[dop.id];
    && (dop.node.Some? ==>
      dop.node == ImapLookupOption(s.nodes, req.loc))
    && s' == s.(reqReadNodes := MapRemove1(s.reqReadNodes, dop.id))
  }

  ///////// AckWrite

  predicate AckWriteSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteSuperblockOp?
    && (dop.which == 0 || dop.which == 1)
    && (dop.which == 0 ==>
      && s.reqWriteSuperblock1.Some?
      && dop.id == s.reqWriteSuperblock1.value
      && s' == s.(reqWriteSuperblock1 := None)
    )
    && (dop.which == 1 ==>
      && s.reqWriteSuperblock2.Some?
      && dop.id == s.reqWriteSuperblock2.value
      && s' == s.(reqWriteSuperblock2 := None)
    )
  }

  predicate AckWriteJournal(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteJournalOp?
    && dop.id in s.reqWriteJournals
    && s' == s.(reqWriteJournals := MapRemove1(s.reqWriteJournals, dop.id))
  }

  predicate AckWriteIndirectionTable(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteIndirectionTableOp?
    && dop.id in s.reqWriteIndirectionTables
    && s' == s.(reqWriteIndirectionTables := MapRemove1(s.reqWriteIndirectionTables, dop.id))
  }

  predicate AckWriteNode(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteNodeOp?
    && dop.id in s.reqWriteNodes
    && s' == s.(reqWriteNodes := MapRemove1(s.reqWriteNodes, dop.id))
  }

  //// Stutter

  predicate Stutter(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.NoDiskOp?
    && s' == s
  }

  predicate Next(k: Constants, s: Variables, s': Variables, dop: DiskOp) {
    && (dop.ReqReadSuperblockOp? ==> RecvReadSuperblock(k, s, s', dop))
    && (dop.ReqReadJournalOp? ==> RecvReadJournal(k, s, s', dop))
    && (dop.ReqReadIndirectionTableOp? ==> RecvReadIndirectionTable(k, s, s', dop))
    && (dop.ReqReadNodeOp? ==> RecvReadNode(k, s, s', dop))

    && (dop.ReqWriteSuperblockOp? ==> RecvWriteSuperblock(k, s, s', dop))
    && (dop.ReqWriteJournalOp? ==> RecvWriteJournal(k, s, s', dop))
    && (dop.ReqWriteIndirectionTableOp? ==> RecvWriteIndirectionTable(k, s, s', dop))
    && (dop.ReqWriteNodeOp? ==> RecvWriteNode(k, s, s', dop))

    && (dop.RespReadSuperblockOp? ==> AckReadSuperblock(k, s, s', dop))
    && (dop.RespReadJournalOp? ==> AckReadJournal(k, s, s', dop))
    && (dop.RespReadIndirectionTableOp? ==> AckReadIndirectionTable(k, s, s', dop))
    && (dop.RespReadNodeOp? ==> AckReadNode(k, s, s', dop))

    && (dop.RespWriteSuperblockOp? ==> AckWriteSuperblock(k, s, s', dop))
    && (dop.RespWriteJournalOp? ==> AckWriteJournal(k, s, s', dop))
    && (dop.RespWriteIndirectionTableOp? ==> AckWriteIndirectionTable(k, s, s', dop))
    && (dop.RespWriteNodeOp? ==> AckWriteNode(k, s, s', dop))

    && (dop.NoDiskOp? ==> Stutter(k, s, s', dop))
  }

  predicate havocSuperblockWrite(superblock: Option<Superblock>, superblock': Option<Superblock>, reqWriteSuperblock: Option<ReqId>)
  {
    reqWriteSuperblock.None? ==> superblock == superblock'
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

  predicate UntouchedLoc(loc: Location, reqs: map<ReqId, Location>)
  {
    forall id | id in reqs :: !overlap(loc, reqs[id])
  }

  predicate havocMap<T>(
    m: imap<Location, T>,
    m': imap<Location, T>,
    reqs: map<ReqId, Location>)
  {
    forall loc | loc in m ::
        UntouchedLoc(loc, reqs) ==>
            loc in m' && m'[loc] == m[loc]
  }

  predicate Crash(k: Constants, s: Variables, s': Variables)
  {
    && s.reqReadSuperblock1 == None
    && s.reqReadSuperblock2 == None
    && s.reqReadJournals == map[]
    && s.reqReadIndirectionTables == map[]
    && s.reqReadNodes == map[]

    && s.reqWriteSuperblock1 == None
    && s.reqWriteSuperblock2 == None
    && s.reqWriteJournals == map[]
    && s.reqWriteIndirectionTables == map[]
    && s.reqWriteNodes == map[]

    && havocSuperblockWrite(s.superblock1, s'.superblock1, s.reqWriteSuperblock1)
    && havocSuperblockWrite(s.superblock2, s'.superblock2, s.reqWriteSuperblock2)
    && havocJournal(s.journal, s'.journal, s.reqWriteJournals)
    && havocMap(s.indirectionTables, s'.indirectionTables, s.reqWriteIndirectionTables)
    && havocMap(s.nodes, s'.nodes, s.reqWriteNodes)
  }
}

abstract module AsyncSectorDiskMachine {
  import D = AsyncSectorDisk
  import UI

  type Variables
  type Constants
  type Location(==)
  type Sector
  type UIOp = UI.Op

  predicate Init(k: Constants, s: Variables)
  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: D.DiskOp)
}

// A disk attached to a program ("Machine"), modeling the nondeterministic crashes that reset the
// program. Designed to look like the AsyncDiskModel, which we want to show refines to this.
// TODO(jonh): Rename this to a "System"?
abstract module AsyncSectorDiskModel {
  import D = AsyncSectorDisk
  import M : AsyncSectorDiskMachine
  import AsyncSectorDiskModelTypes
  import opened SectorType

  type Constants = AsyncSectorDiskModelTypes.AsyncSectorDiskModelConstants<M.Constants, D.Constants>
  type Variables = AsyncSectorDiskModelTypes.AsyncSectorDiskModelVariables<M.Variables, D.Variables>
  type UIOp = M.UIOp

  datatype Step =
    | MachineStep(dop: D.DiskOp)
    | CrashStep
  
  predicate Machine(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: D.DiskOp)
  {
    && M.Next(k.machine, s.machine, s'.machine, uiop, dop)
    && D.Next(k.disk, s.disk, s'.disk, dop)
  }

  predicate Crash(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  {
    && uiop.CrashOp?
    && M.Init(k.machine, s'.machine)
    && D.Crash(k.disk, s.disk, s'.disk)
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: Step)
  {
    match step {
      case MachineStep(dop) => Machine(k, s, s', uiop, dop)
      case CrashStep => Crash(k, s, s', uiop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp) {
    exists step :: NextStep(k, s, s', uiop, step)
  }

  predicate Init(k: Constants, s: Variables)
  predicate Inv(k: Constants, s: Variables)

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp)
    requires Inv(k, s)
    requires Next(k, s, s', uiop)
    ensures Inv(k, s')
}
