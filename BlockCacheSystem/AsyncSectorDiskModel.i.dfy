include "../MapSpec/MapSpec.s.dfy"
include "../lib/Base/Maps.s.dfy"
include "../PivotBetree/Bounds.i.dfy"
include "DiskLayout.i.dfy"
include "SectorType.i.dfy"

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
  import opened PivotBetreeGraph
  import opened Sequences

  type ReqId = uint64

  datatype ReqReadJournal = ReqReadJournal(start: int, len: int)
  datatype ReqReadIndirectionTable = ReqReadIndirectionTable(loc: Location)
  datatype ReqReadNode = ReqReadNode(loc: Location)

  datatype ReqWriteSuperblock = ReqWriteSuperblock(superblock: Superblock)
  datatype ReqWriteJournal = ReqWriteJournal(start: int, journal: JournalRange)
  datatype ReqWriteIndirectionTable = ReqWriteIndirectionTable(loc: Location, indirectionTable: IndirectionTable)
  datatype ReqWriteNode = ReqWriteNode(loc: Location, node: Node)

  datatype ReqWriteSuperblockId = ReqWriteSuperblockId(id: ReqId, req: ReqWriteSuperblock)

  datatype RespReadSuperblockId = RespReadSuperblockId(id: ReqId, superblock: Option<Superblock>)

  datatype DiskOp =
    | ReqReadSuperblockOp(id: ReqId, which: int)
    | ReqReadJournalOp(id: ReqId, reqReadJournal: ReqReadJournal)
    | ReqReadIndirectionTableOp(id: ReqId, reqReadIndirectionTable: ReqReadIndirectionTable)
    | ReqReadNodeOp(id: ReqId, reqReadNode: ReqReadNode)

    | ReqWriteSuperblockOp(id: ReqId, which: int, reqWriteSuperblock: ReqWriteSuperblock)
    | ReqWriteJournalOp(id: ReqId, reqWriteJournal: ReqWriteJournal)
    | ReqWriteJournalOp2(
      id1: ReqId, reqWriteJournal1: ReqWriteJournal,
      id2: ReqId, reqWriteJournal2: ReqWriteJournal)
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

    reqWriteSuperblock1: Option<ReqWriteSuperblockId>,
    reqWriteSuperblock2: Option<ReqWriteSuperblockId>,
    reqWriteJournals: map<ReqId, ReqWriteJournal>,
    reqWriteIndirectionTables: map<ReqId, ReqWriteIndirectionTable>,
    reqWriteNodes: map<ReqId, ReqWriteNode>,

    respReadSuperblock1: Option<RespReadSuperblockId>,
    respReadSuperblock2: Option<RespReadSuperblockId>,
    respReadJournals: map<ReqId, Option<JournalRange>>,
    respReadIndirectionTables: map<ReqId, Option<IndirectionTable>>,
    respReadNodes: map<ReqId, Option<Node>>,

    respWriteSuperblock1: Option<ReqId>,
    respWriteSuperblock2: Option<ReqId>,
    respWriteJournals: set<ReqId>,
    respWriteIndirectionTables: set<ReqId>,
    respWriteNodes: set<ReqId>,

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

    && s.respReadSuperblock1 == None
    && s.respReadSuperblock2 == None
    && s.respReadJournals == map[]
    && s.respReadIndirectionTables == map[]
    && s.respReadNodes == map[]

    && s.respWriteSuperblock1 == None
    && s.respWriteSuperblock2 == None
    && s.respWriteJournals == {}
    && s.respWriteIndirectionTables == {}
    && s.respWriteNodes == {}
  }

  ///////// RecvRead

  predicate RecvReadSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadSuperblockOp?
    && Some(dop.id) != s.reqReadSuperblock1
    && Some(dop.id) != s.reqReadSuperblock2
    && (s.respReadSuperblock1.Some? ==> s.respReadSuperblock1.value.id != dop.id)
    && (s.respReadSuperblock2.Some? ==> s.respReadSuperblock2.value.id != dop.id)
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
    && dop.id !in s.respReadJournals
    && 0 <= dop.reqReadJournal.start < NumJournalBlocks() as int
    && 0 <= dop.reqReadJournal.start + dop.reqReadJournal.len <= NumJournalBlocks() as int
    && s' == s.(reqReadJournals := s.reqReadJournals[dop.id := dop.reqReadJournal])
  }

  predicate RecvReadIndirectionTable(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadIndirectionTableOp?
    && dop.id !in s.reqReadIndirectionTables
    && dop.id !in s.respReadIndirectionTables
    && s' == s.(reqReadIndirectionTables := s.reqReadIndirectionTables[dop.id := dop.reqReadIndirectionTable])
  }

  predicate RecvReadNode(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadNodeOp?
    && dop.id !in s.reqReadNodes
    && dop.id !in s.respReadNodes
    && s' == s.(reqReadNodes := s.reqReadNodes[dop.id := dop.reqReadNode])
  }

  ///////// RecvWrite

  predicate RecvWriteSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteSuperblockOp?
    && Some(dop.id) != s.respWriteSuperblock1
    && Some(dop.id) != s.respWriteSuperblock2
    && (s.reqWriteSuperblock1.Some? ==> s.reqWriteSuperblock1.value.id != dop.id)
    && (s.reqWriteSuperblock2.Some? ==> s.reqWriteSuperblock2.value.id != dop.id)
    && (dop.which == 0 || dop.which == 1)
    && (dop.which == 0 ==>
      s' == s.(reqWriteSuperblock1 := Some(ReqWriteSuperblockId(dop.id, dop.reqWriteSuperblock))))
    && (dop.which == 1 ==>
      s' == s.(reqWriteSuperblock2 := Some(ReqWriteSuperblockId(dop.id, dop.reqWriteSuperblock))))
  }

  predicate ValidReqWriteJournal(reqWriteJournal: ReqWriteJournal)
  {
    && 0 <= reqWriteJournal.start < NumJournalBlocks() as int
    && 0 <= reqWriteJournal.start + |reqWriteJournal.journal| <= NumJournalBlocks() as int
  }

  predicate RecvWriteJournal(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteJournalOp?
    && dop.id !in s.reqWriteJournals
    && dop.id !in s.respWriteJournals
    && ValidReqWriteJournal(dop.reqWriteJournal)
    && s' == s.(reqWriteJournals := s.reqWriteJournals[dop.id := dop.reqWriteJournal])
  }

  predicate RecvWriteJournal2(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteJournalOp2?
    && dop.id1 !in s.reqWriteJournals
    && dop.id1 !in s.respWriteJournals
    && dop.id2 !in s.reqWriteJournals
    && dop.id2 !in s.respWriteJournals
    && ValidReqWriteJournal(dop.reqWriteJournal1)
    && ValidReqWriteJournal(dop.reqWriteJournal2)
    && s' == s.(reqWriteJournals :=
        s.reqWriteJournals[dop.id1 := dop.reqWriteJournal1]
                          [dop.id2 := dop.reqWriteJournal2]
      )
  }

  predicate RecvWriteIndirectionTable(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteIndirectionTableOp?
    && dop.id !in s.reqWriteIndirectionTables
    && dop.id !in s.respWriteIndirectionTables
    && s' == s.(reqWriteIndirectionTables := s.reqWriteIndirectionTables[dop.id := dop.reqWriteIndirectionTable])
  }

  predicate RecvWriteNode(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteNodeOp?
    && dop.id !in s.reqWriteNodes
    && dop.id !in s.respWriteNodes
    && s' == s.(reqWriteNodes := s.reqWriteNodes[dop.id := dop.reqWriteNode])
  }

  ///////// AckRead

  predicate AckReadSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadSuperblockOp?
    && (dop.which == 0 || dop.which == 1)
    && (dop.which == 0 ==>
      && s.respReadSuperblock1.Some?
      && dop.id == s.respReadSuperblock1.value.id
      && dop.superblock == s.respReadSuperblock1.value.superblock
      && s' == s.(respReadSuperblock1 := None)
    )
    && (dop.which == 1 ==>
      && s.respReadSuperblock2.Some?
      && dop.id == s.respReadSuperblock2.value.id
      && dop.superblock == s.respReadSuperblock2.value.superblock
      && s' == s.(respReadSuperblock2 := None)
    )
  }

  predicate AckReadJournal(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadJournalOp?
    && dop.id in s.respReadJournals
    && s.respReadJournals[dop.id] == dop.journal
    && s' == s.(respReadJournals := MapRemove1(s.respReadJournals, dop.id))
  }

  predicate AckReadIndirectionTable(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadIndirectionTableOp?
    && dop.id in s.respReadIndirectionTables
    && s.respReadIndirectionTables[dop.id] == dop.indirectionTable
    && s' == s.(respReadIndirectionTables := MapRemove1(s.respReadIndirectionTables, dop.id))
  }

  predicate AckReadNode(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadNodeOp?
    && dop.id in s.respReadNodes
    && s.respReadNodes[dop.id] == dop.node
    && s' == s.(respReadNodes := MapRemove1(s.respReadNodes, dop.id))
  }

  ///////// AckWrite

  predicate AckWriteSuperblock(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteSuperblockOp?
    && (dop.which == 0 || dop.which == 1)
    && (dop.which == 0 ==>
      && s.respWriteSuperblock1.Some?
      && dop.id == s.respWriteSuperblock1.value
      && s' == s.(respWriteSuperblock1 := None)
    )
    && (dop.which == 1 ==>
      && s.respWriteSuperblock2.Some?
      && dop.id == s.respWriteSuperblock2.value
      && s' == s.(respWriteSuperblock2 := None)
    )
  }

  predicate AckWriteJournal(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteJournalOp?
    && dop.id in s.respWriteJournals
    && s' == s.(respWriteJournals := s.respWriteJournals - {dop.id})
  }

  predicate AckWriteIndirectionTable(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteIndirectionTableOp?
    && dop.id in s.respWriteIndirectionTables
    && s' == s.(respWriteIndirectionTables := s.respWriteIndirectionTables - {dop.id})
  }

  predicate AckWriteNode(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteNodeOp?
    && dop.id in s.respWriteNodes
    && s' == s.(respWriteNodes := s.respWriteNodes - {dop.id})
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
    && (dop.ReqWriteJournalOp2? ==> RecvWriteJournal2(k, s, s', dop))
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

  datatype InternalStep =
    | ProcessReadSuperblockStep(which: int, id: ReqId)
    | ProcessReadJournalStep(id: ReqId)
    | ProcessReadIndirectionTableStep(id: ReqId)
    | ProcessReadNodeStep(id: ReqId)

    | ProcessReadFailureSuperblockStep(which: int, id: ReqId)
    | ProcessReadFailureJournalStep(id: ReqId)
    | ProcessReadFailureIndirectionTableStep(id: ReqId)
    | ProcessReadFailureNodeStep(id: ReqId)

    | ProcessWriteSuperblockStep(which: int, id: ReqId)
    | ProcessWriteJournalStep(id: ReqId)
    | ProcessWriteIndirectionTableStep(id: ReqId)
    | ProcessWriteNodeStep(id: ReqId)

  ///////// ProcessRead

  predicate ProcessReadSuperblock(k: Constants, s: Variables, s': Variables, which: int, id: ReqId)
  {
    && (which == 0 || which == 1)
    && (which == 0 ==>
      && s.reqReadSuperblock1 == Some(id)
      && s' == s.(reqReadSuperblock1 := None)
                .(respReadSuperblock1 := Some(RespReadSuperblockId(id, s.superblock1)))
    )
    && (which == 1 ==>
      && s.reqReadSuperblock2 == Some(id)
      && s' == s.(reqReadSuperblock2 := None)
                .(respReadSuperblock2 := Some(RespReadSuperblockId(id, s.superblock2)))
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

  predicate ProcessReadJournal(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqReadJournals
    && var req := s.reqReadJournals[id];
    && 0 <= req.start <= req.start + req.len <= |s.journal|
    && var jr := journalRead(s.journal[req.start .. req.start + req.len]);
    && s' == s.(reqReadJournals := MapRemove1(s.reqReadJournals, id))
              .(respReadJournals := s.respReadJournals[id := jr])
  }

  predicate ProcessReadIndirectionTable(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqReadIndirectionTables
    && var req := s.reqReadIndirectionTables[id];
    && s' == s.(reqReadIndirectionTables := MapRemove1(s.reqReadIndirectionTables, id))
              .(respReadIndirectionTables := s.respReadIndirectionTables[id := ImapLookupOption(s.indirectionTables, req.loc)])
  }

  predicate ProcessReadNode(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqReadNodes
    && var req := s.reqReadNodes[id];
    && s' == s.(reqReadNodes := MapRemove1(s.reqReadNodes, id))
              .(respReadNodes := s.respReadNodes[id := ImapLookupOption(s.nodes, req.loc)])
  }

  ////////// ProcessReadFailure

  predicate ProcessReadFailureSuperblock(k: Constants, s: Variables, s': Variables, which: int, id: ReqId)
  {
    && (which == 0 || which == 1)
    && (which == 0 ==>
      && s.reqReadSuperblock1 == Some(id)
      && s' == s.(reqReadSuperblock1 := None)
                .(respReadSuperblock1 := Some(RespReadSuperblockId(id, None)))
    )
    && (which == 1 ==>
      && s.reqReadSuperblock2 == Some(id)
      && s' == s.(reqReadSuperblock2 := None)
                .(respReadSuperblock2 := Some(RespReadSuperblockId(id, None)))
    )
  }

  predicate ProcessReadFailureJournal(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqReadJournals
    && s' == s.(reqReadJournals := MapRemove1(s.reqReadJournals, id))
              .(respReadJournals := s.respReadJournals[id := None])
  }

  predicate ProcessReadFailureIndirectionTable(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqReadIndirectionTables
    && s' == s.(reqReadIndirectionTables := MapRemove1(s.reqReadIndirectionTables, id))
              .(respReadIndirectionTables := s.respReadIndirectionTables[id := None])
  }

  predicate ProcessReadFailureNode(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqReadNodes
    && s' == s.(reqReadNodes := MapRemove1(s.reqReadNodes, id))
              .(respReadNodes := s.respReadNodes[id := None])
  }

  //////// ProcessWrite

  predicate ProcessWriteSuperblock(k: Constants, s: Variables, s': Variables, which: int, id: ReqId)
  {
    && (which == 0 || which == 1)
    && (which == 0 ==>
      && s.reqWriteSuperblock1.Some?
      && s.reqWriteSuperblock1.value.id == id
      && s' == s.(superblock1 := Some(s.reqWriteSuperblock1.value.req.superblock))
                .(reqWriteSuperblock1 := None)
                .(respWriteSuperblock1 := Some(id))
    )
    && (which == 1 ==>
      && s.reqWriteSuperblock2.Some?
      && s.reqWriteSuperblock2.value.id == id
      && s' == s.(superblock2 := Some(s.reqWriteSuperblock2.value.req.superblock))
                .(reqWriteSuperblock2 := None)
                .(respWriteSuperblock2 := Some(id))
    )
  }

  predicate ProcessWriteJournal(k: Constants, s: Variables, s': Variables, which: int, id: ReqId)
  {
    && (which == 0 || which == 1)
    && (which == 0 ==>
      && s.reqWriteSuperblock1.Some?
      && s.reqWriteSuperblock1.value.id == id
      && s' == s.(superblock1 := Some(s.reqWriteSuperblock1.value.req.superblock))
                .(reqWriteSuperblock1 := None)
                .(respWriteSuperblock1 := Some(id))
    )
    && (which == 1 ==>
      && s.reqWriteSuperblock2.Some?
      && s.reqWriteSuperblock2.value.id == id
      && s' == s.(superblock2 := Some(s.reqWriteSuperblock2.value.req.superblock))
                .(reqWriteSuperblock2 := None)
                .(respWriteSuperblock2 := Some(id))
    )
  }

  predicate ProcessWriteIndirectionTable(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqWriteIndirectionTables
    && var req := s.reqWriteIndirectionTables[id];
    && s' == s.(reqWriteIndirectionTables := MapRemove1(s.reqWriteIndirectionTables, id))
              .(respWriteIndirectionTables := s.respWriteIndirectionTables + {id})
              .(indirectionTables := s'.indirectionTables)

    && req.loc in s'.indirectionTables
    && s'.indirectionTables[req.loc] == req.indirectionTable
    && (forall loc | loc in s.indirectionTables && !overlap(loc, req.loc) :: loc in s'.indirectionTables && s'.indirectionTables[loc] == s.indirectionTables[loc])
    && (forall loc | loc in s'.indirectionTables && !overlap(loc, req.loc) :: loc in s.indirectionTables)
  }

  predicate ProcessWriteNode(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqWriteNodes
    && var req := s.reqWriteNodes[id];
    && s' == s.(reqWriteNodes := MapRemove1(s.reqWriteNodes, id))
              .(respWriteNodes := s.respWriteNodes + {id})
              .(nodes := s'.nodes)

    // It would be easier to say s'.nodes == s.nodes[req.loc := req.sector]
    // but to make the refinement from AsyncDiskModel easier, we only require that
    // the map preserves every location not intersecting the given region. We don't
    // have to say anything about potential intervals which could intersect this one.
    && req.loc in s'.nodes
    && s'.nodes[req.loc] == req.node
    && (forall loc | loc in s.nodes && !overlap(loc, req.loc) :: loc in s'.nodes && s'.nodes[loc] == s.nodes[loc])
    && (forall loc | loc in s'.nodes && !overlap(loc, req.loc) :: loc in s.nodes)
  }

  predicate NextInternalStep(k: Constants, s: Variables, s': Variables, step: InternalStep)
  {
    match step {
      case ProcessReadSuperblockStep(which, id) => ProcessReadSuperblock(k, s, s', which, id)
      case ProcessReadJournalStep(id) => ProcessReadJournal(k, s, s', id)
      case ProcessReadIndirectionTableStep(id) => ProcessReadIndirectionTable(k, s, s', id)
      case ProcessReadNodeStep(id) => ProcessReadNode(k, s, s', id)
      case ProcessReadFailureSuperblockStep(which, id) => ProcessReadFailureSuperblock(k, s, s', which, id)
      case ProcessReadFailureJournalStep(id) => ProcessReadFailureJournal(k, s, s', id)
      case ProcessReadFailureIndirectionTableStep(id) => ProcessReadFailureIndirectionTable(k, s, s', id)
      case ProcessReadFailureNodeStep(id) => ProcessReadFailureNode(k, s, s', id)
      case ProcessWriteSuperblockStep(which, id) => ProcessWriteSuperblock(k, s, s', which, id)
      case ProcessWriteJournalStep(id) => ProcessWriteJournal(k, s, s', id)
      case ProcessWriteIndirectionTableStep(id) => ProcessWriteIndirectionTable(k, s, s', id)
      case ProcessWriteNodeStep(id) => ProcessWriteNode(k, s, s', id)
    }
  }

  predicate NextInternal(k: Constants, s: Variables, s': Variables)
  {
    exists step :: NextInternalStep(k, s, s', step)
  }

  predicate Crash(k: Constants, s: Variables, s': Variables)
  {
    s' == Variables(map[], map[], map[], map[], s.blocks)
  }
}

/*abstract module AsyncSectorDiskMachine {
  import D = AsyncSectorDisk
  import UI

  type Variables
  type Constants
  type Location(==)
  type Sector
  type UIOp = UI.Op

  type DiskOp = D.DiskOp
  type ReqRead = D.ReqRead
  type ReqWrite = D.ReqWrite
  type RespRead = D.RespRead
  type RespWrite = D.RespWrite

  predicate Init(k: Constants, s: Variables)
  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
}

// A disk attached to a program ("Machine"), modeling the nondeterministic crashes that reset the
// program. Designed to look like the AsyncDiskModel, which we want to show refines to this.
// TODO(jonh): Rename this to a "System"?
abstract module AsyncSectorDiskModel {
  import D = AsyncSectorDisk
  import M : AsyncSectorDiskMachine
  import AsyncSectorDiskModelTypes
  import opened SectorType

  type DiskOp = M.DiskOp
  type Constants = AsyncSectorDiskModelTypes.AsyncSectorDiskModelConstants<M.Constants, D.Constants>
  type Variables = AsyncSectorDiskModelTypes.AsyncSectorDiskModelVariables<M.Variables, D.Variables>
  type UIOp = M.UIOp

  datatype Step =
    | MachineStep(dop: DiskOp)
    | DiskInternalStep(step: D.InternalStep)
    | CrashStep
  
  predicate Machine(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  {
    && M.Next(k.machine, s.machine, s'.machine, uiop, dop)
    && D.Next(k.disk, s.disk, s'.disk, dop)
  }

  predicate DiskInternal(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: D.InternalStep)
  {
    && uiop.NoOp?
    && s.machine == s'.machine
    && D.NextInternalStep(k.disk, s.disk, s'.disk, step)
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
      case DiskInternalStep(step) => DiskInternal(k, s, s', uiop, step)
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
}*/
