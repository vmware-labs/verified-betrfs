include "../BlockCacheSystem/BlockCache.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"

//
// Attach a BlockCache to a Disk
//

module BlockSystem {
  import M = BlockCache
  import D = BlockDisk

  import opened Maps
  import opened Sequences
  import opened Options
  import opened AsyncSectorDiskModelTypes
  import opened NativeTypes
  import opened DiskLayout
  import opened SectorType
  import opened ViewOp

  type DiskOp = M.DiskOp

  type Constants = AsyncSectorDiskModelConstants<M.Constants, D.Constants>
  type Variables = AsyncSectorDiskModelVariables<M.Variables, D.Variables>

  type Reference = M.G.Reference
  type Node = M.G.Node
  type Op = M.Op

  predicate WFIndirectionTableRefWrtDisk(
      indirectionTable: IndirectionTable,
      blocks: imap<Location, Node>,
      ref: Reference)
  requires ref in indirectionTable.locs
  {
    && indirectionTable.locs[ref] in blocks
  }

  predicate WFIndirectionTableWrtDisk(indirectionTable: IndirectionTable, blocks: imap<Location, Node>)
  {
    forall ref | ref in indirectionTable.locs :: 
      indirectionTable.locs[ref] in blocks
  }

  predicate disjointWritesFromIndirectionTable(
      outstandingBlockWrites: map<D.ReqId, M.OutstandingWrite>,
      indirectionTable: IndirectionTable)
  {
    forall req, ref |
        && req in outstandingBlockWrites
        && ref in indirectionTable.locs ::
          outstandingBlockWrites[req].loc != indirectionTable.locs[ref]
  }

  function RefMapOfDisk(
      indirectionTable: IndirectionTable,
      blocks: imap<Location, Node>) : map<Reference, Node>
  requires WFIndirectionTableWrtDisk(indirectionTable, blocks)
  {
    map ref | ref in indirectionTable.locs :: blocks[indirectionTable.locs[ref]]
  }

  function Graph(refs: set<Reference>, refmap: map<Reference, Node>) : imap<Reference, Node>
  requires refs <= refmap.Keys
  {
    imap ref | ref in refs :: refmap[ref]
  }

  predicate WFDiskGraph(indirectionTable: IndirectionTable, blocks: imap<Location, Node>)
  {
    && M.WFCompleteIndirectionTable(indirectionTable)
    && WFIndirectionTableWrtDisk(indirectionTable, blocks)
  }

  function DiskGraph(indirectionTable: IndirectionTable, blocks: imap<Location, Node>) : imap<Reference, Node>
  requires WFDiskGraph(indirectionTable, blocks)
  {
    Graph(indirectionTable.graph.Keys, RefMapOfDisk(indirectionTable, blocks))
  }

  predicate HasDiskCacheLookup(indirectionTable: IndirectionTable, disk: D.Variables, cache: map<Reference, Node>, ref: Reference)
  {
    && WFIndirectionTableWrtDisk(indirectionTable, disk.nodes)
    && (ref !in cache ==>
      && ref in indirectionTable.locs
      && indirectionTable.locs[ref] in disk.nodes
    )
  }

  function DiskCacheLookup(indirectionTable: IndirectionTable, disk: D.Variables, cache: map<Reference, Node>, ref: Reference) : Node
  requires HasDiskCacheLookup(indirectionTable, disk, cache, ref)
  {
    if ref in indirectionTable.locs then
      disk.nodes[indirectionTable.locs[ref]]
    else
      cache[ref]
  }

  predicate WFDiskCacheGraph(indirectionTable: IndirectionTable, disk: D.Variables, cache: map<Reference, Node>)
  {
    && WFIndirectionTableWrtDisk(indirectionTable, disk.nodes)
    && (forall ref | ref in indirectionTable.graph ::
      HasDiskCacheLookup(indirectionTable, disk, cache, ref))
  }

  function DiskCacheGraph(indirectionTable: IndirectionTable, disk: D.Variables, cache: map<Reference, Node>) : imap<Reference, Node>
  requires WFDiskCacheGraph(indirectionTable, disk, cache)
  {
    imap ref | ref in indirectionTable.graph :: DiskCacheLookup(indirectionTable, disk, cache, ref)
  }

  predicate WFDiskGraphOfLoc(
      k: Constants,
      s: Variables,
      loc: Location)
  {
    && ValidIndirectionTableLocation(loc)
    && loc in s.disk.indirectionTables
    && M.WFCompleteIndirectionTable(
        s.disk.indirectionTables[loc])
    && WFIndirectionTableWrtDisk(
      s.disk.indirectionTables[loc],
      s.disk.nodes)
  }

  predicate NoDanglingPointers(graph: imap<Reference, Node>)
  {
    forall r1, r2 {:trigger r2 in M.G.Successors(graph[r1])}
      | r1 in graph && r2 in M.G.Successors(graph[r1])
      :: r2 in graph
  }

  predicate SuccessorsAgree(succGraph: map<Reference, seq<Reference>>, graph: imap<Reference, Node>)
  {
    && (forall key | key in succGraph :: key in graph)
    && (forall key | key in graph :: key in succGraph)
    && forall ref | ref in succGraph :: (iset r | r in succGraph[ref]) == M.G.Successors(graph[ref])
  }

  protected predicate WFSuccs(k: Constants, s: Variables, loc: Location)
  {
    && WFDiskGraphOfLoc(k, s, loc)
    && SuccessorsAgree(
      s.disk.indirectionTables[loc].graph,
      DiskGraphOfLoc(k, s, loc))
    && NoDanglingPointers(DiskGraphOfLoc(k, s, loc))
  }

  function DiskGraphOfLoc(
      k: Constants,
      s: Variables,
      loc: Location) : imap<Reference, Node>
  requires WFDiskGraphOfLoc(k, s, loc)
  {
    DiskGraph(s.disk.indirectionTables[loc], s.disk.nodes)
  }

  protected function DiskGraphMap(
      k: Constants,
      s: Variables) : imap<Location, imap<Reference, Node>>
  {
    imap loc | WFSuccs(k, s, loc)
        :: DiskGraphOfLoc(k, s, loc)
  }

  protected function PersistentLoc(k: Constants, s: Variables) : Option<Location>
  {
    if s.machine.Ready? then 
      Some(s.machine.persistentIndirectionTableLoc)
    else if s.machine.LoadingIndirectionTable? then
      Some(s.machine.indirectionTableLoc)
    else
      None
  }

  protected function FrozenLoc(k: Constants, s: Variables) : Option<Location>
  {
    if s.machine.Ready? && s.machine.frozenIndirectionTableLoc.Some?
        && s.machine.outstandingIndirectionTableWrite.None? then (
      s.machine.frozenIndirectionTableLoc
    ) else (
      None
    )
  }

  predicate DiskChangesPreservesPersistentAndFrozen(k: Constants, s: Variables, s': Variables)
  {
    && (PersistentLoc(k, s).None? ==>
      && forall loc | loc in DiskGraphMap(k, s) ::
          && loc in DiskGraphMap(k, s')
          && DiskGraphMap(k, s')[loc] == DiskGraphMap(k, s)[loc]
    )
    && (PersistentLoc(k, s).Some? ==>
      && PersistentLoc(k, s).value in DiskGraphMap(k, s)
      && PersistentLoc(k, s).value in DiskGraphMap(k, s')
      && DiskGraphMap(k, s')[PersistentLoc(k, s).value]
          == DiskGraphMap(k, s)[PersistentLoc(k, s).value]
    )
    && (FrozenLoc(k, s).Some? ==>
      && FrozenLoc(k, s).value in DiskGraphMap(k, s)
      && FrozenLoc(k, s).value in DiskGraphMap(k, s')
      && DiskGraphMap(k, s')[FrozenLoc(k, s).value]
          == DiskGraphMap(k, s)[FrozenLoc(k, s).value]
    )
  }

  protected predicate WFFrozenGraph(k: Constants, s: Variables)
  {
    && s.machine.Ready?
    && s.machine.frozenIndirectionTable.Some?
    && WFDiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
  }

  protected function FrozenGraph(k: Constants, s: Variables) : imap<Reference, Node>
  requires WFFrozenGraph(k, s)
  {
    DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
  }

  protected predicate UseFrozenGraph(k: Constants, s: Variables)
  {
    s.machine.Ready? && s.machine.frozenIndirectionTable.Some?
  }

  protected function FrozenGraphOpt(k: Constants, s: Variables) : Option<imap<Reference, Node>>
  {
    if WFFrozenGraph(k, s) then
      Some(FrozenGraph(k, s))
    else
      None
  }

  protected predicate WFLoadingGraph(k: Constants, s: Variables)
  {
    && s.machine.LoadingIndirectionTable?
    && WFDiskGraphOfLoc(k, s, s.machine.indirectionTableLoc)
  }

  protected function LoadingGraph(k: Constants, s: Variables) : imap<Reference, Node>
  requires WFLoadingGraph(k, s)
  {
    DiskGraphOfLoc(k, s, s.machine.indirectionTableLoc)
  }

  protected predicate WFEphemeralGraph(k: Constants, s: Variables)
  {
    && s.machine.Ready?
    && WFDiskCacheGraph(s.machine.ephemeralIndirectionTable, s.disk, s.machine.cache)
  }

  protected function EphemeralGraph(k: Constants, s: Variables) : imap<Reference, Node>
  requires WFEphemeralGraph(k, s)
  {
    DiskCacheGraph(s.machine.ephemeralIndirectionTable, s.disk, s.machine.cache)
  }

  protected function EphemeralGraphOpt(k: Constants, s: Variables) : Option<imap<Reference, Node>>
  {
    if WFEphemeralGraph(k, s) then
      Some(EphemeralGraph(k, s))
    else if WFLoadingGraph(k, s) then
      Some(LoadingGraph(k, s))
    else
      None
  }

  ///// Init

  predicate Init(k: Constants, s: Variables, loc: Location)
  {
    && M.Init(k.machine, s.machine)
    && D.Init(k.disk, s.disk)
    && WFDiskGraphOfLoc(k, s, loc)
    && SuccessorsAgree(s.disk.indirectionTables[loc].graph, DiskGraphOfLoc(k, s, loc))
    && NoDanglingPointers(DiskGraphOfLoc(k, s, loc))
    && DiskGraphOfLoc(k, s, loc).Keys == iset{M.G.Root()}
    && M.G.Successors(DiskGraphOfLoc(k, s, loc)[M.G.Root()]) == iset{}
  }

  ////// Next

  datatype Step =
    | MachineStep(dop: DiskOp, machineStep: M.Step)
    | CrashStep
  
  predicate Machine(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, machineStep: M.Step)
  {
    && M.NextStep(k.machine, s.machine, s'.machine, dop, vop, machineStep)
    && D.Next(k.disk, s.disk, s'.disk, dop)

    // The composite state machine of BlockSystem and JournalSystem
    // will need to provide this condition.
    && (vop.SendPersistentLocOp? ==>
          vop.loc in DiskGraphMap(k, s))
  }

  predicate Crash(k: Constants, s: Variables, s': Variables, vop: VOp)
  {
    && vop.CrashOp?
    && M.Init(k.machine, s'.machine)
    && D.Crash(k.disk, s.disk, s'.disk)
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, vop: VOp, step: Step)
  {
    match step {
      case MachineStep(dop, machineStep) => Machine(k, s, s', dop, vop, machineStep)
      case CrashStep => Crash(k, s, s', vop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, vop: VOp) {
    exists step :: NextStep(k, s, s', vop, step)
  }

  ////// Invariants

  predicate CleanCacheEntriesAreCorrect(k: Constants, s: Variables)
  requires s.machine.Ready?
  requires M.WFIndirectionTable(s.machine.ephemeralIndirectionTable)
  requires WFIndirectionTableWrtDisk(s.machine.ephemeralIndirectionTable, s.disk.nodes)
  {
    forall ref | ref in s.machine.cache ::
      ref in s.machine.ephemeralIndirectionTable.locs ==>
        s.machine.cache[ref] == s.disk.nodes[s.machine.ephemeralIndirectionTable.locs[ref]]
  }

  // Any outstanding read we have recorded should be consistent with
  // whatever is in the queue.

  predicate CorrectInflightBlockRead(k: Constants, s: Variables, id: D.ReqId, ref: Reference)
  requires s.machine.Ready?
  {
    && ref !in s.machine.cache
    && ref in s.machine.ephemeralIndirectionTable.locs
    && var loc := s.machine.ephemeralIndirectionTable.locs[ref];
    && loc in s.disk.nodes
    && var sector := s.disk.nodes[loc];
    && (id in s.disk.reqReadNodes ==> s.disk.reqReadNodes[id] == loc)
  }

  predicate CorrectInflightBlockReads(k: Constants, s: Variables)
  requires s.machine.Ready?
  {
    forall id | id in s.machine.outstandingBlockReads ::
      CorrectInflightBlockRead(k, s, id, s.machine.outstandingBlockReads[id].ref)
  }

  predicate CorrectInflightIndirectionTableReads(k: Constants, s: Variables)
  requires s.machine.LoadingIndirectionTable?
  {
    s.machine.indirectionTableRead.Some? ==> (
      && var reqId := s.machine.indirectionTableRead.value;
      && (reqId in s.disk.reqReadIndirectionTables ==>
        && s.disk.reqReadIndirectionTables[reqId] == s.machine.indirectionTableLoc
      )
    )
  }

  // Any outstanding write we have recorded should be consistent with
  // whatever is in the queue.

  predicate CorrectInflightNodeWrite(k: Constants, s: Variables, id: D.ReqId, ref: Reference, loc: Location)
  requires s.machine.Ready?
  {
    && ValidNodeLocation(loc)
    && (forall r | r in s.machine.ephemeralIndirectionTable.locs ::
        s.machine.ephemeralIndirectionTable.locs[r].addr == loc.addr ==> r == ref)


    && (s.machine.frozenIndirectionTable.Some? ==>
        && (forall r | r in s.machine.frozenIndirectionTable.value.locs ::
          s.machine.frozenIndirectionTable.value.locs[r].addr == loc.addr ==> r == ref)
        && (s.machine.frozenIndirectionTableLoc.Some? ==>
          && (forall r | r in s.machine.frozenIndirectionTable.value.locs ::
            s.machine.frozenIndirectionTable.value.locs[r].addr != loc.addr)
        )
      )

    && (forall r | r in s.machine.persistentIndirectionTable.locs ::
        s.machine.persistentIndirectionTable.locs[r].addr != loc.addr)

    && (id in s.disk.reqWriteNodes ==>
      && s.disk.reqWriteNodes[id] == loc
    )
  }

  predicate CorrectInflightNodeWrites(k: Constants, s: Variables)
  requires s.machine.Ready?
  {
    forall id | id in s.machine.outstandingBlockWrites ::
      CorrectInflightNodeWrite(k, s, id, s.machine.outstandingBlockWrites[id].ref, s.machine.outstandingBlockWrites[id].loc)
  }

  predicate CorrectInflightIndirectionTableWrites(k: Constants, s: Variables)
  requires s.machine.Ready?
  {
    s.machine.outstandingIndirectionTableWrite.Some? ==> (
      && s.machine.frozenIndirectionTable.Some?
      && var reqId := s.machine.outstandingIndirectionTableWrite.value;
      && s.machine.frozenIndirectionTableLoc.Some?
      && (reqId in s.disk.reqWriteIndirectionTables ==>
          s.disk.reqWriteIndirectionTables[reqId] ==
            s.machine.frozenIndirectionTableLoc.value
      )
    )
  }

  // If there's a write in progress, then the in-memory state must know about it.

  predicate RecordedWriteRequestIndirectionTable(k: Constants, s: Variables, id: D.ReqId)
  {
    && s.machine.Ready?
    && s.machine.outstandingIndirectionTableWrite == Some(id)
  }

  predicate RecordedWriteRequestNode(k: Constants, s: Variables, id: D.ReqId)
  {
    && s.machine.Ready?
    && id in s.machine.outstandingBlockWrites
  }

  predicate RecordedReadRequestIndirectionTable(k: Constants, s: Variables, id: D.ReqId)
  {
    && s.machine.LoadingIndirectionTable?
    && Some(id) == s.machine.indirectionTableRead
  }

  predicate RecordedReadRequestNode(k: Constants, s: Variables, id: D.ReqId)
  {
    && s.machine.Ready?
    && id in s.machine.outstandingBlockReads
  }

  predicate RecordedWriteRequestsIndirectionTable(k: Constants, s: Variables)
  {
    forall id | id in s.disk.reqWriteIndirectionTables :: RecordedWriteRequestIndirectionTable(k, s, id)
  }

  predicate RecordedWriteRequestsNode(k: Constants, s: Variables)
  {
    forall id | id in s.disk.reqWriteNodes :: RecordedWriteRequestNode(k, s, id)
  }

  predicate RecordedReadRequestsNode(k: Constants, s: Variables)
  {
    forall id | id in s.disk.reqReadNodes :: RecordedReadRequestNode(k, s, id)
  }

  predicate RecordedReadRequestsIndirectionTable(k: Constants, s: Variables)
  {
    forall id | id in s.disk.reqReadIndirectionTables :: RecordedReadRequestIndirectionTable(k, s, id)
  }

  predicate WriteRequestsDontOverlap(reqWrites: map<D.ReqId, Location>)
  {
    forall id1, id2 | id1 in reqWrites && id2 in reqWrites && overlap(reqWrites[id1], reqWrites[id2]) :: id1 == id2
  }

  predicate WriteRequestsAreDistinct(reqWrites: map<D.ReqId, Location>)
  {
    forall id1, id2 | id1 in reqWrites && id2 in reqWrites && reqWrites[id1] == reqWrites[id2] :: id1 == id2
  }

  predicate ReadWritesDontOverlap(
      reqReads: map<D.ReqId, Location>,
      reqWrites: map<D.ReqId, Location>)
  {
    forall id1, id2 | id1 in reqReads && id2 in reqWrites ::
        !overlap(reqReads[id1], reqWrites[id2])
  }

  predicate ReadWritesAreDistinct(
      reqReads: map<D.ReqId, Location>,
      reqWrites: map<D.ReqId, Location>)
  {
    forall id1, id2 | id1 in reqReads && id2 in reqWrites ::
        reqReads[id1] != reqWrites[id2]
  }

  protected predicate Inv(k: Constants, s: Variables)
  ensures Inv(k, s) ==>
    && (s.machine.Ready? ==> EphemeralGraphOpt(k, s).Some?)
    && M.Inv(k.machine, s.machine)
  {
    && M.Inv(k.machine, s.machine)
    && (s.machine.Ready? ==>
      && WFSuccs(k, s, s.machine.persistentIndirectionTableLoc)
      && (s.machine.frozenIndirectionTable.Some? ==>
        && WFIndirectionTableWrtDisk(s.machine.frozenIndirectionTable.value, s.disk.nodes)
        && SuccessorsAgree(s.machine.frozenIndirectionTable.value.graph, FrozenGraph(k, s))
      )
      && (s.machine.frozenIndirectionTableLoc.Some? ==>
        && s.machine.frozenIndirectionTable.Some?
        && M.WFCompleteIndirectionTable(s.machine.frozenIndirectionTable.value)
        && s.machine.frozenIndirectionTableLoc.value in s.disk.indirectionTables
        && s.machine.frozenIndirectionTable == Some(s.disk.indirectionTables[s.machine.frozenIndirectionTableLoc.value])
      )
      && s.machine.persistentIndirectionTableLoc in s.disk.indirectionTables
      && s.disk.indirectionTables[s.machine.persistentIndirectionTableLoc]
        == s.machine.persistentIndirectionTable
      && WFIndirectionTableWrtDisk(s.machine.ephemeralIndirectionTable, s.disk.nodes)
      && SuccessorsAgree(s.machine.ephemeralIndirectionTable.graph, EphemeralGraph(k, s))
      && NoDanglingPointers(EphemeralGraph(k, s))
      && CleanCacheEntriesAreCorrect(k, s)
      && CorrectInflightBlockReads(k, s)
      && CorrectInflightNodeWrites(k, s)
      && CorrectInflightIndirectionTableWrites(k, s)
    )
    && (s.machine.LoadingIndirectionTable? ==>
      && CorrectInflightIndirectionTableReads(k, s)
      && WFLoadingGraph(k, s)
      && WFSuccs(k, s, s.machine.indirectionTableLoc)
    )
    && WriteRequestsDontOverlap(s.disk.reqWriteNodes)
    && WriteRequestsAreDistinct(s.disk.reqWriteNodes)
    && ReadWritesDontOverlap(s.disk.reqReadNodes, s.disk.reqWriteNodes)
    && ReadWritesAreDistinct(s.disk.reqReadNodes, s.disk.reqWriteNodes)
    && WriteRequestsDontOverlap(s.disk.reqWriteIndirectionTables)
    && WriteRequestsAreDistinct(s.disk.reqWriteIndirectionTables)
    && ReadWritesDontOverlap(s.disk.reqReadIndirectionTables, s.disk.reqWriteIndirectionTables)
    && ReadWritesAreDistinct(s.disk.reqReadIndirectionTables, s.disk.reqWriteIndirectionTables)
    && RecordedWriteRequestsNode(k, s)
    && RecordedReadRequestsNode(k, s)
    && RecordedWriteRequestsIndirectionTable(k, s)
    && RecordedReadRequestsIndirectionTable(k, s)
  }

  ////// Proofs

  ////////////////////////////////////////////////////
  ////////////////////// Init
  //////////////////////

  lemma InitGraphs(k: Constants, s: Variables, loc: Location)
    requires Init(k, s, loc)
    ensures loc in DiskGraphMap(k, s)
    ensures PersistentLoc(k, s) == None
    ensures FrozenLoc(k, s) == None
    ensures EphemeralGraphOpt(k, s) == None
    ensures FrozenGraphOpt(k, s) == None
  {
  }
  
  lemma InitGraphsValue(k: Constants, s: Variables, loc: Location)
    requires Init(k, s, loc)
    ensures loc in DiskGraphMap(k, s)
    ensures PersistentLoc(k, s) == None
    ensures FrozenLoc(k, s) == None
    ensures EphemeralGraphOpt(k, s) == None
    ensures FrozenGraphOpt(k, s) == None
    ensures loc in s.disk.indirectionTables
    ensures M.G.Root() in s.disk.indirectionTables[loc].locs
    ensures s.disk.indirectionTables[loc].locs[M.G.Root()]
              in s.disk.nodes
    ensures DiskGraphMap(k, s)[loc]
        == imap[M.G.Root() :=
            s.disk.nodes[
              s.disk.indirectionTables[loc].locs[M.G.Root()]
            ]
           ]
  {
  }

  lemma InitImpliesInv(k: Constants, s: Variables, loc: Location)
    requires Init(k, s, loc)
    ensures Inv(k, s)
  {
    InitGraphs(k, s, loc);
  }

  ////////////////////////////////////////////////////
  ////////////////////// WriteBackNodeReq
  //////////////////////

  lemma WriteBackNodeReqStepUniqueLBAs(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
    requires Inv(k, s)
    requires M.WriteBackNodeReq(k.machine, s.machine, s'.machine, dop, vop, ref)
    requires D.RecvWriteNode(k.disk, s.disk, s'.disk, dop);
    ensures WriteRequestsDontOverlap(s'.disk.reqWriteNodes)
    ensures WriteRequestsAreDistinct(s'.disk.reqWriteNodes)
  {
    forall id1 | id1 in s'.disk.reqWriteNodes
    ensures s'.disk.reqWriteNodes[id1] == s'.disk.reqWriteNodes[dop.id]
        ==> id1 == dop.id
    ensures overlap(s'.disk.reqWriteNodes[id1], s'.disk.reqWriteNodes[dop.id])
        ==> id1 == dop.id
    {
      if s'.disk.reqWriteNodes[id1] == s'.disk.reqWriteNodes[dop.id] {
        assert s'.disk.reqWriteNodes[id1].addr == s'.disk.reqWriteNodes[dop.id].addr;
      }
      if overlap(s'.disk.reqWriteNodes[id1], s'.disk.reqWriteNodes[dop.id]) {
        overlappingLocsSameType(
            s'.disk.reqWriteNodes[id1],
            s'.disk.reqWriteNodes[dop.id]);
        overlappingNodesSameAddr(
            s'.disk.reqWriteNodes[id1],
            s'.disk.reqWriteNodes[dop.id]);
      }
    }
  }

  lemma WriteBackNodeReqStepPreservesDiskGraph(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference, indirectionTable: IndirectionTable)
    requires Inv(k, s)
    requires M.WriteBackNodeReq(k.machine, s.machine, s'.machine, dop, vop, ref)
    requires D.RecvWriteNode(k.disk, s.disk, s'.disk, dop);

    requires M.WFIndirectionTable(indirectionTable)
    requires WFIndirectionTableWrtDisk(indirectionTable, s.disk.nodes)
    requires dop.reqWriteNode.loc !in indirectionTable.locs.Values

    requires forall r | r in indirectionTable.locs ::
        indirectionTable.locs[r].addr != dop.reqWriteNode.loc.addr

    requires WFDiskGraph(indirectionTable, s.disk.nodes)

    ensures WFDiskGraph(indirectionTable, s'.disk.nodes)
    ensures DiskGraph(indirectionTable, s.disk.nodes)
         == DiskGraph(indirectionTable, s'.disk.nodes)
  {
    forall ref | ref in indirectionTable.locs
    ensures indirectionTable.locs[ref] in s'.disk.nodes
    ensures s.disk.nodes[indirectionTable.locs[ref]]
         == s'.disk.nodes[indirectionTable.locs[ref]]
    {
      if overlap(indirectionTable.locs[ref], dop.reqWriteNode.loc) {
        overlappingNodesSameAddr(indirectionTable.locs[ref], dop.reqWriteNode.loc);
        assert false;
      }
    }
  }

  lemma WriteBackNodeReqStepPreservesDiskCacheGraph(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference, indirectionTable: IndirectionTable, indirectionTable': IndirectionTable)
    requires Inv(k, s)
    requires M.WriteBackNodeReq(k.machine, s.machine, s'.machine, dop, vop, ref)
    requires D.RecvWriteNode(k.disk, s.disk, s'.disk, dop);

    requires M.WFIndirectionTable(indirectionTable)
    requires WFIndirectionTableWrtDisk(indirectionTable, s.disk.nodes)
    requires indirectionTable' == M.assignRefToLocation(indirectionTable, ref, dop.reqWriteNode.loc)
    requires M.IndirectionTableCacheConsistent(indirectionTable, s.machine.cache)
    requires dop.reqWriteNode.loc !in indirectionTable.locs.Values

    requires forall r | r in indirectionTable.locs ::
        indirectionTable.locs[r].addr != dop.reqWriteNode.loc.addr

    ensures M.WFIndirectionTable(indirectionTable')
    ensures WFIndirectionTableWrtDisk(indirectionTable', s'.disk.nodes)
    ensures DiskCacheGraph(indirectionTable, s.disk, s.machine.cache)
         == DiskCacheGraph(indirectionTable', s'.disk, s'.machine.cache)
  {
    assert dop.id !in s.disk.reqWriteNodes;

    WriteBackNodeReqStepUniqueLBAs(k, s, s', dop, vop, ref);

    forall r | r in indirectionTable'.locs
    ensures indirectionTable'.locs[r] in s'.disk.nodes
    {
      if (r == ref && ref !in indirectionTable.locs) {
        assert s'.disk.reqWriteNodes[dop.id] == dop.reqWriteNode.loc;
        assert indirectionTable'.locs[r] in s'.disk.nodes;
      } else {
        assert indirectionTable'.locs[r] in s.disk.nodes;
        if overlap(indirectionTable'.locs[r],
            dop.reqWriteNode.loc) {
          overlappingNodesSameAddr(
            indirectionTable'.locs[r],
            dop.reqWriteNode.loc);
          assert false;
        }
        assert indirectionTable'.locs[r] in s'.disk.nodes;
      }
    }

    forall r | r in indirectionTable.graph
    ensures DiskCacheLookup(indirectionTable, s.disk, s.machine.cache, r)
         == DiskCacheLookup(indirectionTable', s'.disk, s'.machine.cache, r)
    {
      if (r == ref) {
        if ref in indirectionTable'.locs && dop.reqWriteNode.loc == indirectionTable'.locs[ref] {
          //assert DiskMapUpdate(s.disk.nodes, s'.disk.nodes, dop.reqWriteNode.loc, dop.reqWriteNode.node);
          assert dop.reqWriteNode.node == s.machine.cache[ref];
          assert dop.reqWriteNode.loc == indirectionTable'.locs[ref];
          assert DiskCacheLookup(indirectionTable', s'.disk, s'.machine.cache, r)
              == s'.disk.nodes[indirectionTable'.locs[ref]]
              == s.machine.cache[ref]
              == DiskCacheLookup(indirectionTable, s.disk, s.machine.cache, r);
          assert DiskCacheLookup(indirectionTable, s.disk, s.machine.cache, r) == DiskCacheLookup(indirectionTable', s'.disk, s'.machine.cache, r);
        } else {
          if overlap(indirectionTable'.locs[r],
              dop.reqWriteNode.loc) {
            overlappingNodesSameAddr(
              indirectionTable'.locs[r],
              dop.reqWriteNode.loc);
            assert false;
          }

          assert DiskCacheLookup(indirectionTable, s.disk, s.machine.cache, r) == DiskCacheLookup(indirectionTable', s'.disk, s'.machine.cache, r);
        }
      } else if (r in indirectionTable.locs) {
        if overlap(indirectionTable'.locs[r],
            dop.reqWriteNode.loc) {
          overlappingNodesSameAddr(
            indirectionTable'.locs[r],
            dop.reqWriteNode.loc);
          assert false;
        }

        assert DiskCacheLookup(indirectionTable, s.disk, s.machine.cache, r) == DiskCacheLookup(indirectionTable', s'.disk, s'.machine.cache, r);
      } else {

        assert DiskCacheLookup(indirectionTable, s.disk, s.machine.cache, r) == DiskCacheLookup(indirectionTable', s'.disk, s'.machine.cache, r);
      }
    }
  }

  lemma WriteBackNodeReqStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
    requires Inv(k, s)
    requires M.WriteBackNodeReq(k.machine, s.machine, s'.machine, dop, vop, ref)
    requires D.RecvWriteNode(k.disk, s.disk, s'.disk, dop);

    ensures DiskChangesPreservesPersistentAndFrozen(k, s, s')
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
    ensures FrozenLoc(k, s') == FrozenLoc(k, s)
    ensures PersistentLoc(k, s') == PersistentLoc(k, s)
  {
    WriteBackNodeReqStepPreservesDiskGraph(k, s, s', dop, vop, ref, s.machine.persistentIndirectionTable);
    WriteBackNodeReqStepPreservesDiskCacheGraph(k, s, s', dop, vop, ref, s.machine.ephemeralIndirectionTable, s'.machine.ephemeralIndirectionTable);
    if s.machine.frozenIndirectionTable.Some? {
      WriteBackNodeReqStepPreservesDiskCacheGraph(k, s, s', dop, vop, ref, s.machine.frozenIndirectionTable.value, s'.machine.frozenIndirectionTable.value);
    }

    /*forall ref | ref in s.machine.persistentIndirectionTable.locs
    ensures s.machine.persistentIndirectionTable.locs[ref] in s'.disk.nodes
    {
      if overlap(s.machine.persistentIndirectionTable.locs[ref], dop.reqWriteNode.loc) {
        overlappingNodesSameAddr(s.machine.persistentIndirectionTable.locs[ref], dop.reqWriteNode.loc);
        assert false;
      }
    }*/

    //assert WFDiskGraphOfLoc(k, s',
    //    s.machine.persistentIndirectionTableLoc);
  }

  lemma WriteBackNodeReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
    requires Inv(k, s)
    requires M.WriteBackNodeReq(k.machine, s.machine, s'.machine, dop, vop, ref)
    requires D.RecvWriteNode(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    WriteBackNodeReqStepUniqueLBAs(k, s, s', dop, vop, ref);
    WriteBackNodeReqStepPreservesGraphs(k, s, s', dop, vop, ref);

    forall id1 | id1 in s'.disk.reqReadNodes
    ensures s'.disk.reqReadNodes[id1] != s'.disk.reqWriteNodes[dop.id]
    ensures !overlap(s'.disk.reqReadNodes[id1], s'.disk.reqWriteNodes[dop.id])
    {
      if overlap(s'.disk.reqReadNodes[id1], s'.disk.reqWriteNodes[dop.id]) {
        overlappingNodesSameAddr(
            s'.disk.reqReadNodes[id1],
            s'.disk.reqWriteNodes[dop.id]);
      }
    }

    forall r | r in s'.machine.cache &&
      r in s'.machine.ephemeralIndirectionTable.locs
    ensures s'.machine.cache[r]
        == s'.disk.nodes[s'.machine.ephemeralIndirectionTable.locs[r]]
    {
      if overlap(s'.machine.ephemeralIndirectionTable.locs[r], dop.reqWriteNode.loc) {
        overlappingNodesSameAddr(s'.machine.ephemeralIndirectionTable.locs[r], dop.reqWriteNode.loc);
      }
    }

  }

  ////////////////////////////////////////////////////
  ////////////////////// WriteBackNodeResp
  //////////////////////

  lemma WriteBackNodeRespStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.WriteBackNodeResp(k.machine, s.machine, s'.machine, dop, vop)
    requires D.AckWriteNode(k.disk, s.disk, s'.disk, dop);

    ensures DiskGraphMap(k, s') == DiskGraphMap(k, s)
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
    ensures FrozenLoc(k, s') == FrozenLoc(k, s)
    ensures PersistentLoc(k, s') == PersistentLoc(k, s)
  {
    if (s.machine.Ready?) {
      assert DiskCacheGraph(s.machine.ephemeralIndirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.ephemeralIndirectionTable, s'.disk, s'.machine.cache);
    }
    if (UseFrozenGraph(k, s)) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma WriteBackNodeRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.WriteBackNodeResp(k.machine, s.machine, s'.machine, dop, vop)
    requires D.AckWriteNode(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    WriteBackNodeRespStepPreservesGraphs(k, s, s', dop, vop);
  }

  ////////////////////////////////////////////////////
  ////////////////////// WriteBackIndirectionTableReq
  //////////////////////

  lemma WriteBackIndirectionTableReqStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTableReq(k.machine, s.machine, s'.machine, dop, vop)
    requires D.RecvWriteIndirectionTable(k.disk, s.disk, s'.disk, dop);

    ensures DiskChangesPreservesPersistentAndFrozen(k, s, s')
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
    ensures FrozenLoc(k, s') == FrozenLoc(k, s)
    ensures PersistentLoc(k, s') == PersistentLoc(k, s)
  {
    assert forall id | id in s.disk.reqWriteIndirectionTables :: id in s'.disk.reqWriteIndirectionTables;

    assert WFIndirectionTableWrtDisk(s'.machine.ephemeralIndirectionTable, s'.disk.nodes);

    assert s'.machine.Ready? && s'.machine.frozenIndirectionTable.Some? ==> WFIndirectionTableWrtDisk(s'.machine.frozenIndirectionTable.value, s'.disk.nodes);

    if (s.machine.Ready?) {
      assert DiskCacheGraph(s.machine.ephemeralIndirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.ephemeralIndirectionTable, s'.disk, s'.machine.cache);
    }
    if (UseFrozenGraph(k, s)) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }

    assert WFDiskGraphOfLoc(k, s', s'.machine.frozenIndirectionTableLoc.value);
  }

  lemma WriteBackIndirectionTableReqStep_WriteRequestsDontOverlap(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTableReq(k.machine, s.machine, s'.machine, dop, vop)
    requires D.RecvWriteIndirectionTable(k.disk, s.disk, s'.disk, dop);
    ensures WriteRequestsDontOverlap(s'.disk.reqWriteIndirectionTables)
    ensures WriteRequestsAreDistinct(s'.disk.reqWriteIndirectionTables)
  {
    forall id1 | id1 in s'.disk.reqWriteIndirectionTables
    ensures s'.disk.reqWriteIndirectionTables[id1] == s'.disk.reqWriteIndirectionTables[dop.id]
        ==> id1 == dop.id
    ensures overlap(s'.disk.reqWriteIndirectionTables[id1], s'.disk.reqWriteIndirectionTables[dop.id])
        ==> id1 == dop.id
    {
      if s'.disk.reqWriteIndirectionTables[id1] == s'.disk.reqWriteIndirectionTables[dop.id] {
        assert s'.disk.reqWriteIndirectionTables[id1].addr == s'.disk.reqWriteIndirectionTables[dop.id].addr;
      }
      if overlap(s'.disk.reqWriteIndirectionTables[id1], s'.disk.reqWriteIndirectionTables[dop.id]) {
        overlappingIndirectionTablesSameAddr(
            s'.disk.reqWriteIndirectionTables[id1],
            s'.disk.reqWriteIndirectionTables[dop.id]);
      }
    }
  }

  lemma WriteBackIndirectionTableReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTableReq(k.machine, s.machine, s'.machine, dop, vop)
    requires D.RecvWriteIndirectionTable(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    WriteBackIndirectionTableReqStepPreservesGraphs(k, s, s', dop, vop);
    WriteBackIndirectionTableReqStep_WriteRequestsDontOverlap(k, s, s', dop, vop);

    forall id1 | id1 in s'.disk.reqReadIndirectionTables
    ensures s'.disk.reqReadIndirectionTables[id1] != s'.disk.reqWriteIndirectionTables[dop.id]
    ensures !overlap(s'.disk.reqReadIndirectionTables[id1], s'.disk.reqWriteIndirectionTables[dop.id])
    {
      assert ValidNodeLocation(s'.disk.reqReadIndirectionTables[id1]);
      if overlap(s'.disk.reqReadIndirectionTables[id1], s'.disk.reqWriteIndirectionTables[dop.id]) {
        overlappingIndirectionTablesSameAddr(
            s'.disk.reqReadIndirectionTables[id1],
            s'.disk.reqWriteIndirectionTables[dop.id]);
      }
    }
  }

  ////////////////////////////////////////////////////
  ////////////////////// WriteBackIndirectionTableResp
  //////////////////////

  lemma WriteBackIndirectionTableRespStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTableResp(k.machine, s.machine, s'.machine, dop, vop)
    requires D.AckWriteIndirectionTable(k.disk, s.disk, s'.disk, dop);

    ensures FrozenLoc(k, s) == None
    ensures FrozenLoc(k, s') == Some(vop.loc)

    ensures FrozenGraphOpt(k, s).Some?
    ensures FrozenLoc(k, s').value in DiskGraphMap(k, s)
    ensures DiskGraphMap(k, s)[FrozenLoc(k, s').value] == FrozenGraphOpt(k, s).value

    ensures DiskGraphMap(k, s') == DiskGraphMap(k, s)
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
    ensures PersistentLoc(k, s') == PersistentLoc(k, s)
  {
    M.WriteBackIndirectionTableRespStepPreservesInv(k.machine, s.machine, s'.machine, dop, vop);
    if (s.machine.Ready?) {
      assert DiskCacheGraph(s.machine.ephemeralIndirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.ephemeralIndirectionTable, s'.disk, s'.machine.cache);
    }
    if (UseFrozenGraph(k, s)) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma WriteBackIndirectionTableRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.WriteBackIndirectionTableResp(k.machine, s.machine, s'.machine, dop, vop)
    requires D.AckWriteIndirectionTable(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    M.WriteBackIndirectionTableRespStepPreservesInv(k.machine, s.machine, s'.machine, dop, vop);
    WriteBackIndirectionTableRespStepPreservesGraphs(k, s, s', dop, vop);
  }

  ////////////////////////////////////////////////////
  ////////////////////// Dirty
  //////////////////////

  lemma DirtyStepUpdatesGraph(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires M.Dirty(k.machine, s.machine, s'.machine, ref, block)
    requires s.disk == s'.disk

    ensures DiskGraphMap(k, s') == DiskGraphMap(k, s)
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures FrozenLoc(k, s') == FrozenLoc(k, s);
    ensures PersistentLoc(k, s') == PersistentLoc(k, s);

    ensures EphemeralGraphOpt(k, s).Some?
    ensures EphemeralGraphOpt(k, s').Some?
    ensures ref in EphemeralGraphOpt(k, s).value
    ensures EphemeralGraphOpt(k, s').value == EphemeralGraphOpt(k, s).value[ref := block]
    ensures forall key | key in M.G.Successors(block) ::
        key in EphemeralGraphOpt(k, s).value.Keys
  {
    if (UseFrozenGraph(k, s')) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma DirtyStepPreservesInv(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires M.Dirty(k.machine, s.machine, s'.machine, ref, block)
    requires s.disk == s'.disk
    ensures Inv(k, s')
  {
  }

  ////////////////////////////////////////////////////
  ////////////////////// Alloc
  //////////////////////

  lemma AllocStepUpdatesGraph(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires M.Alloc(k.machine, s.machine, s'.machine, ref, block)
    requires s.disk == s'.disk

    ensures DiskGraphMap(k, s') == DiskGraphMap(k, s)
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures FrozenLoc(k, s') == FrozenLoc(k, s);
    ensures PersistentLoc(k, s') == PersistentLoc(k, s);

    ensures EphemeralGraphOpt(k, s).Some?
    ensures ref !in EphemeralGraphOpt(k, s).value
    ensures EphemeralGraphOpt(k, s').value == EphemeralGraphOpt(k, s).value[ref := block]
    ensures forall key | key in M.G.Successors(block) ::
        key in EphemeralGraphOpt(k, s).value.Keys
  {
    if (UseFrozenGraph(k, s)) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma AllocStepPreservesInv(k: Constants, s: Variables, s': Variables, ref: Reference, block: Node)
    requires Inv(k, s)
    requires M.Alloc(k.machine, s.machine, s'.machine, ref, block)
    requires s.disk == s'.disk
    ensures Inv(k, s')
  {
  }

  ////////////////////////////////////////////////////
  ////////////////////// Transaction
  //////////////////////

  lemma OpPreservesInv(k: Constants, s: Variables, s': Variables, op: Op)
    requires Inv(k, s)
    requires M.OpStep(k.machine, s.machine, s'.machine, op)
    requires s.disk == s'.disk
    ensures Inv(k, s')
  {
    match op {
      case WriteOp(ref, block) => DirtyStepPreservesInv(k, s, s', ref, block);
      case AllocOp(ref, block) => AllocStepPreservesInv(k, s, s', ref, block);
    }
  }

  lemma OpTransactionPreservesInv(k: Constants, s: Variables, s': Variables, ops: seq<Op>)
    requires Inv(k, s)
    requires M.OpTransaction(k.machine, s.machine, s'.machine, ops)
    requires s.disk == s'.disk
    ensures Inv(k, s')
    decreases |ops|
  {
    if |ops| == 0 {
    } else if |ops| == 1 {
      OpPreservesInv(k, s, s', ops[0]);
    } else {
      var ops1, smid, ops2 := M.SplitTransaction(k.machine, s.machine, s'.machine, ops);
      OpTransactionPreservesInv(k, s, AsyncSectorDiskModelVariables(smid, s.disk), ops1);
      OpTransactionPreservesInv(k, AsyncSectorDiskModelVariables(smid, s.disk), s', ops2);
    }
  }

  lemma TransactionStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ops: seq<Op>)
    requires Inv(k, s)
    requires M.Transaction(k.machine, s.machine, s'.machine, dop, vop, ops)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
    decreases |ops|
  {
    OpTransactionPreservesInv(k, s, s', ops);
  }

  ////////////////////////////////////////////////////
  ////////////////////// Unalloc
  //////////////////////

  lemma UnallocStepUpdatesGraph(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
    requires Inv(k, s)
    requires M.Unalloc(k.machine, s.machine, s'.machine, dop, vop, ref)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);

    ensures DiskGraphMap(k, s') == DiskGraphMap(k, s)
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures PersistentLoc(k, s') == PersistentLoc(k, s);
    ensures FrozenLoc(k, s') == FrozenLoc(k, s);

    ensures EphemeralGraphOpt(k, s).Some?
    ensures EphemeralGraphOpt(k, s').Some?
    ensures EphemeralGraphOpt(k, s').value == IMapRemove1(EphemeralGraphOpt(k, s).value, ref)
    ensures ref in EphemeralGraphOpt(k, s).value
    ensures forall r | r in EphemeralGraphOpt(k, s).value ::
        ref !in M.G.Successors(EphemeralGraphOpt(k, s).value[r])
  {
    if (UseFrozenGraph(k, s)) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma UnallocStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
    requires Inv(k, s)
    requires M.Unalloc(k.machine, s.machine, s'.machine, dop, vop, ref)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    /*
    var graph := EphemeralGraph(k, s);
    var graph' := EphemeralGraph(k, s');
    var cache := s.machine.cache;
    var cache' := s'.machine.cache;
    */
  }

  ////////////////////////////////////////////////////
  ////////////////////// PageInReq
  //////////////////////

  lemma PageInNodeReqStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
    requires Inv(k, s)
    requires M.PageInNodeReq(k.machine, s.machine, s'.machine, dop, vop, ref)
    requires D.RecvReadNode(k.disk, s.disk, s'.disk, dop);

    ensures DiskGraphMap(k, s') == DiskGraphMap(k, s)
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
    ensures FrozenLoc(k, s') == FrozenLoc(k, s)
    ensures PersistentLoc(k, s') == PersistentLoc(k, s)
  {
    if (s.machine.Ready?) {
      assert DiskCacheGraph(s.machine.ephemeralIndirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.ephemeralIndirectionTable, s'.disk, s'.machine.cache);
    }
    if (UseFrozenGraph(k, s)) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma PageInNodeReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
    requires Inv(k, s)
    requires M.PageInNodeReq(k.machine, s.machine, s'.machine, dop, vop, ref)
    requires D.RecvReadNode(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    PageInNodeReqStepPreservesGraphs(k, s, s', dop, vop, ref);

    forall id | id in s'.machine.outstandingBlockReads
    ensures CorrectInflightBlockRead(k, s', id, s'.machine.outstandingBlockReads[id].ref)
    {
    }

    forall id2 | id2 in s'.disk.reqWriteNodes
    ensures dop.loc != s'.disk.reqWriteNodes[id2]
    ensures !overlap(dop.loc, s'.disk.reqWriteNodes[id2])
    {
      if overlap(dop.loc, s'.disk.reqWriteNodes[id2]) {
        overlappingLocsSameType(dop.loc, s'.disk.reqWriteNodes[id2]);
        overlappingNodesSameAddr(dop.loc, s'.disk.reqWriteNodes[id2]);
      }
    }
  }

  ////////////////////////////////////////////////////
  ////////////////////// PageInNodeResp
  //////////////////////

  lemma PageInNodeRespStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.PageInNodeResp(k.machine, s.machine, s'.machine, dop, vop)
    requires D.AckReadNode(k.disk, s.disk, s'.disk, dop);

    ensures DiskGraphMap(k, s') == DiskGraphMap(k, s)
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
    ensures FrozenLoc(k, s') == FrozenLoc(k, s)
    ensures PersistentLoc(k, s') == PersistentLoc(k, s)
  {
    if (s.machine.Ready?) {
      assert DiskCacheGraph(s.machine.ephemeralIndirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.ephemeralIndirectionTable, s'.disk, s'.machine.cache);
    }
    if (UseFrozenGraph(k, s)) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma PageInNodeRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.PageInNodeResp(k.machine, s.machine, s'.machine, dop, vop)
    requires D.AckReadNode(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    PageInNodeRespStepPreservesGraphs(k, s, s', dop, vop);
  }

  ////////////////////////////////////////////////////
  ////////////////////// PageInIndirectionTableReq
  //////////////////////

  lemma PageInIndirectionTableReqStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.PageInIndirectionTableReq(k.machine, s.machine, s'.machine, dop, vop)
    requires D.RecvReadIndirectionTable(k.disk, s.disk, s'.disk, dop);

    ensures DiskGraphMap(k, s') == DiskGraphMap(k, s)
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
    ensures FrozenLoc(k, s') == FrozenLoc(k, s)
    ensures PersistentLoc(k, s') == PersistentLoc(k, s)
  {
    if (UseFrozenGraph(k, s)) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma PageInIndirectionTableReqStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.PageInIndirectionTableReq(k.machine, s.machine, s'.machine, dop, vop)
    requires D.RecvReadIndirectionTable(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    PageInIndirectionTableReqStepPreservesGraphs(k, s, s', dop, vop);
  }

  ////////////////////////////////////////////////////
  ////////////////////// PageInIndirectionTableResp
  //////////////////////

  lemma PageInIndirectionTableRespStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.PageInIndirectionTableResp(k.machine, s.machine, s'.machine, dop, vop)
    requires D.AckReadIndirectionTable(k.disk, s.disk, s'.disk, dop);

    ensures DiskGraphMap(k, s') == DiskGraphMap(k, s)
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
    ensures FrozenLoc(k, s') == FrozenLoc(k, s)
    ensures PersistentLoc(k, s') == PersistentLoc(k, s)
  {
    assert LoadingGraph(k, s)
        == EphemeralGraph(k, s');
  }

  lemma PageInIndirectionTableRespStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.PageInIndirectionTableResp(k.machine, s.machine, s'.machine, dop, vop)
    requires D.AckReadIndirectionTable(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    PageInIndirectionTableRespStepPreservesGraphs(k, s, s', dop, vop);
  }

  ////////////////////////////////////////////////////
  ////////////////////// ReceiveLoc
  //////////////////////

  lemma ReceiveLocStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.ReceiveLoc(k.machine, s.machine, s'.machine, dop, vop)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    requires vop.loc in DiskGraphMap(k, s)

    ensures PersistentLoc(k, s) == None
    ensures DiskGraphMap(k, s') == DiskGraphMap(k, s)
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures PersistentLoc(k, s') == Some(vop.loc)
    ensures vop.loc in DiskGraphMap(k, s)
    ensures EphemeralGraphOpt(k, s').Some?
    ensures EphemeralGraphOpt(k, s').value ==
        DiskGraphMap(k, s)[vop.loc]
    ensures FrozenLoc(k, s') == FrozenLoc(k, s)
  {
    assert WFSuccs(k, s, vop.loc);
    assert WFDiskGraphOfLoc(k, s, vop.loc);

    if (s.machine.Ready?) {
      assert DiskCacheGraph(s.machine.ephemeralIndirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.ephemeralIndirectionTable, s'.disk, s'.machine.cache);
    }
    if (UseFrozenGraph(k, s)) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma ReceiveLocStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.ReceiveLoc(k.machine, s.machine, s'.machine, dop, vop)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    requires WFSuccs(k, s, vop.loc);
    ensures Inv(k, s')
  {
    ReceiveLocStepPreservesGraphs(k, s, s', dop, vop);
  }

  ////////////////////////////////////////////////////
  ////////////////////// Evict
  //////////////////////

  lemma EvictStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
    requires Inv(k, s)
    requires M.Evict(k.machine, s.machine, s'.machine, dop, vop, ref)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);

    ensures DiskGraphMap(k, s') == DiskGraphMap(k, s)
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
    ensures FrozenLoc(k, s') == FrozenLoc(k, s)
    ensures PersistentLoc(k, s') == PersistentLoc(k, s)
  {
    if (s.machine.Ready?) {
      assert DiskCacheGraph(s.machine.ephemeralIndirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.ephemeralIndirectionTable, s'.disk, s'.machine.cache);
    }
    if (UseFrozenGraph(k, s)) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma EvictStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, ref: Reference)
    requires Inv(k, s)
    requires M.Evict(k.machine, s.machine, s'.machine, dop, vop, ref)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    EvictStepPreservesGraphs(k, s, s', dop, vop, ref);
  }

  ////////////////////////////////////////////////////
  ////////////////////// Freeze
  //////////////////////

  lemma FreezeStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.Freeze(k.machine, s.machine, s'.machine, dop, vop)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures M.Inv(k.machine, s'.machine);

    ensures DiskGraphMap(k, s') == DiskGraphMap(k, s)
    ensures FrozenGraphOpt(k, s') == EphemeralGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
    ensures FrozenLoc(k, s') == None
    ensures PersistentLoc(k, s') == PersistentLoc(k, s)
  {
    M.FreezeStepPreservesInv(k.machine, s.machine, s'.machine, dop, vop);
  }

  lemma FreezeStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.Freeze(k.machine, s.machine, s'.machine, dop, vop)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    FreezeStepPreservesGraphs(k, s, s', dop, vop);
  }

  ////////////////////////////////////////////////////
  ////////////////////// CleanUp
  //////////////////////

  lemma CleanUpStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.CleanUp(k.machine, s.machine, s'.machine, dop, vop)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures M.Inv(k.machine, s'.machine);

    ensures DiskGraphMap(k, s') == DiskGraphMap(k, s)
    ensures FrozenGraphOpt(k, s') == None
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
    ensures FrozenLoc(k, s') == None
    ensures PersistentLoc(k, s') == FrozenLoc(k, s)
  {
  }

  lemma CleanUpStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.CleanUp(k.machine, s.machine, s'.machine, dop, vop)
    requires D.Stutter(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    M.CleanUpStepPreservesInv(k.machine, s.machine, s'.machine, dop, vop);
    CleanUpStepPreservesGraphs(k, s, s', dop, vop);
  }

  ////////////////////////////////////////////////////
  ////////////////////// No-Op
  //////////////////////

  lemma NoOpStepPreservesGraphs(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.NoOp(k.machine, s.machine, s'.machine, dop, vop)
    requires D.Next(k.disk, s.disk, s'.disk, dop);

    ensures DiskGraphMap(k, s') == DiskGraphMap(k, s)
    ensures FrozenGraphOpt(k, s') == FrozenGraphOpt(k, s);
    ensures EphemeralGraphOpt(k, s') == EphemeralGraphOpt(k, s);
    ensures FrozenLoc(k, s') == FrozenLoc(k, s)
    ensures PersistentLoc(k, s') == PersistentLoc(k, s)
  {
    if (s.machine.Ready?) {
      assert DiskCacheGraph(s.machine.ephemeralIndirectionTable, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.ephemeralIndirectionTable, s'.disk, s'.machine.cache);
    }
    if (UseFrozenGraph(k, s)) {
      assert DiskCacheGraph(s.machine.frozenIndirectionTable.value, s.disk, s.machine.cache)
          == DiskCacheGraph(s'.machine.frozenIndirectionTable.value, s'.disk, s'.machine.cache);
    }
  }

  lemma NoOpStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp)
    requires Inv(k, s)
    requires M.NoOp(k.machine, s.machine, s'.machine, dop, vop)
    requires D.Next(k.disk, s.disk, s'.disk, dop);
    ensures Inv(k, s')
  {
    NoOpStepPreservesGraphs(k, s, s', dop, vop);
  }

  ////////////////////////////////////////////////////
  ////////////////////// MachineStep
  //////////////////////

  lemma MachineStepPreservesInv(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, machineStep: M.Step)
    requires Inv(k, s)
    requires Machine(k, s, s', dop, vop, machineStep)
    ensures Inv(k, s')
  {
    match machineStep {
      case WriteBackNodeReqStep(ref) => WriteBackNodeReqStepPreservesInv(k, s, s', dop, vop, ref);
      case WriteBackNodeRespStep => WriteBackNodeRespStepPreservesInv(k, s, s', dop, vop);
      case WriteBackIndirectionTableReqStep => WriteBackIndirectionTableReqStepPreservesInv(k, s, s', dop, vop);
      case WriteBackIndirectionTableRespStep => WriteBackIndirectionTableRespStepPreservesInv(k, s, s', dop, vop);
      case UnallocStep(ref) => UnallocStepPreservesInv(k, s, s', dop, vop, ref);
      case PageInNodeReqStep(ref) => PageInNodeReqStepPreservesInv(k, s, s', dop, vop, ref);
      case PageInNodeRespStep => PageInNodeRespStepPreservesInv(k, s, s', dop, vop);
      case PageInIndirectionTableReqStep => PageInIndirectionTableReqStepPreservesInv(k, s, s', dop, vop);
      case PageInIndirectionTableRespStep => PageInIndirectionTableRespStepPreservesInv(k, s, s', dop, vop);
      case ReceiveLocStep => ReceiveLocStepPreservesInv(k, s, s', dop, vop);
      case EvictStep(ref) => EvictStepPreservesInv(k, s, s', dop, vop, ref);
      case FreezeStep => FreezeStepPreservesInv(k, s, s', dop, vop);
      case CleanUpStep => CleanUpStepPreservesInv(k, s, s', dop, vop);
      case NoOpStep => { NoOpStepPreservesInv(k, s, s', dop, vop); }
      case TransactionStep(ops) => TransactionStepPreservesInv(k, s, s', dop, vop, ops);
    }
  }

  ////////////////////////////////////////////////////
  ////////////////////// Crash
  //////////////////////

  lemma CrashPreservesGraphs(k: Constants, s: Variables, s': Variables, vop: VOp)
    requires Inv(k, s)
    requires Crash(k, s, s', vop)

    ensures DiskChangesPreservesPersistentAndFrozen(k, s, s')
    ensures FrozenGraphOpt(k, s') == None
    ensures EphemeralGraphOpt(k, s') == None
    ensures FrozenLoc(k, s') == None
    ensures PersistentLoc(k, s') == None
  {
    if PersistentLoc(k, s).Some? {
      var persistentLoc := PersistentLoc(k, s).value;
      if !D.UntouchedLoc(persistentLoc, s.disk.reqWriteIndirectionTables) {
        var id :| id in s.disk.reqWriteIndirectionTables && overlap(persistentLoc, s.disk.reqWriteIndirectionTables[id]);
        overlappingIndirectionTablesSameAddr(
            persistentLoc, s.disk.reqWriteIndirectionTables[id]);
      }
      var indirectionTable := s.disk.indirectionTables[persistentLoc];
      //assert M.WFCompleteIndirectionTable(indirectionTable);
      forall ref | ref in indirectionTable.locs
      ensures indirectionTable.locs[ref] in s.disk.nodes
      ensures indirectionTable.locs[ref] in s'.disk.nodes
      ensures s.disk.nodes[indirectionTable.locs[ref]] == s'.disk.nodes[indirectionTable.locs[ref]]
      {
        var loc := indirectionTable.locs[ref];
        //assert loc in indirectionTable.locs.Values;
        //assert ValidNodeLocation(loc);
        if !D.UntouchedLoc(loc, s.disk.reqWriteNodes) {
          var id :| id in s.disk.reqWriteNodes && overlap(loc, s.disk.reqWriteNodes[id]);
          overlappingNodesSameAddr(
              loc, s.disk.reqWriteNodes[id]);
          assert false;
        }
        //assert loc in s'.disk.nodes;
        //assert s.disk.nodes[loc] == s'.disk.nodes[loc];
      }
    }
    if FrozenLoc(k, s).Some? {
      var frozenLoc := FrozenLoc(k, s).value;
      if !D.UntouchedLoc(frozenLoc, s.disk.reqWriteIndirectionTables) {
        var id :| id in s.disk.reqWriteIndirectionTables && overlap(frozenLoc, s.disk.reqWriteIndirectionTables[id]);
        overlappingIndirectionTablesSameAddr(
            frozenLoc, s.disk.reqWriteIndirectionTables[id]);
      }
      var indirectionTable := s.disk.indirectionTables[frozenLoc];
      //assert M.WFCompleteIndirectionTable(indirectionTable);
      forall ref | ref in indirectionTable.locs
      ensures indirectionTable.locs[ref] in s.disk.nodes
      ensures indirectionTable.locs[ref] in s'.disk.nodes
      ensures s.disk.nodes[indirectionTable.locs[ref]] == s'.disk.nodes[indirectionTable.locs[ref]]
      {
        var loc := indirectionTable.locs[ref];
        //assert loc in indirectionTable.locs.Values;
        //assert ValidNodeLocation(loc);
        if !D.UntouchedLoc(loc, s.disk.reqWriteNodes) {
          var id :| id in s.disk.reqWriteNodes && overlap(loc, s.disk.reqWriteNodes[id]);
          overlappingNodesSameAddr(
              loc, s.disk.reqWriteNodes[id]);
          assert false;
        }
        //assert loc in s'.disk.nodes;
        //assert s.disk.nodes[loc] == s'.disk.nodes[loc];
      }

    }
  }

  lemma CrashStepPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp)
    requires Inv(k, s)
    requires Crash(k, s, s', vop)
    ensures Inv(k, s')
  {
  }

  ////////////////////////////////////////////////////
  ////////////////////// NextStep
  //////////////////////

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', vop, step)
    ensures Inv(k, s')
  {
    match step {
      case MachineStep(dop, machineStep) => MachineStepPreservesInv(k, s, s', dop, vop, machineStep);
      case CrashStep => CrashStepPreservesInv(k, s, s', vop);
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, vop: VOp)
    requires Inv(k, s)
    requires Next(k, s, s', vop)
    ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', vop, step);
    NextStepPreservesInv(k, s, s', vop, step);
  }

  /*lemma ReadReqIdIsValid(k: Constants, s: Variables, id: D.ReqId)
  requires Inv(k, s)
  requires id in s.disk.reqReads
  ensures s.disk.reqReads[id].loc in s.disk.blocks
  {
  }*/

  ////////////////////////////////////////////////////
  ////////////////////// Reads
  //////////////////////

  lemma EphemeralGraphRead(k: Constants, s: Variables, op: M.ReadOp)
  requires Inv(k, s)
  requires M.ReadStep(k.machine, s.machine, op)
  ensures EphemeralGraphOpt(k, s).Some?
  ensures op.ref in EphemeralGraphOpt(k, s).value
  ensures EphemeralGraphOpt(k, s).value[op.ref] == op.node
  {
  }

  ////////////////////////////////////////////////////
  ////////////////////// Misc lemma
  //////////////////////

  /*lemma RequestsDontOverlap(k: Constants, s: Variables)
  requires Inv(k, s)
  ensures WriteRequestsDontOverlap(s.disk.reqWriteNodes)
  ensures ReadWritesDontOverlap(s.disk.reqReadNodes, s.disk.reqWriteNodes)
  ensures WriteRequestsDontOverlap(s.disk.reqWriteIndirectionTables)
  ensures ReadWritesDontOverlap(s.disk.reqReadIndirectionTables, s.disk.reqWriteIndirectionTables)
  {
  }*/

  lemma NewRequestReadNodeDoesntOverlap(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, step: M.Step, id: D.ReqId)
  requires Inv(k, s)
  requires M.NextStep(k.machine, s.machine, s'.machine, dop, vop, step)
  requires dop.ReqReadNodeOp?
  requires id in s.disk.reqWriteNodes
  ensures !overlap(dop.loc, s.disk.reqWriteNodes[id])
  {
    if overlap(dop.loc, s.disk.reqWriteNodes[id]) {
      overlappingNodesSameAddr(dop.loc, s.disk.reqWriteNodes[id]);
    }
  }

  lemma NewRequestReadIndirectionTableDoesntOverlap(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, step: M.Step, id: D.ReqId)
  requires Inv(k, s)
  requires M.NextStep(k.machine, s.machine, s'.machine, dop, vop, step)
  requires dop.ReqReadIndirectionTableOp?
  requires id in s.disk.reqWriteIndirectionTables
  ensures !overlap(dop.loc, s.disk.reqWriteIndirectionTables[id])
  {
    /*MachineStepPreservesInv(k, s, s', dop, vop, step);
    assert !overlap(
        s'.disk.reqReadIndirectionTables[dop.id],
        s'.disk.reqWriteIndirectionTables[id]);
    assert !overlap(dop.loc, s'.disk.reqWriteIndirectionTables[id]);*/
  }

  lemma NewRequestWriteNodeDoesntOverlap(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, step: M.Step, id: D.ReqId)
  requires Inv(k, s)
  requires M.NextStep(k.machine, s.machine, s'.machine, dop, vop, step)
  requires dop.ReqWriteNodeOp?
  requires id in s.disk.reqWriteNodes
  ensures !overlap(dop.reqWriteNode.loc, s.disk.reqWriteNodes[id])
  {
    if overlap(dop.reqWriteNode.loc, s.disk.reqWriteNodes[id]) {
      overlappingNodesSameAddr(dop.reqWriteNode.loc, s.disk.reqWriteNodes[id]);
    }
  }

  lemma NewRequestWriteIndirectionTableDoesntOverlap(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, step: M.Step, id: D.ReqId)
  requires Inv(k, s)
  requires M.NextStep(k.machine, s.machine, s'.machine, dop, vop, step)
  requires dop.ReqWriteIndirectionTableOp?
  requires id in s.disk.reqWriteIndirectionTables
  ensures !overlap(dop.reqWriteIndirectionTable.loc, s.disk.reqWriteIndirectionTables[id])
  {
    /*MachineStepPreservesInv(k, s, s', dop, vop, step);
    assert !overlap(
        s'.disk.reqWriteIndirectionTables[dop.id],
        s'.disk.reqWriteIndirectionTables[id]);
    assert !overlap(dop.reqWriteNode.loc, s'.disk.reqWriteIndirectionTables[id]);*/
  }

  lemma NewRequestWriteNodeDoesntOverlapRead(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, step: M.Step, id: D.ReqId)
  requires Inv(k, s)
  requires M.NextStep(k.machine, s.machine, s'.machine, dop, vop, step)
  requires dop.ReqWriteNodeOp?
  requires id in s.disk.reqReadNodes
  ensures !overlap(dop.reqWriteNode.loc, s.disk.reqReadNodes[id])
  {
    if overlap(dop.reqWriteNode.loc, s.disk.reqReadNodes[id]) {
      overlappingNodesSameAddr(dop.reqWriteNode.loc, s.disk.reqReadNodes[id]);
    }
  }

  lemma NewRequestWriteIndirectionTableDoesntOverlapRead(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, step: M.Step, id: D.ReqId)
  requires Inv(k, s)
  requires M.NextStep(k.machine, s.machine, s'.machine, dop, vop, step)
  requires dop.ReqWriteIndirectionTableOp?
  requires id in s.disk.reqReadIndirectionTables
  ensures !overlap(dop.reqWriteIndirectionTable.loc, s.disk.reqReadIndirectionTables[id])
  {
  }

  lemma NewRequestReadNodeIsValid(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, step: M.Step)
  requires Inv(k, s)
  requires M.NextStep(k.machine, s.machine, s'.machine, dop, vop, step)
  requires dop.ReqReadNodeOp?
  ensures dop.loc in s.disk.nodes
  {
  }

  lemma NewRequestReadIndirectionTableIsValid(k: Constants, s: Variables, s': Variables, dop: DiskOp, vop: VOp, step: M.Step)
  requires Inv(k, s)
  requires M.NextStep(k.machine, s.machine, s'.machine, dop, vop, step)
  requires dop.ReqReadIndirectionTableOp?
  ensures dop.loc in s.disk.indirectionTables
  {
  }

}
