include "Betree.dfy"
include "../lib/sequences.dfy"
include "../lib/Maps.dfy"
include "Graph.dfy"
include "AsyncDiskModel.dfy"
include "BlockCache.dfy"

abstract module AsyncBlockCache refines Transactable {
  import opened Maps
  import opened Options
  import LBAType

  import Disk = AsyncDisk

  type ReqId = Disk.ReqId
  type LBA = LBAType.LBA
  datatype Constants = Constants()
  function method IndirectionTableLBA() : LBA { LBAType.IndirectionTableLBA() }

  // TODO make indirectionTable take up more than one block
  datatype IndirectionTable = IndirectionTable(
      lbas: map<Reference, LBA>,
      graph: map<Reference, seq<Reference>>)

  datatype Sector =
    | SectorBlock(block: Node)
    | SectorIndirectionTable(indirectionTable: IndirectionTable)

  type DiskOp = Disk.DiskOp<LBA, Sector>

  // BlockCache stuff

  datatype OutstandingWrite = OutstandingWrite(ref: Reference, lba: LBA)
  datatype OutstandingRead = OutstandingRead(ref: Reference)
  datatype OutstandingIndirectionTableWrite = OutstandingIndirectionTableWrite(reqId: ReqId, indirectionTable: IndirectionTable)

  datatype Variables =
    | Ready(
        persistentIndirectionTable: IndirectionTable,
        ephemeralIndirectionTable: IndirectionTable,
        outstandingIndirectionTableWrite: Option<OutstandingIndirectionTableWrite>,
        
        outstandingBlockWrites: map<ReqId, OutstandingWrite>,
        outstandingBlockReads: map<ReqId, OutstandingRead>,

        cache: map<Reference, Node>)
    | Unready(outstandingIndirectionTableRead: Option<ReqId>)

  predicate IsAllocated(s: Variables, ref: Reference)
  requires s.Ready?
  {
    ref in s.ephemeralIndirectionTable.graph
  }
  predicate ValidLBAForNode(k: Constants, lba: LBA)
  {
    lba != IndirectionTableLBA()
  }

  datatype Step =
    | WriteBackReqStep(ref: Reference)
    | WriteBackRespStep
    | WriteBackIndirectionTableReqStep
    | WriteBackIndirectionTableRespStep
    | UnallocStep(ref: Reference)
    | PageInReqStep(ref: Reference)
    | PageInRespStep
    | PageInIndirectionTableReqStep
    | PageInIndirectionTableRespStep
    | EvictStep(ref: Reference)
    | NoOpStep
    | TransactionStep(ops: seq<Op>)

  predicate WriteBackReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.ReqWriteOp?
    && ref in s.cache
    && ValidLBAForNode(k, dop.reqWrite.lba)
    && dop.reqWrite.lba !in s.persistentIndirectionTable.lbas.Values
    && dop.reqWrite.lba !in s.ephemeralIndirectionTable.lbas.Values
    && dop.reqWrite.sector == SectorBlock(s.cache[ref])
    && s'.Ready?
    && s'.persistentIndirectionTable == s.persistentIndirectionTable
    && s'.ephemeralIndirectionTable.lbas == s.ephemeralIndirectionTable.lbas[ref := dop.reqWrite.lba]
    && s'.ephemeralIndirectionTable.graph == s.ephemeralIndirectionTable.graph
    && s'.cache == s.cache
    && s'.outstandingBlockWrites == s.outstandingBlockWrites[dop.id := OutstandingWrite(ref, dop.reqWrite.lba)]
    && s'.outstandingBlockReads == s.outstandingBlockReads
    && s'.outstandingIndirectionTableWrite == s'.outstandingIndirectionTableWrite
    && s.outstandingIndirectionTableWrite == s.outstandingIndirectionTableWrite
  }

  predicate WriteBackResp(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Ready?
    && dop.RespWriteOp?
    && dop.id in s.outstandingBlockWrites
    && s' == s.(outstandingBlockWrites := MapRemove1(s.outstandingBlockWrites, dop.id))
  }

  predicate WriteBackIndirectionTableReq(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Ready?
    && dop.ReqWriteOp?
    && dop.reqWrite.lba == IndirectionTableLBA()
    && dop.reqWrite.sector == SectorIndirectionTable(s.ephemeralIndirectionTable)
    && s.cache.Keys <= s.ephemeralIndirectionTable.lbas.Keys
    && s.outstandingIndirectionTableWrite.None?
    && s.outstandingBlockWrites == map[]
    && s' == s.(outstandingIndirectionTableWrite := Some(OutstandingIndirectionTableWrite(dop.id, s.ephemeralIndirectionTable)))
  }

  predicate WriteBackIndirectionTableResp(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && s.Ready?
    && dop.RespWriteOp?
    && s.outstandingIndirectionTableWrite.Some?
    && dop.id == s.outstandingIndirectionTableWrite.value.reqId
    && s' == s.(outstandingIndirectionTableWrite := None)
              .(persistentIndirectionTable := s.outstandingIndirectionTableWrite.value.indirectionTable)
  }

  predicate NoPredecessors(graph: map<Reference, seq<Reference>>, ref: Reference)
  {
    forall r | r in graph :: ref !in graph[r]
  }

  predicate Unalloc(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.NoDiskOp?

    && IsAllocated(s, ref)

    // We can only dealloc this if nothing is pointing to it.
    && ref != G.Root()
    && NoPredecessors(s.ephemeralIndirectionTable.graph, ref)

    && s'.Ready?
    && s'.persistentIndirectionTable == s.persistentIndirectionTable
    && s'.ephemeralIndirectionTable.lbas == MapRemove(s.ephemeralIndirectionTable.lbas, {ref})
    && s'.cache == MapRemove(s.cache, {ref})
    && s'.ephemeralIndirectionTable.graph == MapRemove(s.ephemeralIndirectionTable.graph, {ref})
  }

  predicate PageInReq(k: Constants, s: Variables, s': Variables, dop: DiskOp, ref: Reference)
  {
    && s.Ready?
    && dop.ReqReadOp?
    && IsAllocated(s, ref)
    && ref in s.ephemeralIndirectionTable.lbas
    && ref !in s.cache
    && s.ephemeralIndirectionTable.lbas[ref] == dop.reqRead.lba
    && s' == s.(outstandingBlockReads := s.outstandingBlockReads[dop.id := OutstandingRead(ref)])
  }
}

