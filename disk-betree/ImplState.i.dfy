include "../lib/MutableMap.i.dfy"
include "ImplModel.i.dfy"
include "MainDiskIOHandler.s.dfy"

module {:extern} ImplState {
  import opened Options
  import opened Sequences
  import opened NativeTypes
  import TTT = TwoThreeTree
  import IM = ImplModel

  import BT = PivotBetreeSpec`Internal
  import Messages = ValueMessage
  import MS = MapSpec
  import Pivots = PivotsLib
  import BC = BetreeGraphBlockCache
  import M = BetreeBlockCache
  import KMTable = KMTable
  import D = AsyncSectorDisk
  import MainDiskIOHandler
  import LruModel
  import opened BucketsLib

  import MM = MutableMap
  import ReferenceType`Internal

  type Reference = BT.G.Reference
  type Key = MS.Key
  type Message = Messages.Message
  type TreeMap = TTT.Tree<Message>

  type MutIndirectionTable = MM.ResizingHashMap<(Option<BC.Location>, seq<Reference>)>

  type Node = IM.Node
  datatype Variables =
    | Ready(
        persistentIndirectionTable: MutIndirectionTable,
        frozenIndirectionTable: Option<MutIndirectionTable>,
        ephemeralIndirectionTable: MutIndirectionTable,
        outstandingIndirectionTableWrite: Option<BC.ReqId>,
        outstandingBlockWrites: map<D.ReqId, BC.OutstandingWrite>,
        outstandingBlockReads: map<D.ReqId, BC.OutstandingRead>,
        syncReqs: map<int, BC.SyncReqStatus>,
        cache: map<Reference, Node>,
        lru: LruModel.LruQueue,
        rootBucket: TreeMap,
        rootBucketWeightBound: uint64)
    | Unready(outstandingIndirectionTableRead: Option<D.ReqId>, syncReqs: map<int, BC.SyncReqStatus>)
  datatype Sector =
    | SectorBlock(block: Node)
    | SectorIndirectionTable(indirectionTable: MutIndirectionTable)

  function VariablesReadSet(s: Variables): set<object>
  reads if s.Ready? then (
      {s.persistentIndirectionTable, s.ephemeralIndirectionTable} +
      (if s.frozenIndirectionTable.Some? then {s.frozenIndirectionTable.value} else {}))
      else {}
  {
    if s.Ready? then
      s.persistentIndirectionTable.Repr +
      s.ephemeralIndirectionTable.Repr +
      (if s.frozenIndirectionTable.Some? then s.frozenIndirectionTable.value.Repr else {})
    else
      {}
  }
  predicate VarsReprInv(vars: Variables)
  reads if vars.Ready? then (
      {vars.persistentIndirectionTable, vars.ephemeralIndirectionTable} +
      (if vars.frozenIndirectionTable.Some? then {vars.frozenIndirectionTable.value} else {}))
      else {}
  reads VariablesReadSet(vars)
  {
    match vars {
      case Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, _, _, _, _, _, _, _, _) => (
        // NOALIAS statically enforced no-aliasing would probably help here
        && persistentIndirectionTable.Repr !! ephemeralIndirectionTable.Repr
        && (frozenIndirectionTable.Some? ==> persistentIndirectionTable.Repr !! frozenIndirectionTable.value.Repr)
        && (frozenIndirectionTable.Some? ==> ephemeralIndirectionTable.Repr !! frozenIndirectionTable.value.Repr)
      )
      case Unready(outstandingIndirectionTableRead, syncReqs) => true
    }
  }
  predicate WVarsReady(vars: Variables)
  requires vars.Ready?
  reads {vars.persistentIndirectionTable, vars.ephemeralIndirectionTable} +
      (if vars.frozenIndirectionTable.Some? then {vars.frozenIndirectionTable.value} else {})
  reads VariablesReadSet(vars)
  {
    && vars.persistentIndirectionTable.Inv()
    && (vars.frozenIndirectionTable.Some? ==> vars.frozenIndirectionTable.value.Inv())
    && vars.ephemeralIndirectionTable.Inv()
    && TTT.TTTree(vars.rootBucket)
  }
  predicate WVars(vars: Variables)
  reads if vars.Ready? then (
      {vars.persistentIndirectionTable, vars.ephemeralIndirectionTable} +
      (if vars.frozenIndirectionTable.Some? then {vars.frozenIndirectionTable.value} else {}))
      else {}
  reads VariablesReadSet(vars)
  {
    && VarsReprInv(vars)
    && match vars {
      case Ready(_, _, _, _, _, _, _, _, _, _, _) => WVarsReady(vars)
      case Unready(outstandingIndirectionTableRead, syncReqs) => true
    }
  }
  predicate WFSector(sector: Sector)
  reads if sector.SectorIndirectionTable? then {sector.indirectionTable} + sector.indirectionTable.Repr else {}
  {
    && (sector.SectorIndirectionTable? ==> sector.indirectionTable.Inv())
  }

  function IIndirectionTable(table: MutIndirectionTable) : (result: IM.IndirectionTable)
  reads table, table.Repr
  {
    table.Contents
  }
  function IIndirectionTableOpt(table: Option<MutIndirectionTable>) : (result: Option<IM.IndirectionTable>)
  reads if table.Some? then {table.value} + table.value.Repr else {}
  {
    if table.Some? then
      Some(IIndirectionTable(table.value))
    else
      None
  }
  function IVars(vars: Variables) : IM.Variables
  requires WVars(vars)
  reads VariablesReadSet(vars)
  {
    match vars {
      case Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, syncReqs, cache, lru, rootBucket, rootBucketWeightBound) =>
        IM.Ready(IIndirectionTable(persistentIndirectionTable), IIndirectionTableOpt(frozenIndirectionTable), IIndirectionTable(ephemeralIndirectionTable), outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, syncReqs, cache, lru, TTT.I(rootBucket), rootBucketWeightBound)
      case Unready(outstandingIndirectionTableRead, syncReqs) => IM.Unready(outstandingIndirectionTableRead, syncReqs)
    }
  }
  function ISector(sector: Sector) : IM.Sector
  requires WFSector(sector)
  reads if sector.SectorIndirectionTable? then sector.indirectionTable.Repr else {}
  {
    match sector {
      case SectorBlock(node) => IM.SectorBlock(node)
      case SectorIndirectionTable(indirectionTable) => IM.SectorIndirectionTable(IIndirectionTable(indirectionTable))
    }
  }

  predicate WFVars(vars: Variables)
  reads if vars.Ready? then (
      {vars.persistentIndirectionTable, vars.ephemeralIndirectionTable} +
      (if vars.frozenIndirectionTable.Some? then {vars.frozenIndirectionTable.value} else {}))
      else {}
  reads VariablesReadSet(vars)
  {
    && WVars(vars)
    && IM.WFVars(IVars(vars))
  }

  predicate Inv(k: M.Constants, vars: Variables)
  reads if vars.Ready? then (
      {vars.persistentIndirectionTable, vars.ephemeralIndirectionTable} +
      (if vars.frozenIndirectionTable.Some? then {vars.frozenIndirectionTable.value} else {}))
      else {}
  reads VariablesReadSet(vars)
  {
    && WVars(vars)
    && IM.Inv(Ic(k), IVars(vars))
  }

  function Ic(k: M.Constants) : IM.Constants
  {
    IM.Constants()
  }

  function IIO(io: MainDiskIOHandler.DiskIOHandler) : IM.IO
  reads io
  {
    match io.diskOp() {
      case NoDiskOp => IM.IOInit(io.reservedId())
      case ReqReadOp(id, reqRead) => IM.IOReqRead(id, reqRead)
      case ReqWriteOp(id, reqWrite) => IM.IOReqWrite(id, reqWrite)
      case RespReadOp(id, respRead) => IM.IORespRead(id, respRead)
      case RespWriteOp(id, respWrite) => IM.IORespWrite(id, respWrite)
    }
  }
}
