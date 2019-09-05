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
  import MutableLru
  import opened BucketsLib

  import MM = MutableMap
  import ReferenceType`Internal

  type Reference = BT.G.Reference
  type Key = MS.Key
  type Message = Messages.Message
  type TreeMap = TTT.Tree<Message>

  type MutIndirectionTable = MM.ResizingHashMap<(Option<BC.Location>, seq<Reference>)>
  type MutIndirectionTableNullable = MM.ResizingHashMap?<(Option<BC.Location>, seq<Reference>)>

  type Node = IM.Node

  datatype Sector =
    | SectorBlock(block: Node)
    | SectorIndirectionTable(indirectionTable: MutIndirectionTable)
 
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
 
  function IIndirectionTableOpt(table: MutIndirectionTableNullable) : (result: Option<IM.IndirectionTable>)
  reads if table != null then {table} + table.Repr else {}
  {
    if table != null then
      Some(IIndirectionTable(table))
    else
      None
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

  class Variables {
    var ready: bool;

    var syncReqs: map<int, BC.SyncReqStatus>;

    // Ready
    var persistentIndirectionTable: MutIndirectionTable;
    var frozenIndirectionTable: MutIndirectionTableNullable;
    var ephemeralIndirectionTable: MutIndirectionTable;
    var outstandingIndirectionTableWrite: Option<BC.ReqId>;
    var outstandingBlockWrites: map<D.ReqId, BC.OutstandingWrite>;
    var outstandingBlockReads: map<D.ReqId, BC.OutstandingRead>;
    var cache: map<Reference, Node>;
    var lru: MutableLru.MutableLruQueue;
    var rootBucket: TreeMap;
    var rootBucketWeightBound: uint64;

    // Unready
    var outstandingIndirectionTableRead: Option<D.ReqId>;

    function Repr() : set<object>
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru
    {
      {this} +
      persistentIndirectionTable.Repr +
      ephemeralIndirectionTable.Repr +
      (if frozenIndirectionTable != null then frozenIndirectionTable.Repr else {}) +
      lru.Repr
    }

    predicate ReprInv()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru
    reads Repr()
    {
        // NOALIAS statically enforced no-aliasing would probably help here
        && persistentIndirectionTable.Repr !! ephemeralIndirectionTable.Repr
        && (frozenIndirectionTable != null ==> persistentIndirectionTable.Repr !! frozenIndirectionTable.Repr)
        && (frozenIndirectionTable != null ==> ephemeralIndirectionTable.Repr !! frozenIndirectionTable.Repr)
        && persistentIndirectionTable.Repr !! lru.Repr
        && ephemeralIndirectionTable.Repr !! lru.Repr
        && (frozenIndirectionTable != null ==> frozenIndirectionTable.Repr !! lru.Repr)
        && this !in ephemeralIndirectionTable.Repr
        && this !in persistentIndirectionTable.Repr
        && (frozenIndirectionTable != null ==> this !in frozenIndirectionTable.Repr)
        && this !in lru.Repr
    }

    predicate W()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru
    reads Repr()
    {
      && ReprInv()
      && persistentIndirectionTable.Inv()
      && (frozenIndirectionTable != null ==> frozenIndirectionTable.Inv())
      && ephemeralIndirectionTable.Inv()
      && TTT.TTTree(rootBucket)
      && lru.Inv()
    }

    function I() : IM.Variables
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru
    reads Repr()
    requires W()
    {
      if ready then (
        IM.Ready(IIndirectionTable(persistentIndirectionTable), IIndirectionTableOpt(frozenIndirectionTable), IIndirectionTable(ephemeralIndirectionTable), outstandingIndirectionTableWrite, outstandingBlockWrites, outstandingBlockReads, syncReqs, cache, lru.Queue, TTT.I(rootBucket), rootBucketWeightBound)
      ) else (
        IM.Unready(outstandingIndirectionTableRead, syncReqs)
      )
    }

    predicate WF()
    reads this, persistentIndirectionTable, ephemeralIndirectionTable,
        frozenIndirectionTable, lru
    reads Repr()
    {
      && W()
      && IM.WFVars(I())
    }

    constructor()
    ensures !ready
    ensures syncReqs == map[]
    ensures outstandingIndirectionTableRead == None
    ensures WF()
    {
      ready := false;
      syncReqs := map[];
      outstandingIndirectionTableRead := None;

      // Unused for the `ready = false` state but we need to initialize them.
      // (could make them nullable instead).
      lru := new MutableLru.MutableLruQueue();
      ephemeralIndirectionTable := new MM.ResizingHashMap(128);
      persistentIndirectionTable := new MM.ResizingHashMap(128);
      frozenIndirectionTable := null;
      rootBucket := TTT.EmptyTree;
    }
  }

  predicate Inv(k: M.Constants, s: Variables)
  reads s, s.persistentIndirectionTable, s.ephemeralIndirectionTable,
      s.frozenIndirectionTable, s.lru
  reads s.Repr()
  {
    && s.W()
    && IM.Inv(Ic(k), s.I())
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

  twostate predicate WellUpdated(s: Variables)
  reads s, s.persistentIndirectionTable, s.ephemeralIndirectionTable,
      s.frozenIndirectionTable, s.lru
  reads s.Repr()
  {
    && s.W()
    && (forall o | o in s.Repr() :: o in old(s.Repr()) || fresh(o))
  }
}
