include "PivotBetreeSpec.dfy"
include "Message.dfy"
include "../lib/Option.dfy"
include "SSTable.dfy"
include "BetreeBlockCache.dfy"
include "../lib/MutableMap.dfy"

module {:extern} ImplState {
  import opened Options
  import opened Sequences

  import BT = PivotBetreeSpec`Internal
  import Messages = ValueMessage
  import MS = MapSpec
  import Pivots = PivotsLib
  import BC = BetreeGraphBlockCache
  import M = BetreeBlockCache
  import SSTable = SSTable
  import D = AsyncSectorDisk

  import MM = MutableMap
  import ReferenceType`Internal

  type Reference = BT.G.Reference
  type Key = MS.Key
  type Message = Messages.Message

  type MutIndirectionTable = MM.ResizingHashMap<(Option<BC.LBA>, seq<Reference>)>

  datatype Node = Node(
      pivotTable: Pivots.PivotTable,
      children: Option<seq<Reference>>,
      buckets: seq<SSTable.SSTable>
    )
  datatype Variables =
    | Ready(
        persistentIndirectionTable: MutIndirectionTable, // this lets us keep track of available LBAs
                                                         // TODO replace with something that only tracks LBAs
        frozenIndirectionTable: Option<MutIndirectionTable>,
        ephemeralIndirectionTable: MutIndirectionTable,
        outstandingIndirectionTableWrite: Option<BC.ReqId>,
        outstandingBlockWrites: map<D.ReqId, BC.OutstandingWrite>,
        outstandingBlockReads: map<D.ReqId, BC.OutstandingRead>,
        syncReqs: map<int, BC.SyncReqStatus>,
        cache: map<Reference, Node>)
    | Unready(outstandingIndirectionTableRead: Option<D.ReqId>, syncReqs: map<int, BC.SyncReqStatus>)
  datatype Sector =
    | SectorBlock(block: Node)
    | SectorIndirectionTable(indirectionTable: MutIndirectionTable)

  predicate WFBuckets(buckets: seq<SSTable.SSTable>)
  {
    forall i | 0 <= i < |buckets| :: SSTable.WFSSTableMap(buckets[i])
  }
  predicate WFNode(node: Node)
  {
    WFBuckets(node.buckets)
  }
  predicate WFCache(cache: map<Reference, Node>)
  {
    forall ref | ref in cache :: WFNode(cache[ref])
  }
  predicate WFVars(vars: Variables)
  {
    match vars {
      case Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, syncReqs, cache) => WFCache(cache)
      case Unready(outstandingIndirectionTableRead, syncReqs) => true
    }
  }
  predicate WFSector(sector: Sector)
    reads if sector.SectorIndirectionTable? then sector.indirectionTable.Repr else {}
  {
    match sector {
      case SectorBlock(node) => WFNode(node)
      case SectorIndirectionTable(indirectionTable) => (
        && BC.WFCompleteIndirectionTable(IIndirectionTable(indirectionTable))
        && indirectionTable.Inv()
      )
    }
  }

  function INode(node: Node) : BT.G.Node
  requires WFNode(node)
  {
    BT.G.Node(node.pivotTable, node.children, SSTable.ISeq(node.buckets))
  }
  function ICache(cache: map<Reference, Node>) : map<Reference, BT.G.Node>
  requires WFCache(cache)
  {
    map ref | ref in cache :: INode(cache[ref])
  }
  function IIndirectionTable(table: MutIndirectionTable) : (result: BC.IndirectionTable)
    reads table
  {
    var lbas := map k | k in table.Contents && table.Contents[k].0.Some? :: table.Contents[k].0.value;
    var graph := map k | k in table.Contents :: table.Contents[k].1;
    BC.IndirectionTable(lbas, graph)
  }
  function IIndirectionTableOpt(table: Option<MutIndirectionTable>) : (result: Option<BC.IndirectionTable>)
    reads if table.Some? then {table.value} else {}
  {
    if table.Some? then
      Some(IIndirectionTable(table.value))
    else
      None
  }
  function IVars(vars: Variables) : M.Variables
  requires WFVars(vars)
  reads if vars.Ready? then {vars.persistentIndirectionTable, vars.ephemeralIndirectionTable} else {}
  reads if vars.Ready? && vars.frozenIndirectionTable.Some? then {vars.frozenIndirectionTable.value} else {}
  {
    match vars {
      case Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, syncReqs, cache) =>
        BC.Ready(IIndirectionTable(persistentIndirectionTable), IIndirectionTableOpt(frozenIndirectionTable), IIndirectionTable(ephemeralIndirectionTable), outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, syncReqs, ICache(cache))
      case Unready(outstandingIndirectionTableRead, syncReqs) => BC.Unready(outstandingIndirectionTableRead, syncReqs)
    }
  }
  function ISector(sector: Sector) : BC.Sector
  requires WFSector(sector)
  reads if sector.SectorIndirectionTable? then sector.indirectionTable.Repr else {}
  {
    match sector {
      case SectorBlock(node) => BC.SectorBlock(INode(node))
      case SectorIndirectionTable(indirectionTable) => BC.SectorIndirectionTable(IIndirectionTable(indirectionTable))
    }
  }

  class ImplHeapState {
    var s: Variables
    constructor()
    ensures WFVars(s)
    ensures M.Init(BC.Constants(), IVars(s));
    {
      s := Unready(None, map[]);
    }
  }
  function ImplHeapSet(hs: ImplHeapState) : set<object> { {hs} }
}
