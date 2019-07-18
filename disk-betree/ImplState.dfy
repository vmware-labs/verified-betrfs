include "PivotBetreeSpec.dfy"
include "Message.dfy"
include "../lib/Option.dfy"
include "SSTable.dfy"
include "BetreeBlockCache.dfy"

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

  type Reference = BT.G.Reference
  type Key = MS.Key
  type Message = Messages.Message

  datatype Node = Node(
      pivotTable: Pivots.PivotTable,
      children: Option<seq<Reference>>,
      buckets: seq<SSTable.SSTable>
    )
  datatype Variables =
    | Ready(
        persistentIndirectionTable: BC.IndirectionTable,
        ephemeralIndirectionTable: BC.IndirectionTable,
        cache: map<Reference, Node>)
    | Unready
  datatype Sector =
    | SectorBlock(block: Node)
    | SectorIndirectionTable(indirectionTable: BC.IndirectionTable)

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
      case Ready(persistentIndirectionTable, ephemeralIndirectionTable, cache) => WFCache(cache)
      case Unready => true
    }
  }
  predicate WFSector(sector: Sector)
  {
    match sector {
      case SectorBlock(node) => WFNode(node)
      case SectorIndirectionTable(indirectionTable) => BC.WFPersistentIndirectionTable(indirectionTable)
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
  function IVars(vars: Variables) : M.Variables
  requires WFVars(vars)
  {
    match vars {
      case Ready(persistentIndirectionTable, ephemeralIndirectionTable, cache) =>
        BC.Ready(persistentIndirectionTable, ephemeralIndirectionTable, ICache(cache))
      case Unready => BC.Unready
    }
  }
  function ISector(sector: Sector) : BC.Sector
  requires WFSector(sector)
  {
    match sector {
      case SectorBlock(node) => BC.SectorBlock(INode(node))
      case SectorIndirectionTable(indirectionTable) => BC.SectorIndirectionTable(indirectionTable)
    }
  }

  class ImplHeapState {
    var s: Variables
    constructor()
    ensures WFVars(s)
    ensures M.Init(BC.Constants(), IVars(s));
    {
      s := Unready;
    }
  }
  function ImplHeapSet(hs: ImplHeapState) : set<object> { {hs} }
}
