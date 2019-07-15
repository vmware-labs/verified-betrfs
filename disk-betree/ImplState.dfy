include "PivotBetreeSpec.dfy"
include "Message.dfy"
include "../lib/Option.dfy"
include "SSTable.dfy"
include "BetreeBlockCache.dfy"

module ImplState {
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
        persistentSuperblock: BC.Superblock,
        ephemeralSuperblock: BC.Superblock,
        cache: map<Reference, Node>)
    | Unready
  datatype Sector =
    | SectorBlock(block: Node)
    | SectorSuperblock(superblock: BC.Superblock)

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
      case Ready(persistentSuperblock, ephemeralSuperblock, cache) => WFCache(cache)
      case Unready => true
    }
  }
  predicate WFSector(sector: Sector)
  {
    match sector {
      case SectorBlock(node) => WFNode(node)
      case SectorSuperblock(superblock) => BC.WFPersistentSuperblock(superblock)
    }
  }

  function IBuckets(buckets: seq<SSTable.SSTable>) : seq<map<Key, Message>>
  requires WFBuckets(buckets)
  {
    if |buckets| == 0 then [] else IBuckets(DropLast(buckets)) + [SSTable.I(Last(buckets))]
  }
  function INode(node: Node) : BT.G.Node
  requires WFNode(node)
  {
    BT.G.Node(node.pivotTable, node.children, IBuckets(node.buckets))
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
      case Ready(persistentSuperblock, ephemeralSuperblock, cache) =>
        BC.Ready(persistentSuperblock, ephemeralSuperblock, ICache(cache))
      case Unready => BC.Unready
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
  type HeapState = ImplHeapState
  function HeapSet(hs: HeapState) : set<object> { {hs} }

  
}
