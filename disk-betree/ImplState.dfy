include "PivotBetreeSpec.dfy"
include "Message.dfy"
include "../lib/Option.dfy"
include "BetreeBlockCache.dfy"
include "KMTable.dfy"
include "../lib/tttree.dfy"

module {:extern} ImplState {
  import opened Options
  import opened Sequences
  import TTT = TwoThreeTree

  import BT = PivotBetreeSpec`Internal
  import Messages = ValueMessage
  import MS = MapSpec
  import Pivots = PivotsLib
  import BC = BetreeGraphBlockCache
  import M = BetreeBlockCache
  import KMTable = KMTable
  import D = AsyncSectorDisk
  import opened BucketsLib

  type Reference = BT.G.Reference
  type Key = MS.Key
  type Message = Messages.Message
  type TreeMap = TTT.Tree<Message>

  datatype Node = Node(
      pivotTable: Pivots.PivotTable,
      children: Option<seq<Reference>>,
      buckets: seq<KMTable.KMTable>
    )
  datatype Variables =
    | Ready(
        persistentIndirectionTable: BC.IndirectionTable,
        frozenIndirectionTable: Option<BC.IndirectionTable>,
        ephemeralIndirectionTable: BC.IndirectionTable,
        outstandingIndirectionTableWrite: Option<BC.ReqId>,
        outstandingBlockWrites: map<D.ReqId, BC.OutstandingWrite>,
        outstandingBlockReads: map<D.ReqId, BC.OutstandingRead>,
        syncReqs: map<int, BC.SyncReqStatus>,
        cache: map<Reference, Node>,
        rootBucket: TreeMap)
    | Unready(outstandingIndirectionTableRead: Option<D.ReqId>, syncReqs: map<int, BC.SyncReqStatus>)
  datatype Sector =
    | SectorBlock(block: Node)
    | SectorIndirectionTable(indirectionTable: BC.IndirectionTable)

  predicate WFBuckets(buckets: seq<KMTable.KMTable>)
  {
    && (forall i | 0 <= i < |buckets| :: KMTable.WF(buckets[i]))
    && (forall i | 0 <= i < |buckets| :: KMTable.Bounded(buckets[i]))
  }
  predicate WFNode(node: Node)
  {
    && WFBuckets(node.buckets)
    && WFBucketList(KMTable.ISeq(node.buckets), node.pivotTable)
  }
  predicate WFCache(cache: map<Reference, Node>)
  {
    forall ref | ref in cache :: WFNode(cache[ref])
  }
  predicate WFVars(vars: Variables)
  {
    match vars {
      case Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, syncReqs, cache, rootBucket) => (
        && WFCache(cache)
        && TTT.TTTree(rootBucket)
        && (forall key | key in TTT.I(rootBucket) :: TTT.I(rootBucket)[key] != Messages.IdentityMessage())
        && (rootBucket != TTT.EmptyTree ==> BT.G.Root() in cache)
      )
      case Unready(outstandingIndirectionTableRead, syncReqs) => true
    }
  }
  predicate WFSector(sector: Sector)
  {
    match sector {
      case SectorBlock(node) => WFNode(node)
      case SectorIndirectionTable(indirectionTable) => BC.WFCompleteIndirectionTable(indirectionTable)
    }
  }

  function INode(node: Node) : BT.G.Node
  requires WFBuckets(node.buckets)
  {
    BT.G.Node(node.pivotTable, node.children, KMTable.ISeq(node.buckets))
  }
  function INodeRoot(node: Node, rootBucket: TreeMap) : BT.G.Node
  requires WFNode(node)
  requires TTT.TTTree(rootBucket)
  {
    BT.G.Node(node.pivotTable, node.children,
      BucketListFlush(TTT.I(rootBucket), KMTable.ISeq(node.buckets), node.pivotTable))
  }
  function INodeForRef(cache: map<Reference, Node>, ref: Reference, rootBucket: TreeMap) : BT.G.Node
  requires WFCache(cache)
  requires ref in cache
  requires TTT.TTTree(rootBucket)
  {
    if ref == BT.G.Root() then
      INodeRoot(cache[ref], rootBucket)
    else
      INode(cache[ref])
  }
  function ICache(cache: map<Reference, Node>, rootBucket: TreeMap) : map<Reference, BT.G.Node>
  requires WFCache(cache)
  requires TTT.TTTree(rootBucket)
  {
    map ref | ref in cache :: INodeForRef(cache, ref, rootBucket)
  }
  function IVars(vars: Variables) : M.Variables
  requires WFVars(vars)
  {
    match vars {
      case Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, syncReqs, cache, rootBucket) =>
        BC.Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, syncReqs, ICache(cache, rootBucket))
      case Unready(outstandingIndirectionTableRead, syncReqs) => BC.Unready(outstandingIndirectionTableRead, syncReqs)
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
      s := Unready(None, map[]);
    }
  }
  function ImplHeapSet(hs: ImplHeapState) : set<object> { {hs} }
}
