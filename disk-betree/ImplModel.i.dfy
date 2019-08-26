include "PivotBetreeSpec.i.dfy"
include "Message.i.dfy"
include "AsyncDiskModel.s.dfy"
include "../lib/Option.s.dfy"
include "KMTable.i.dfy"
include "BetreeBlockCache.i.dfy"
include "../lib/tttree.i.dfy"
include "../lib/NativeTypes.s.dfy"

// This file represents immutability's last stand
// It is the highest-fidelity representation of the implementation
// that can be represented with immutable datatypes

// For example, it has a model of the root bucket which does not exist in BlockCache
// It also represents indirection table as a map to pairs, rather than two maps,
// because real, mutable implementation uses a map to pairs.
// Eventually it will probably have refcounts.

module ImplModel {
  import opened Options
  import opened Sequences
  import opened NativeTypes

  import BT = PivotBetreeSpec`Internal
  import Messages = ValueMessage
  import MS = MapSpec
  import Pivots = PivotsLib
  import BC = BetreeGraphBlockCache
  import BBC = BetreeBlockCache
  import KMTable = KMTable
  import SD = AsyncSectorDisk
  import D = AsyncDisk
  import opened BucketsLib
  import opened BucketWeights
  import opened Bounds
  import UI

  import ReferenceType`Internal

  type Reference = BT.G.Reference
  type Key = MS.Key
  type Message = Messages.Message
  type DiskOp = BBC.DiskOp

  type IndirectionTable = map<uint64, (Option<BC.Location>, seq<Reference>)>

  datatype Node = Node(
      pivotTable: Pivots.PivotTable,
      children: Option<seq<Reference>>,
      buckets: seq<KMTable.KMTable>
    )
  datatype Constants = Constants()
  datatype Variables =
    | Ready(
        persistentIndirectionTable: IndirectionTable, // this lets us keep track of available LBAs
                                                         // TODO replace with something that only tracks LBAs
        frozenIndirectionTable: Option<IndirectionTable>,
        ephemeralIndirectionTable: IndirectionTable,
        outstandingIndirectionTableWrite: Option<BC.ReqId>,
        outstandingBlockWrites: map<SD.ReqId, BC.OutstandingWrite>,
        outstandingBlockReads: map<SD.ReqId, BC.OutstandingRead>,
        syncReqs: map<int, BC.SyncReqStatus>,
        cache: map<Reference, Node>,
        rootBucket: map<Key, Message>)
    | Unready(outstandingIndirectionTableRead: Option<SD.ReqId>, syncReqs: map<int, BC.SyncReqStatus>)
  datatype Sector =
    | SectorBlock(block: Node)
    | SectorIndirectionTable(indirectionTable: IndirectionTable)

  predicate WFBuckets(buckets: seq<KMTable.KMTable>)
  {
    && (forall i | 0 <= i < |buckets| :: KMTable.WF(buckets[i]))
  }
  predicate WFNode(node: Node)
  {
    && WFBuckets(node.buckets)
    && WFBucketList(KMTable.ISeq(node.buckets), node.pivotTable)
    && (node.children.Some? ==> |node.buckets| == |node.children.value|)
    && |node.buckets| <= MaxNumChildren()
    && WeightBucketList(KMTable.ISeq(node.buckets)) <= MaxTotalBucketWeight()
  }
  predicate WFCache(cache: map<Reference, Node>)
  {
    forall ref | ref in cache :: WFNode(cache[ref])
  }

  predicate WFVarsReady(vars: Variables)
  requires vars.Ready?
  {
    var Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, syncReqs, cache, rootBucket) := vars;
    && WFCache(cache)
    && (forall key | key in rootBucket :: rootBucket[key] != Messages.IdentityMessage())
    && (forall key | key in rootBucket :: rootBucket[key] != Messages.IdentityMessage())
    && (rootBucket != map[] ==> BT.G.Root() in cache)
    && (BT.G.Root() in cache ==>
        WeightBucket(rootBucket) + WeightBucketList(KMTable.ISeq(cache[BT.G.Root()].buckets))
          <= MaxTotalBucketWeight())
  }
  predicate WFVars(vars: Variables)
  {
    && (vars.Ready? ==> WFVarsReady(vars))
  }
  predicate WFSector(sector: Sector)
  {
    match sector {
      case SectorBlock(node) => WFNode(node)
      case SectorIndirectionTable(indirectionTable) => (
        && BC.WFCompleteIndirectionTable(IIndirectionTable(indirectionTable))
      )
    }
  }

  function INode(node: Node) : (result: BT.G.Node)
  requires WFBuckets(node.buckets)
  {
    BT.G.Node(node.pivotTable, node.children, KMTable.ISeq(node.buckets))
  }
  function INodeRoot(node: Node, rootBucket: map<Key, Message>) : BT.G.Node
  requires WFBuckets(node.buckets)
  requires Pivots.WFPivots(node.pivotTable)
  requires |node.buckets| == |node.pivotTable| + 1
  {
    BT.G.Node(node.pivotTable, node.children,
      BucketListFlush(rootBucket, KMTable.ISeq(node.buckets), node.pivotTable))
  }
  function INodeForRef(cache: map<Reference, Node>, ref: Reference, rootBucket: map<Key, Message>) : BT.G.Node
  requires WFCache(cache)
  requires ref in cache
  {
    if ref == BT.G.Root() then
      INodeRoot(cache[ref], rootBucket)
    else
      INode(cache[ref])
  }
  function ICache(cache: map<Reference, Node>, rootBucket: map<Key, Message>) : map<Reference, BT.G.Node>
  requires WFCache(cache)
  {
    map ref | ref in cache :: INodeForRef(cache, ref, rootBucket)
  }
  function IIndirectionTableLbas(table: IndirectionTable) : map<uint64, BC.Location>
  {
    map ref | ref in table && table[ref].0.Some? :: table[ref].0.value
  }
  function IIndirectionTableGraph(table: IndirectionTable) : map<uint64, seq<Reference>>
  {
    map ref | ref in table :: table[ref].1
  }
  function IIndirectionTable(table: IndirectionTable) : (result: BC.IndirectionTable)
  {
    var lbas := IIndirectionTableLbas(table);
    var graph := IIndirectionTableGraph(table);
    BC.IndirectionTable(lbas, graph)
  }
  function IIndirectionTableOpt(table: Option<IndirectionTable>) : (result: Option<BC.IndirectionTable>)
  {
    if table.Some? then
      Some(IIndirectionTable(table.value))
    else
      None
  }
  function IVars(vars: Variables) : BBC.Variables
  requires WFVars(vars)
  {
    match vars {
      case Ready(persistentIndirectionTable, frozenIndirectionTable, ephemeralIndirectionTable, outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, syncReqs, cache, rootBucket) =>
        BC.Ready(IIndirectionTable(persistentIndirectionTable), IIndirectionTableOpt(frozenIndirectionTable), IIndirectionTable(ephemeralIndirectionTable), outstandingIndirectionTableWrite, oustandingBlockWrites, outstandingBlockReads, syncReqs, ICache(cache, rootBucket))
      case Unready(outstandingIndirectionTableRead, syncReqs) => BC.Unready(outstandingIndirectionTableRead, syncReqs)
    }
  }
  function ISector(sector: Sector) : BC.Sector
  requires WFSector(sector)
  {
    match sector {
      case SectorBlock(node) => BC.SectorBlock(INode(node))
      case SectorIndirectionTable(indirectionTable) => BC.SectorIndirectionTable(IIndirectionTable(indirectionTable))
    }
  }

  function Ik(k: Constants) : BBC.Constants
  {
    BC.Constants()
  }

  function I(k: Constants, s: Variables) : BBC.Variables
  requires WFVars(s)
  {
    IVars(s)
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && WFVars(s)
    && BBC.Inv(Ik(k), IVars(s))
  }

  // Functional model of the DiskIOHandler

  datatype IO =
    | IOInit(id: uint64)
    | IOReqRead(id: uint64, reqRead: D.ReqRead)
    | IOReqWrite(id: uint64, reqWrite: D.ReqWrite)
    | IORespRead(id: uint64, respRead: D.RespRead)
    | IORespWrite(id: uint64, respWrite: D.RespWrite)

  function diskOp(io: IO) : D.DiskOp {
    match io {
      case IOInit(id) => D.NoDiskOp
      case IOReqRead(id, reqRead) => D.ReqReadOp(id, reqRead)
      case IOReqWrite(id, reqWrite) => D.ReqWriteOp(id, reqWrite)
      case IORespRead(id, respRead) => D.RespReadOp(id, respRead)
      case IORespWrite(id, respWrite) => D.RespWriteOp(id, respWrite)
    }
  }
}
