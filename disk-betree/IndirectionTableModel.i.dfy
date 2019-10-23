module IndirectionTableModel {
  import opened Maps
  import opened Options
  import opened NativeTypes
  import BT = PivotBetreeSpec`Internal
  import LBAType
  import LruModel

  datatype IndirectionTable = IndirectionTable(
    locs: map<BT.G.Reference, LBAType.Location>,
    graph: map<BT.G.Reference, seq<BT.G.Reference>,

    // This contains reference with the empty predecessor set.
    // We use a LRU queue not because we care about the LRU,
    // but just because it happens to be a queue data structure lying around.
    garbageQueue: LruModel.LruQueue,
    refcounts: map<BT.G.Reference, uint64>)

  datatype PredecessorEdge = PredecessorEdge(src: BT.G.Reference, idx: int)

  function PredecessorSet(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference) : set<PredecessorEdge>
  {
    set src, idx | src in graph && 0 <= idx < graph[src] :: PredecessorEdge(src, idx)
  }

  function GraphRefcounts(graph: map<BT.G.Reference, seq<BT.G.Reference>>) : map<BT.G.Reference, uint64>
  {
    map ref | ref in graph :: |PredecessorSet(graph, ref)|
  }

  predicate Refcount0(table: IndirectionTable, ref: BT.G.Reference)
  {
    && ref in refcounts
    && refcounts[ref] == 0
  }

  protected predicate Inv(table: IndirectionTable)
  {
    && (forall ref | ref in LruModel.I(table.garbageQueue) :: Refcount0(table, ref))
    && (forall ref | Refcount0(table, ref) :: ref in LruModel.I(table.garbageQueue))
    && table.refcounts == GraphRefcounts(table.graph)
  }

  function RemoveLoc(table: IndirectionTable, ref: BT.G.Reference)
  {
    IndirectionTable(
      MapRemove1(table.locs, ref),
      table.graph,
      table.garbageQueue,
      table.refcounts)
  }

  function AddLoc(table: IndirectionTable, ref: BT.G.Reference, loc: LBAType.Location)
  {
    IndirectionTable(
      table.locs[ref := loc],
      table.graph,
      table.garbageQueue,
      table.refcounts)
  }

  function updateRefcountsInc(garbageQueue: LruModel.LruQueue, refcounts: map<BT.G.Reference, uint64>, oldChildren: seq<BT.G.Reference, uint64>, newChildren: seq<BT.G.Reference>, idx: uint64)
  requires 0 <= idx <= |newChildren|
  {
    if idx ==
  }

  function UpdateAndRemoveLoc(table: IndirectionTable, ref: BT.G.Reference, children: seq<BT.G.Reference>)
  {
    var (gq, rc) := updateRefcountsInc(table.garbageQueue, table.refcounts,
        table.locs[ref], children, 0);
    IndirectionTable(
      MapRemove1(table.locs, ref),
      table.locs[ref := children],
      gq,
      rc)
  }
}
