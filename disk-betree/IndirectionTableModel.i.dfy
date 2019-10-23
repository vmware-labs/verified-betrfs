include "../lib/Maps.s.dfy"
include "../lib/sequences.s.dfy"
include "../lib/Option.s.dfy"
include "../lib/NativeTypes.s.dfy"
include "../lib/LRU.i.dfy"
include "../lib/MutableMapModel.i.dfy"
include "PivotBetreeSpec.i.dfy"
include "AsyncSectorDiskModel.i.dfy"
include "BlockCacheSystem.i.dfy"
include "../lib/Marshalling/GenericMarshalling.i.dfy"

module IndirectionTableModel {
  import opened Maps
  import opened Options
  import opened Sequences
  import opened NativeTypes
  import ReferenceType`Internal
  import BT = PivotBetreeSpec`Internal
  import BC = BetreeGraphBlockCache
  import LruModel
  import MutableMapModel
  import LBAType
  import opened GenericMarshalling

  datatype Entry = Entry(loc: Option<BC.Location>, succs: seq<BT.G.Reference>)
  type HashMap = MutableMapModel.LinearHashMap<Entry>

  datatype IndirectionTable = IndirectionTable(
    t: HashMap,
    locs: map<BT.G.Reference, BC.Location>,
    graph: map<BT.G.Reference, seq<BT.G.Reference>>
  )

    // This contains reference with the empty predecessor set.
    // We use a LRU queue not because we care about the LRU,
    // but just because it happens to be a queue data structure lying around.
    //garbageQueue: LruModel.LruQueue,
    //refcounts: map<BT.G.Reference, uint64>)

  function Locs(t: HashMap) : map<BT.G.Reference, BC.Location>
  {
    map ref | ref in t.contents && t.contents[ref].loc.Some? :: t.contents[ref].loc.value
  }

  function Graph(t: HashMap) : map<BT.G.Reference, seq<BT.G.Reference>>
  {
    map ref | ref in t.contents :: t.contents[ref].succs
  }

  /*datatype PredecessorEdge = PredecessorEdge(src: BT.G.Reference, idx: int)

  function PredecessorSet(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference) : set<PredecessorEdge>
  {
    set src, idx | src in graph && 0 <= idx < graph[src] :: PredecessorEdge(src, idx)
  }

  function GraphRefcounts(graph: map<BT.G.Reference, seq<BT.G.Reference>>) : map<BT.G.Reference, uint64>
  {
    map ref | ref in graph :: |PredecessorSet(graph, ref)|
  }

  predicate Refcount0(self: IndirectionTable, ref: BT.G.Reference)
  {
    && ref in refcounts
    && refcounts[ref] == 0
  }
  */

  protected predicate Inv(self: IndirectionTable)
  {
    //&& (forall ref | ref in LruModel.I(self.garbageQueue) :: Refcount0(self, ref))
    //&& (forall ref | Refcount0(self, ref) :: ref in LruModel.I(self.garbageQueue))
    //&& self.refcounts == GraphRefcounts(self.graph)
    && MutableMapModel.Inv(self.t)
    && self.locs == Locs(self.t)
    && self.graph == Graph(self.t)
  }

  function I(self: IndirectionTable) : BC.IndirectionTable
  {
    BC.IndirectionTable(self.locs, self.graph)
  }

  function {:opaque} RemoveLocIfPresent(self: IndirectionTable, ref: BT.G.Reference) : (self' : IndirectionTable)
  requires Inv(self)
  ensures Inv(self')
  ensures self'.locs == MapRemove1(self.locs, ref)
  ensures self'.graph == self.graph
  {
    assume self.t.count as nat < 0x10000000000000000 / 8;
    var oldEntry := MutableMapModel.Get(self.t, ref);
    var t := (if oldEntry.Some? then
      MutableMapModel.Insert(self.t, ref, Entry(None, oldEntry.value.succs))
    else
      self.t);
    IndirectionTable(t, Locs(t), Graph(t))
  }

  function {:opaque} AddLocIfPresent(self: IndirectionTable, ref: BT.G.Reference, loc: BC.Location) : (self' : IndirectionTable)
  requires Inv(self)
  ensures Inv(self')
  ensures self'.graph == self.graph
  ensures ref in self.graph ==> self'.locs == self.locs[ref := loc]
  ensures ref !in self.graph ==> self'.locs == self.locs
  {
    assume self.t.count as nat < 0x10000000000000000 / 8;
    var oldEntry := MutableMapModel.Get(self.t, ref);
    var t := (if oldEntry.Some? then
      MutableMapModel.Insert(self.t, ref, Entry(Some(loc), oldEntry.value.succs))
    else
      self.t);
    IndirectionTable(t, Locs(t), Graph(t))
  }

  /*function updateRefcountsInc(garbageQueue: LruModel.LruQueue, refcounts: map<BT.G.Reference, uint64>, oldChildren: seq<BT.G.Reference, uint64>, newChildren: seq<BT.G.Reference>, idx: uint64)
  requires 0 <= idx <= |newChildren|
  {
    if idx ==
  }*/

  function {:opaque} UpdateAndRemoveLoc(self: IndirectionTable, ref: BT.G.Reference, succs: seq<BT.G.Reference>) : (self' : IndirectionTable)
  requires Inv(self)
  ensures Inv(self')
  ensures self'.locs == MapRemove1(self.locs, ref)
  ensures self'.graph == self.graph[ref := succs]
  {
    assume self.t.count as nat < 0x10000000000000000 / 8;
    var t := MutableMapModel.Insert(self.t, ref, Entry(None, succs));
    IndirectionTable(t, Locs(t), Graph(t))
  }

  function {:fuel ValInGrammar,3} valToHashMap(a: seq<V>) : (s : Option<HashMap>)
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GTuple([GUint64, GUint64, GUint64, GUint64Array]))
  ensures s.Some? ==> forall v | v in s.value.contents.Values :: v.loc.Some? && BC.ValidLocationForNode(v.loc.value)
  {
    if |a| == 0 then
      Some(MutableMapModel.Constructor(1024))
    else (
      var res := valToHashMap(DropLast(a));
      match res {
        case Some(table) => (
          var tuple := Last(a);
          var ref := tuple.t[0].u;
          var lba := tuple.t[1].u;
          var len := tuple.t[2].u;
          var succs := Some(tuple.t[3].ua);
          match succs {
            case None => None
            case Some(succs) => (
              var loc := LBAType.Location(lba, len);
              if ref in table.contents || lba == 0 || !LBAType.ValidLocation(loc) then (
                None
              ) else (
                assume table.count as nat < 0x10000000000000000 / 8;
                Some(MutableMapModel.Insert(table, ref, Entry(Some(loc), succs)))
              )
            )
          }
        )
        case None => None
      }
    )
  }

  function method IndirectionTableGrammar() : G
  ensures ValidGrammar(IndirectionTableGrammar())
  {
    // (Reference, address, len, successor-list) triples
    GArray(GTuple([GUint64, GUint64, GUint64, GUint64Array]))
  }

  function valToIndirectionTable(v: V) : (s : Option<IndirectionTable>)
  requires ValInGrammar(v, IndirectionTableGrammar())
  ensures s.Some? ==> Inv(s.value)
  ensures s.Some? ==> BC.WFCompleteIndirectionTable(I(s.value))
  {
    var t := valToHashMap(v.a);
    match t {
      case Some(t) => (
        var res := IndirectionTable(t, Locs(t), Graph(t));
        if BT.G.Root() in res.graph && BC.GraphClosed(res.graph) then (
          Some(res)
        ) else (
          None
        )
      )
      case None => None
    }
  }
}
