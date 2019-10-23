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
include "../lib/Bitmap.i.dfy"

module IndirectionTableModel {
  import opened Maps
  import opened Sets
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
  import Bitmap
  import opened Bounds

  datatype Entry = Entry(loc: Option<BC.Location>, succs: seq<BT.G.Reference>)
  type HashMap = MutableMapModel.LinearHashMap<Entry>

  // TODO move bitmap in here?
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
  ensures Inv(self) ==> (forall ref | ref in self.locs :: ref in self.graph)
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

  function {:opaque} GetEntry(self: IndirectionTable, ref: BT.G.Reference) : (e : Option<Entry>)
  requires Inv(self)
  ensures e.None? ==> ref !in self.graph
  ensures e.Some? ==> ref in self.graph
  ensures e.Some? ==> self.graph[ref] == e.value.succs
  ensures e.Some? && e.value.loc.Some? ==>
      ref in self.locs && self.locs[ref] == e.value.loc.value
  ensures ref in self.locs ==> e.Some? && e.value.loc.Some?
  {
    MutableMapModel.Get(self.t, ref)
  }

  predicate {:opaque} HasEmptyLoc(self: IndirectionTable, ref: BT.G.Reference)
  requires Inv(self)
  ensures HasEmptyLoc(self, ref) == (ref in self.graph && ref !in self.locs)
  {
    var entry := MutableMapModel.Get(self.t, ref);
    entry.Some? && entry.value.loc.None?
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

  function {:opaque} AddLocIfPresent(self: IndirectionTable, ref: BT.G.Reference, loc: BC.Location) : (IndirectionTable, bool)
  requires Inv(self)
  ensures var (self', added) := AddLocIfPresent(self, ref, loc);
    && Inv(self')
    && added == (ref in self.graph && ref !in self.locs)
    && self'.graph == self.graph
    && (added ==> self'.locs == self.locs[ref := loc])
    && (!added ==> self'.locs == self.locs)
  {
    assume self.t.count as nat < 0x10000000000000000 / 8;
    var oldEntry := MutableMapModel.Get(self.t, ref);
    var added := oldEntry.Some? && oldEntry.value.loc.None?;
    var t := (if added then
      MutableMapModel.Insert(self.t, ref, Entry(Some(loc), oldEntry.value.succs))
    else
      self.t);
    (IndirectionTable(t, Locs(t), Graph(t)), added)
  }

  function {:opaque} RemoveRef(self: IndirectionTable, ref: BT.G.Reference)
    : (res : (IndirectionTable, Option<BC.Location>))
  requires Inv(self)
  ensures var (self', oldLoc) := res;
    && Inv(self')
    && self'.graph == MapRemove1(self.graph, ref)
    && self'.locs == MapRemove1(self.locs, ref)
    && (ref in self.locs ==> oldLoc == Some(self.locs[ref]))
    && (ref !in self.locs ==> oldLoc == None)
  {
    var (t, oldEntry) := MutableMapModel.RemoveAndGet(self.t, ref);
    var self' := IndirectionTable(t, Locs(t), Graph(t));
    var oldLoc := if oldEntry.Some? then oldEntry.value.loc else None;
    (self', oldLoc)
  }

  /*function updateRefcountsInc(garbageQueue: LruModel.LruQueue, refcounts: map<BT.G.Reference, uint64>, oldChildren: seq<BT.G.Reference, uint64>, newChildren: seq<BT.G.Reference>, idx: uint64)
  requires 0 <= idx <= |newChildren|
  {
    if idx ==
  }*/

  function {:opaque} UpdateAndRemoveLoc(self: IndirectionTable, ref: BT.G.Reference, succs: seq<BT.G.Reference>) : (res : (IndirectionTable, Option<BC.Location>))
  requires Inv(self)
  ensures var (self', oldLoc) := res;
    && Inv(self')
    && self'.locs == MapRemove1(self.locs, ref)
    && self'.graph == self.graph[ref := succs]
    && (oldLoc.None? ==> ref !in self.locs)
    && (oldLoc.Some? ==> ref in self.locs && self.locs[ref] == oldLoc.value)
  {
    assume self.t.count as nat < 0x10000000000000000 / 8;
    var (t, oldEntry) := MutableMapModel.InsertAndGetOld(self.t, ref, Entry(None, succs));
    var self' := IndirectionTable(t, Locs(t), Graph(t));
    var oldLoc := if oldEntry.Some? && oldEntry.value.loc.Some? then oldEntry.value.loc else None;
    (self', oldLoc)
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

  // To bitmap

  predicate IsLocAllocIndirectionTable(indirectionTable: IndirectionTable, i: int)
  {
    || i == 0 // block 0 is always implicitly allocated
    || !(
      forall ref | ref in indirectionTable.locs ::
        indirectionTable.locs[ref].addr as int != i * BlockSize() as int
    )
  }

  predicate IsLocAllocBitmap(bm: Bitmap.BitmapModel, i: int)
  {
    && 0 <= i < Bitmap.Len(bm)
    && Bitmap.IsSet(bm, i)
  }

  function InitLocBitmapIterate(indirectionTable: IndirectionTable,
      it: MutableMapModel.Iterator<Entry>,
      bm: Bitmap.BitmapModel)
  : (res : (bool, Bitmap.BitmapModel))
  requires Inv(indirectionTable)
  requires MutableMapModel.WFIter(indirectionTable.t, it)
  requires BC.WFCompleteIndirectionTable(I(indirectionTable))
  requires Bitmap.Len(bm) == NumBlocks()
  ensures Bitmap.Len(res.1) == NumBlocks()
  decreases it.decreaser
  {
    if it.next.None? then (
      (true, bm)
    ) else (
      var kv := it.next.value;
      assert kv.0 in I(indirectionTable).locs;

      var loc: uint64 := kv.1.loc.value.addr;
      var locIndex: uint64 := loc / BlockSize() as uint64;
      if locIndex < NumBlocks() as uint64 && !Bitmap.IsSet(bm, locIndex as int) then (
        InitLocBitmapIterate(indirectionTable,
            MutableMapModel.IterInc(indirectionTable.t, it),
            Bitmap.BitSet(bm, locIndex as int))
      ) else (
        (false, bm)
      )
    )
  }

  function {:opaque} InitLocBitmap(indirectionTable: IndirectionTable) : (res : (bool, Bitmap.BitmapModel))
  requires Inv(indirectionTable)
  requires BC.WFCompleteIndirectionTable(I(indirectionTable))
  ensures Bitmap.Len(res.1) == NumBlocks()
  {
    var bm := Bitmap.EmptyBitmap(NumBlocks());
    var bm' := Bitmap.BitSet(bm, 0);
    InitLocBitmapIterate(indirectionTable,
        MutableMapModel.IterStart(indirectionTable.t),
        bm')
  }

  predicate IsLocAllocIndirectionTablePartial(indirectionTable: IndirectionTable, i: int, s: set<uint64>)
  {
    || i == 0 // block 0 is always implicitly allocated
    || !(
      forall ref | ref in indirectionTable.locs && ref in s ::
        indirectionTable.locs[ref].addr as int != i * BlockSize() as int
    )
  }

  lemma InitLocBitmapIterateCorrect(indirectionTable: IndirectionTable,
      it: MutableMapModel.Iterator<Entry>,
      bm: Bitmap.BitmapModel)
  requires Inv(indirectionTable)
  requires InitLocBitmapIterate.requires(indirectionTable, it, bm);
  requires (forall i: int ::
        (IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s)) <==> IsLocAllocBitmap(bm, i)
      )
  requires 
    forall r1, r2 | r1 in I(indirectionTable).locs && r2 in I(indirectionTable).locs ::
        r1 in it.s && r2 in it.s ==>
        BC.LocationsForDifferentRefsDontOverlap(I(indirectionTable), r1, r2)
  ensures var (succ, bm') := InitLocBitmapIterate(indirectionTable, it, bm);
    (succ ==>
      && (forall i: int ::
        (IsLocAllocIndirectionTable(indirectionTable, i)
        <==> IsLocAllocBitmap(bm', i)
      ))
      && BC.AllLocationsForDifferentRefsDontOverlap(I(indirectionTable))
    )
  decreases it.decreaser
  {
    Bitmap.reveal_BitSet();
    Bitmap.reveal_IsSet();

    var (succ, bm') := InitLocBitmapIterate(indirectionTable, it, bm);
    if it.next.None? {
      forall i: int | IsLocAllocIndirectionTable(indirectionTable, i)
      ensures IsLocAllocBitmap(bm', i)
      {
      }

      forall i: int
      | IsLocAllocBitmap(bm', i)
      ensures IsLocAllocIndirectionTable(indirectionTable, i)
      {
      }
    } else {
      if (succ) {
        var kv := it.next.value;
        assert kv.0 in indirectionTable.locs;
        var loc: uint64 := kv.1.loc.value.addr;
        var locIndex: uint64 := loc / BlockSize() as uint64;

        //assert I(indirectionTable).locs[kv.0] == kv.1.0.value;
        LBAType.reveal_ValidAddr();
        assert BC.ValidLocationForNode(kv.1.loc.value);
        assert locIndex as int * BlockSize() == loc as int;

        //assert locIndex < NumBlocks() as uint64;
        //assert !Bitmap.IsSet(bm, locIndex as int);

        var bm0 := Bitmap.BitSet(bm, locIndex as int);
        var it0 := MutableMapModel.IterInc(indirectionTable.t, it);

        forall i: int
        | IsLocAllocIndirectionTablePartial(indirectionTable, i, it0.s)
        ensures IsLocAllocBitmap(bm0, i)
        {
          // This triggers all the right stuff:
          if IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s) { }
          /*
          if i != 0 {
            var ref :| ref in indirectionTable.contents && indirectionTable.contents[ref].0.Some? && ref in it0.s && indirectionTable.contents[ref].0.value.addr as int == i * BlockSize() as int;
            if (ref == kv.0) {
              assert IsLocAllocBitmap(bm0, i);
            } else {
              assert IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s);
              assert IsLocAllocBitmap(bm0, i);
            }
          } else {
            assert IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s);
          }
          */
        }

        forall i: int
        | IsLocAllocBitmap(bm0, i)
        ensures IsLocAllocIndirectionTablePartial(indirectionTable, i, it0.s)
        {
          if IsLocAllocBitmap(bm, i) { }
          if IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s) { }

          if i == locIndex as int {
            var ref := kv.0;
            assert indirectionTable.t.contents[ref].loc.Some?;
            assert ref in it0.s;
            assert indirectionTable.t.contents[ref] == kv.1;
            assert indirectionTable.t.contents[ref].loc.value.addr as int == i * BlockSize() as int;

            assert IsLocAllocIndirectionTablePartial(indirectionTable, i, it0.s);
          } else {
            assert IsLocAllocIndirectionTablePartial(indirectionTable, i, it0.s);
          }
        }

        forall r1, r2 | r1 in I(indirectionTable).locs && r2 in I(indirectionTable).locs && r1 in it0.s && r2 in it0.s
        ensures BC.LocationsForDifferentRefsDontOverlap(I(indirectionTable), r1, r2)
        {
          if r1 != r2 {
            if r1 in it.s && r2 in it.s {
              assert BC.LocationsForDifferentRefsDontOverlap(I(indirectionTable), r1, r2);
            } else {
              if I(indirectionTable).locs[r1].addr == I(indirectionTable).locs[r2].addr {
                var j1 := LBAType.ValidAddrDivisor(I(indirectionTable).locs[r1].addr);
                var j2 := LBAType.ValidAddrDivisor(I(indirectionTable).locs[r2].addr);
                if r1 !in it.s {
                  assert r2 in it.s;
                  assert !Bitmap.IsSet(bm, j1);
                  assert IsLocAllocBitmap(bm, j2);
                  assert Bitmap.IsSet(bm, j2);
                  assert false;
                } else {
                  assert r1 in it.s;
                  assert !Bitmap.IsSet(bm, j2);
                  assert IsLocAllocBitmap(bm, j1);
                  assert Bitmap.IsSet(bm, j1);
                  assert false;
                }
              } else {
                assert BC.LocationsForDifferentRefsDontOverlap(I(indirectionTable), r1, r2);
              }
            }
          }
        }

        InitLocBitmapIterateCorrect(indirectionTable, it0, bm0);
        assert (succ, bm') == InitLocBitmapIterate(indirectionTable, it0, bm0);
      }
    }
  }

  lemma InitLocBitmapCorrect(indirectionTable: IndirectionTable)
  requires Inv(indirectionTable)
  requires BC.WFCompleteIndirectionTable(I(indirectionTable))
  ensures var (succ, bm) := InitLocBitmap(indirectionTable);
    (succ ==>
      && (forall i: int :: IsLocAllocIndirectionTable(indirectionTable, i)
        <==> IsLocAllocBitmap(bm, i)
      )
      && BC.AllLocationsForDifferentRefsDontOverlap(I(indirectionTable))
    )
  {
    reveal_InitLocBitmap();
    Bitmap.reveal_BitSet();
    Bitmap.reveal_IsSet();

    var it := MutableMapModel.IterStart(indirectionTable.t);

    var bm := Bitmap.EmptyBitmap(NumBlocks());
    var bm' := Bitmap.BitSet(bm, 0);

    /*forall i: int | IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s)
    ensures IsLocAllocBitmap(bm', i)
    {
      assert i == 0;
    }*/

    forall i: int | IsLocAllocBitmap(bm', i)
    ensures IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s)
    {
      if i != 0 {
        assert Bitmap.IsSet(bm', i)
            == Bitmap.IsSet(bm, i)
            == false;
      }
      assert i == 0;
    }

    InitLocBitmapIterateCorrect(indirectionTable, it, bm');
  }

  ///// Dealloc stuff

  predicate deallocable(self: IndirectionTable, ref: BT.G.Reference)
  {
    && ref in I(self).graph
    && ref != BT.G.Root()
    && (forall r | r in I(self).graph :: ref !in I(self).graph[r])
  }

  function FindDeallocableIterate(self: IndirectionTable, ephemeralRefs: seq<BT.G.Reference>, i: uint64)
  : (ref: Option<BT.G.Reference>)
  requires 0 <= i as int <= |ephemeralRefs|
  requires |ephemeralRefs| < 0x1_0000_0000_0000_0000;
  decreases 0x1_0000_0000_0000_0000 - i as int
  {
    if i == |ephemeralRefs| as uint64 then (
      None
    ) else (
      var ref := ephemeralRefs[i];
      var isDeallocable := deallocable(self, ref);
      if isDeallocable then (
        Some(ref)
      ) else (
        FindDeallocableIterate(self, ephemeralRefs, i + 1)
      )
    )
  }

  function {:opaque} FindDeallocable(self: IndirectionTable)
  : (ref: Option<BT.G.Reference>)
  requires Inv(self)
  {
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var ephemeralRefs := setToSeq(self.t.contents.Keys);

    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;

    FindDeallocableIterate(self, ephemeralRefs, 0)
  }

  lemma FindDeallocableIterateCorrect(self: IndirectionTable, ephemeralRefs: seq<BT.G.Reference>, i: uint64)
  requires Inv(self)
  requires 0 <= i as int <= |ephemeralRefs|
  requires |ephemeralRefs| < 0x1_0000_0000_0000_0000;
  requires ephemeralRefs == setToSeq(self.t.contents.Keys)
  requires forall k : nat | k < i as nat :: (
        && ephemeralRefs[k] in I(self).graph
        && !deallocable(self, ephemeralRefs[k]))
  ensures var ref := FindDeallocableIterate(self, ephemeralRefs, i);
      && (ref.Some? ==> ref.value in I(self).graph)
      && (ref.Some? ==> deallocable(self, ref.value))
      && (ref.None? ==> forall r | r in I(self).graph :: !deallocable(self, r))
  decreases 0x1_0000_0000_0000_0000 - i as int
  {
    if i == |ephemeralRefs| as uint64 {
      assert forall r | r in I(self).graph :: !deallocable(self, r);
    } else {
      var ref := ephemeralRefs[i];
      var isDeallocable := deallocable(self, ref);
      if isDeallocable {
      } else {
        FindDeallocableIterateCorrect(self, ephemeralRefs, i + 1);
      }
    }
  }

  lemma FindDeallocableCorrect(self: IndirectionTable)
  requires Inv(self)
  ensures var ref := FindDeallocable(self);
      && (ref.Some? ==> ref.value in I(self).graph)
      && (ref.Some? ==> deallocable(self, ref.value))
      && (ref.None? ==> forall r | r in I(self).graph :: !deallocable(self, r))
  {
    reveal_FindDeallocable();
    var ephemeralRefs := setToSeq(self.t.contents.Keys);
    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;
    FindDeallocableIterateCorrect(self, ephemeralRefs, 0);
  }
}
