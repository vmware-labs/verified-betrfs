include "../lib/Base/Maps.s.dfy"
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/NativeTypes.s.dfy"
include "../lib/DataStructures/LruModel.i.dfy"
include "../lib/DataStructures/MutableMapModel.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "../lib/DataStructures/BitmapModel.i.dfy"
include "../ByteBlockCacheSystem/Marshalling.i.dfy"

//
// An IndirectionTable maps references to locations and tracks
// dependencies (accounts for locations containing references).
// This module includes a reference-counting map and free list
// that make discovering free blocks (and maintaining the list of
// them) cheap.
// 
// TODO(thance): separate API from refcount-y implementation using
// a layer of Dafny refinement.
//
// TODO(jonh): Here "Model" means "lowest functional model of the mutable
// impl". Maybe move Model to the beginning of all such usages?
//

module IndirectionTableModel {
  import opened Maps
  import opened Sets
  import opened Options
  import opened Sequences
  import opened NativeTypes
  import ReferenceType`Internal
  import BT = PivotBetreeSpec`Internal
  import BC = BlockCache
  import LruModel
  import MutableMapModel
  import SectorType
  import opened DiskLayout
  import opened GenericMarshalling
  import BitmapModel
  import opened Bounds
  import SetBijectivity
  import Marshalling

  datatype Entry = Entry(loc: Option<Location>, succs: seq<BT.G.Reference>, predCount: uint64)
  type HashMap = MutableMapModel.LinearHashMap<Entry>

  // TODO move bitmap in here?
  datatype IndirectionTable = IndirectionTable(
    t: HashMap,
    garbageQueue: Option<LruModel.LruQueue>,
    refUpperBound: uint64,
    findLoclessIterator: Option<MutableMapModel.SimpleIterator>,

    // These are for easy access in proof code, but all the relevant data
    // is contained in the `t: HashMap` field.
    ghost locs: map<BT.G.Reference, Location>,
    ghost graph: map<BT.G.Reference, seq<BT.G.Reference>>,
    ghost predCounts: map<BT.G.Reference, int>
  )

  function Locs(t: HashMap) : map<BT.G.Reference, Location>
  {
    map ref | ref in t.contents && t.contents[ref].loc.Some? :: t.contents[ref].loc.value
  }

  function Graph(t: HashMap) : map<BT.G.Reference, seq<BT.G.Reference>>
  {
    map ref | ref in t.contents :: t.contents[ref].succs
  }

  function PredCounts(t: HashMap) : map<BT.G.Reference, int>
  {
    map ref | ref in t.contents :: t.contents[ref].predCount as int
  }

  datatype PredecessorEdge = PredecessorEdge(src: BT.G.Reference, ghost idx: int)

  function PredecessorSet(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference) : set<PredecessorEdge>
  {
    set src, idx | src in graph && 0 <= idx < |graph[src]| && graph[src][idx] == dest :: PredecessorEdge(src, idx)
  }

  function PredecessorSetRestricted(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference, domain: set<BT.G.Reference>) : set<PredecessorEdge>
  {
    set src, idx | src in graph && 0 <= idx < |graph[src]| && graph[src][idx] == dest && src in domain :: PredecessorEdge(src, idx)
  }

  function PredecessorSetRestrictedPartial(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference, domain: set<BT.G.Reference>, next: BT.G.Reference, j: int) : set<PredecessorEdge>
  {
    set src, idx | src in graph && 0 <= idx < |graph[src]| && graph[src][idx] == dest && (src in domain || (src == next && idx < j)) :: PredecessorEdge(src, idx)
  }

  predicate GraphClosedRestricted(graph: map<BT.G.Reference, seq<BT.G.Reference>>, domain: set<BT.G.Reference>)
  {
    forall ref | ref in graph && ref in domain ::
      forall i | 0 <= i < |graph[ref]| ::
        graph[ref][i] in graph
  }

  predicate GraphClosedRestrictedPartial(graph: map<BT.G.Reference, seq<BT.G.Reference>>, domain: set<BT.G.Reference>, next: BT.G.Reference, j: int)
  requires next in graph
  requires 0 <= j <= |graph[next]|
  {
    && GraphClosedRestricted(graph, domain)
    && (forall i | 0 <= i < j :: graph[next][i] in graph)
  }

  function IsRoot(ref: BT.G.Reference) : int
  {
    if ref == BT.G.Root() then 1 else 0
  }

  predicate ValidPredCounts(predCounts: map<BT.G.Reference, int>, graph: map<BT.G.Reference, seq<BT.G.Reference>>)
  {
    forall ref | ref in predCounts ::
        predCounts[ref] == |PredecessorSet(graph, ref)| + IsRoot(ref)
  }

  function MaxSize() : int
  {
    IndirectionTableMaxSize()
  }

  function method MaxSizeUint64() : uint64
  {
    IndirectionTableMaxSizeUint64()
  }

  protected predicate Inv(self: IndirectionTable)
  ensures Inv(self) ==> (forall ref | ref in self.locs :: ref in self.graph)
  {
    Inv1(self)
  }

  predicate TrackingGarbage(self: IndirectionTable)
  {
    self.garbageQueue.Some?
  }

  predicate Inv1(self: IndirectionTable)
  {
    && MutableMapModel.Inv(self.t)
    && self.locs == Locs(self.t)
    && self.graph == Graph(self.t)
    && self.predCounts == PredCounts(self.t)
    && ValidPredCounts(self.predCounts, self.graph)
    && BC.GraphClosed(self.graph)
    && (forall ref | ref in self.graph :: |self.graph[ref]| <= MaxNumChildren())
    && (self.garbageQueue.Some? ==>
      && LruModel.WF(self.garbageQueue.value)
      && (forall ref | ref in self.t.contents && self.t.contents[ref].predCount == 0 :: ref in LruModel.I(self.garbageQueue.value))
      && (forall ref | ref in LruModel.I(self.garbageQueue.value) :: ref in self.t.contents && self.t.contents[ref].predCount == 0)
    )
    && BT.G.Root() in self.t.contents
    && self.t.count as int <= MaxSize()
    && (forall ref | ref in self.graph :: ref <= self.refUpperBound)
    && (self.findLoclessIterator.Some? ==>
        && MutableMapModel.WFSimpleIter(self.t,
            self.findLoclessIterator.value)
        && (forall r | r in self.findLoclessIterator.value.s ::
            r in self.locs)
      )
  }

  lemma reveal_Inv(self: IndirectionTable)
  ensures Inv(self) == Inv1(self)
  {
  }

  function IHashMap(m: HashMap) : SectorType.IndirectionTable
  {
    SectorType.IndirectionTable(Locs(m), Graph(m))
  }

  function I(self: IndirectionTable) : SectorType.IndirectionTable
  {
    SectorType.IndirectionTable(self.locs, self.graph)
  }

  function FromHashMap(
    m: HashMap,
    q: Option<LruModel.LruQueue>,
    refUpperBound: uint64,
    findLoclessIterator: Option<MutableMapModel.SimpleIterator>
  ) : IndirectionTable
  {
    IndirectionTable(m, q, refUpperBound, findLoclessIterator, Locs(m), Graph(m), PredCounts(m))
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

  function {:opaque} AddLocIfPresent(self: IndirectionTable, ref: BT.G.Reference, loc: Location) : (IndirectionTable, bool)
  requires Inv(self)
  ensures var (self', added) := AddLocIfPresent(self, ref, loc);
    && Inv(self')
    && added == (ref in self.graph && ref !in self.locs)
    && self'.graph == self.graph
    && (added ==> self'.locs == self.locs[ref := loc])
    && (!added ==> self'.locs == self.locs)
    && (TrackingGarbage(self) ==> TrackingGarbage(self'))
  {
    var it := MutableMapModel.FindSimpleIter(self.t, ref);
    var oldEntry := MutableMapModel.SimpleIterOutput(self.t, it);
    var added := oldEntry.Next? && oldEntry.value.loc.None?;
    //assert oldEntry.Next? == (ref in self.graph);
    //assert oldEntry.Next? ==> oldEntry.value.loc.None? == (ref !in self.locs);
    if added then (
      var t := MutableMapModel.UpdateByIter(self.t, it, 
          Entry(Some(loc), oldEntry.value.succs, oldEntry.value.predCount));

      assert Graph(t) == Graph(self.t);
      assert PredCounts(t) == PredCounts(self.t);

      var _ := if self.findLoclessIterator.Some? then (
        MutableMapModel.UpdatePreservesSimpleIter(self.t, it, 
          Entry(Some(loc), oldEntry.value.succs, oldEntry.value.predCount), self.findLoclessIterator.value); 0
      ) else 0;

      (FromHashMap(t, self.garbageQueue, self.refUpperBound, self.findLoclessIterator), true)
    ) else (
      (self, false)
    )
  }

  /////// Reference count updating

  function SeqCountSet(s: seq<BT.G.Reference>, ref: BT.G.Reference, lb: int) : set<int>
  requires 0 <= lb <= |s|
  {
    set i | lb <= i < |s| && s[i] == ref
  }

  function SeqCount(s: seq<BT.G.Reference>, ref: BT.G.Reference, lb: int) : int
  requires 0 <= lb <= |s|
  {
    |SeqCountSet(s, ref, lb)|
  }

  function PredecessorSetExcept(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference, except: BT.G.Reference) : set<PredecessorEdge>
  {
    set src, idx | src in graph && 0 <= idx < |graph[src]| && graph[src][idx] == dest && src != except :: PredecessorEdge(src, idx)
  }

  predicate ValidPredCountsIntermediate(
      predCounts: map<BT.G.Reference, int>,
      graph: map<BT.G.Reference, seq<BT.G.Reference>>,
      newSuccs: seq<BT.G.Reference>,
      oldSuccs: seq<BT.G.Reference>,
      newIdx: int,
      oldIdx: int)
  requires 0 <= newIdx <= |newSuccs|
  requires 0 <= oldIdx <= |oldSuccs|
  {
    forall ref | ref in predCounts ::
      predCounts[ref] == |PredecessorSet(graph, ref)| + IsRoot(ref)
          - SeqCount(newSuccs, ref, newIdx)
          + SeqCount(oldSuccs, ref, oldIdx)
  }

  lemma SeqCountPlusPredecessorSetExcept(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference, except: BT.G.Reference)
  ensures var succs := if except in graph then graph[except] else [];
    SeqCount(succs, dest, 0) + |PredecessorSetExcept(graph, dest, except)| == |PredecessorSet(graph, dest)|
  {
    var succs := if except in graph then graph[except] else [];
    var a1 := SeqCountSet(succs, dest, 0);
    var a := set src, idx | src in graph && 0 <= idx < |graph[src]| && graph[src][idx] == dest && src == except :: PredecessorEdge(src, idx);
    var b := PredecessorSetExcept(graph, dest, except);
    var c := PredecessorSet(graph, dest);

    assert a + b == c;
    assert a !! b;
    assert |a| + |b| == |c|;

    var relation := iset p : (PredecessorEdge, int) | p.0.idx == p.1;
    forall x | x in a ensures exists y :: y in a1 && (x, y) in relation
    {
      var y := x.idx;
      assert y in a1 && (x, y) in relation;
    }
    forall y | y in a1 ensures exists x :: x in a && (x, y) in relation
    {
      var x := PredecessorEdge(except, y);
      assert x in a && (x, y) in relation;
    }
    SetBijectivity.BijectivityImpliesEqualCardinality(a, a1, relation);
    assert |a| == |a1|;
  }

  predicate RefcountUpdateInv(
      t: HashMap,
      q: LruModel.LruQueue,
      changingRef: BT.G.Reference,
      newSuccs: seq<BT.G.Reference>,
      oldSuccs: seq<BT.G.Reference>,
      newIdx: int,
      oldIdx: int)
  {
    && MutableMapModel.Inv(t)
    && LruModel.WF(q)
    && t.count as int <= MaxSize()
    && |oldSuccs| <= MaxNumChildren()
    && |newSuccs| <= MaxNumChildren()
    && (forall ref | ref in Graph(t) :: |Graph(t)[ref]| <= MaxNumChildren())
    && 0 <= newIdx <= |newSuccs|
    && 0 <= oldIdx <= |oldSuccs|
    && (changingRef in Graph(t) ==> Graph(t)[changingRef] == newSuccs)
    && (changingRef !in Graph(t) ==> newSuccs == [])
    && ValidPredCountsIntermediate(PredCounts(t), Graph(t), newSuccs, oldSuccs, newIdx, oldIdx)
    && (forall j | 0 <= j < |oldSuccs| :: oldSuccs[j] in t.contents)
    && BC.GraphClosed(Graph(t))
    && (forall ref | ref in t.contents && t.contents[ref].predCount == 0 :: ref in LruModel.I(q))
    && (forall ref | ref in LruModel.I(q) :: ref in t.contents && t.contents[ref].predCount == 0)
    && BT.G.Root() in t.contents
  }

  lemma SeqCountLePredecessorSet(
      graph: map<BT.G.Reference, seq<BT.G.Reference>>,
      ref: BT.G.Reference,
      r: BT.G.Reference,
      lb: int)
  requires r in graph
  requires 0 <= lb <= |graph[r]|
  ensures SeqCount(graph[r], ref, lb) <= |PredecessorSet(graph, ref)|
  {
    var setA := set i | lb <= i < |graph[r]| && graph[r][i] == ref;
    var setB := set src, idx | src in graph && 0 <= idx < |graph[src]| && graph[src][idx] == ref && src == r && lb <= idx :: PredecessorEdge(src, idx);
    var setC := set src, idx | src in graph && 0 <= idx < |graph[src]| && graph[src][idx] == ref :: PredecessorEdge(src, idx);
    

    calc {
      |SeqCountSet(graph[r], ref, lb)|;
      |setA|;
      {
        var relation := iset i, src, idx | src == r && i == idx :: (i, PredecessorEdge(src, idx));
        forall a | a in setA
        ensures exists b :: b in setB && (a, b) in relation
        {
          var b := PredecessorEdge(r, a);
          assert b in setB;
          assert (a, b) in relation;
        }
        forall b | b in setB
        ensures exists a :: a in setA && (a, b) in relation
        {
          var a := b.idx;
          assert a in setA;
          assert (a, b) in relation;
        }

        SetBijectivity.BijectivityImpliesEqualCardinality(setA, setB, relation);
      }
      |setB|;
    }

    SetInclusionImpliesSmallerCardinality(setB, setC);
  }

  lemma SeqCountInc(
      s: seq<BT.G.Reference>,
      ref: BT.G.Reference,
      idx: int)
  requires 0 <= idx < |s|
  requires s[idx] == ref
  ensures SeqCount(s, ref, idx + 1)
       == SeqCount(s, ref, idx) - 1;
  {
    var a := set i | idx <= i < |s| && s[i] == ref;
    var b := set i | idx + 1 <= i < |s| && s[i] == ref;
    assert a == b + {idx};
  }

  lemma SeqCountIncOther(
      s: seq<BT.G.Reference>,
      ref: BT.G.Reference,
      idx: int)
  requires 0 <= idx < |s|
  requires s[idx] != ref
  ensures SeqCount(s, ref, idx + 1)
       == SeqCount(s, ref, idx);
  {
    var a := set i | idx <= i < |s| && s[i] == ref;
    var b := set i | idx + 1 <= i < |s| && s[i] == ref;
    assert a == b;
  }

  lemma LemmaUpdatePredCountsDecStuff(
      t: HashMap,
      q: LruModel.LruQueue,
      changingRef: BT.G.Reference,
      newSuccs: seq<BT.G.Reference>,
      oldSuccs: seq<BT.G.Reference>,
      idx: int)
  requires RefcountUpdateInv(t, q, changingRef, newSuccs, oldSuccs, |newSuccs|, idx)
  ensures idx < |oldSuccs| ==> oldSuccs[idx] in t.contents
  ensures idx < |oldSuccs| ==> t.contents[oldSuccs[idx]].predCount > 0
  ensures idx < |oldSuccs| ==>
    var (t', q') := PredDec(t, q, oldSuccs[idx]);
    RefcountUpdateInv(t', q', changingRef, newSuccs, oldSuccs, |newSuccs|, idx + 1)
  ensures |LruModel.I(q)| <= 0x1_0000_0000
  {
    assert LruModel.I(q) <= t.contents.Keys;
    SetInclusionImpliesSmallerCardinality(LruModel.I(q), t.contents.Keys);
    assert |t.contents.Keys| == |t.contents|;

    if idx < |oldSuccs| {
      var graph := Graph(t);

      assert oldSuccs[idx] in graph;

      assert oldSuccs[idx] in t.contents;

      var ref := oldSuccs[idx];
      assert t.contents[ref].predCount as int
        == |PredecessorSet(graph, ref)| + IsRoot(ref)
          - SeqCount(newSuccs, ref, |newSuccs|)
          + SeqCount(oldSuccs, ref, idx);

      if changingRef in graph {
        SeqCountLePredecessorSet(graph, ref, changingRef, |newSuccs|);
        assert |PredecessorSet(graph, ref)|
            >= SeqCount(graph[changingRef], ref, |newSuccs|);
      }

      SeqCountInc(oldSuccs, ref, idx);
      assert SeqCount(oldSuccs, ref, idx + 1)
          == SeqCount(oldSuccs, ref, idx) - 1;

      assert t.contents[oldSuccs[idx]].predCount > 0;

      var (t', q') := PredDec(t, q, oldSuccs[idx]);
      assert Graph(t) == Graph(t');

      var predCounts := PredCounts(t);
      var predCounts' := PredCounts(t');
      forall r | r in predCounts'
      ensures predCounts'[r] == |PredecessorSet(graph, r)| + IsRoot(r)
          - SeqCount(newSuccs, r, |newSuccs|)
          + SeqCount(oldSuccs, r, idx + 1)
      {
        if r == ref {
        } else {
          SeqCountIncOther(oldSuccs, r, idx);
          assert SeqCount(oldSuccs, r, idx) == SeqCount(oldSuccs, r, idx + 1);
        }
      }

      LruModel.LruUse(q, ref);
    }
  }

  lemma PredecessorSetRestrictedSizeBound(graph: map<BT.G.Reference, seq<BT.G.Reference>>,
      dest: BT.G.Reference, domain: set<BT.G.Reference>)
  requires |graph| <= MaxSize()
  requires forall ref | ref in graph :: |graph[ref]| <= MaxNumChildren()
  ensures |PredecessorSetRestricted(graph, dest, domain)| <= MaxSize() * MaxNumChildren()
  {
    var s1 := set src, idx | src in graph && 0 <= idx < |graph[src]| && graph[src][idx] == dest && src in domain :: PredecessorEdge(src, idx);
    var s2 := set src, idx | src in graph.Keys && idx in SetRange(MaxNumChildren()) :: PredecessorEdge(src, idx);
    var s3 := set src, idx | src in graph.Keys && idx in SetRange(MaxNumChildren()) :: (src, idx);

    assert s1 <= s2;
    SetInclusionImpliesSmallerCardinality(s1, s2);
    assert |s1| <= |s2|;

    var relation := iset t : (PredecessorEdge, (BT.G.Reference, int)) | t.0.src == t.1.0 && t.0.idx == t.1.1;
    forall a | a in s2 ensures exists b :: b in s3 && (a, b) in relation
    {
      var b := (a.src, a.idx);
      assert b in s3;
    }
    forall b | b in s3 ensures exists a :: a in s2 && (a, b) in relation
    {
      var a := PredecessorEdge(b.0, b.1);
      assert a in s2;
    }
    SetBijectivity.BijectivityImpliesEqualCardinality(s2, s3, relation);
    assert |s2| == |s3|;

    var x1 := graph.Keys;
    var y1 := SetRange(MaxNumChildren());
    var z1 := (set a, b | a in x1 && b in y1 :: (a,b));
    SetBijectivity.CrossProductCardinality(x1, y1, z1);
    assert |s3|
        == |z1|
        == |x1| * |y1|
        == |graph.Keys| * |SetRange(MaxNumChildren())|;
    assert |graph.Keys| <= MaxSize();
    CardinalitySetRange(MaxNumChildren());
    assert |SetRange(MaxNumChildren())| == MaxNumChildren();
  }

  lemma PredecessorSetSizeBound(graph: map<BT.G.Reference, seq<BT.G.Reference>>,
      dest: BT.G.Reference)
  requires |graph| <= MaxSize()
  requires forall ref | ref in graph :: |graph[ref]| <= MaxNumChildren()
  ensures |PredecessorSet(graph, dest)| <= MaxSize() * MaxNumChildren()
  {
    PredecessorSetRestrictedSizeBound(graph, dest, graph.Keys);
    assert PredecessorSet(graph, dest) == PredecessorSetRestricted(graph, dest, graph.Keys);
  }

  lemma SeqCountBound(s: seq<BT.G.Reference>, ref: BT.G.Reference, lb: int)
  requires 0 <= lb <= |s|
  ensures SeqCount(s, ref, lb) <= |s|
  {
    var s1 := SeqCountSet(s, ref, lb);
    var s2 := SetRange(|s|);
    assert s1 <= s2;
    SetInclusionImpliesSmallerCardinality(s1, s2);
    CardinalitySetRange(|s|);
  }

  lemma LemmaUpdatePredCountsIncStuff(
      t: HashMap,
      q: LruModel.LruQueue,
      changingRef: BT.G.Reference,
      newSuccs: seq<BT.G.Reference>,
      oldSuccs: seq<BT.G.Reference>,
      idx: int)
  requires RefcountUpdateInv(t, q, changingRef, newSuccs, oldSuccs, idx, 0)
  ensures idx < |newSuccs| ==> newSuccs[idx] in t.contents
  ensures idx < |newSuccs| ==> t.contents[newSuccs[idx]].predCount < 0xffff_ffff_ffff_ffff
  ensures idx < |newSuccs| ==>
    var (t', q') := PredInc(t, q, newSuccs[idx]);
    RefcountUpdateInv(t', q', changingRef, newSuccs, oldSuccs, idx + 1, 0)
  ensures MutableMapModel.Inv(t)
  ensures 0 <= idx <= |newSuccs|
  {
    if idx < |newSuccs| {
      var graph := Graph(t);

      assert newSuccs[idx] in graph;
      assert newSuccs[idx] in t.contents;

      var ref := newSuccs[idx];
      assert t.contents[ref].predCount as int
        == |PredecessorSet(graph, ref)| + IsRoot(ref)
          - SeqCount(newSuccs, ref, idx)
          + SeqCount(oldSuccs, ref, 0);

      SeqCountInc(newSuccs, ref, idx);
      assert SeqCount(newSuccs, ref, idx + 1)
          == SeqCount(newSuccs, ref, idx) - 1;

      lemma_count_eq_graph_size(t);
      PredecessorSetSizeBound(graph, ref);
      SeqCountBound(oldSuccs, ref, 0);
      assert t.contents[ref].predCount < 0xffff_ffff_ffff_ffff;

      var (t', q') := PredInc(t, q, newSuccs[idx]);
      assert Graph(t) == Graph(t');

      var predCounts := PredCounts(t);
      var predCounts' := PredCounts(t');
      forall r | r in predCounts'
      ensures predCounts'[r] == |PredecessorSet(graph, r)| + IsRoot(r)
          - SeqCount(newSuccs, r, idx + 1)
          + SeqCount(oldSuccs, r, 0)
      {
        if r == ref {
        } else {
          SeqCountIncOther(newSuccs, r, idx);
        }
      }

      LruModel.LruRemove(q, ref);
    }
  }

  function PredInc(t: HashMap, q: LruModel.LruQueue, ref: BT.G.Reference) : (HashMap, LruModel.LruQueue)
  requires MutableMapModel.Inv(t)
  requires t.count as nat < 0x1_0000_0000_0000_0000 / 8
  requires ref in t.contents
  requires t.contents[ref].predCount < 0xffff_ffff_ffff_ffff
  {
    var oldEntry := t.contents[ref];
    var newEntry := oldEntry.(predCount := oldEntry.predCount + 1);
    var t' := MutableMapModel.Insert(t, ref, newEntry);
    var q' := if oldEntry.predCount == 0 then LruModel.Remove(q, ref) else q;
    (t', q')
  }

  function PredDec(t: HashMap, q: LruModel.LruQueue, ref: BT.G.Reference) : (HashMap, LruModel.LruQueue)
  requires MutableMapModel.Inv(t)
  requires t.count as nat < 0x1_0000_0000_0000_0000 / 8
  requires ref in t.contents
  requires t.contents[ref].predCount > 0
  {
    var oldEntry := t.contents[ref];
    var newEntry := oldEntry.(predCount := oldEntry.predCount - 1);
    var t' := MutableMapModel.Insert(t, ref, newEntry);
    var q' := if oldEntry.predCount == 1 then LruModel.Use(q, ref) else q;
    (t', q')
  }

  function UpdatePredCountsDec(
      t: HashMap,
      q: LruModel.LruQueue,
      changingRef: BT.G.Reference,
      newSuccs: seq<BT.G.Reference>,
      oldSuccs: seq<BT.G.Reference>,
      idx: uint64) : (res : (HashMap, LruModel.LruQueue))
  requires RefcountUpdateInv(t, q, changingRef, newSuccs, oldSuccs, |newSuccs|, idx as int)
  decreases |oldSuccs| - idx as int
  ensures var (t', q') := res;
    && RefcountUpdateInv(t', q', changingRef, newSuccs, oldSuccs, |newSuccs|, |oldSuccs|)
    && Graph(t) == Graph(t')
    && Locs(t) == Locs(t')
  {
    LemmaUpdatePredCountsDecStuff(t, q, changingRef, newSuccs, oldSuccs, idx as int);

    if idx == |oldSuccs| as uint64 then
      (t, q)
    else (
      var (t', q') := PredDec(t, q, oldSuccs[idx]);
      UpdatePredCountsDec(t', q', changingRef, newSuccs, oldSuccs, idx + 1)
    )
  }

  function {:fuel RefcountUpdateInv,0} UpdatePredCountsInc(
      t: HashMap,
      q: LruModel.LruQueue,
      changingRef: BT.G.Reference,
      newSuccs: seq<BT.G.Reference>,
      oldSuccs: seq<BT.G.Reference>,
      idx: uint64) : (res : (HashMap, LruModel.LruQueue))
  requires RefcountUpdateInv(t, q, changingRef, newSuccs, oldSuccs, idx as int, 0)
  decreases |newSuccs| - idx as int
  ensures var (t', q') := res;
    && RefcountUpdateInv(t', q', changingRef, newSuccs, oldSuccs, |newSuccs|, |oldSuccs|)
    && Graph(t) == Graph(t')
    && Locs(t) == Locs(t')
  {
    LemmaUpdatePredCountsIncStuff(t, q, changingRef, newSuccs, oldSuccs, idx as int);

    if idx == |newSuccs| as uint64 then
      UpdatePredCountsDec(t, q, changingRef, newSuccs, oldSuccs, 0)
    else (
      var (t', q') := PredInc(t, q, newSuccs[idx]);
      UpdatePredCountsInc(t', q', changingRef, newSuccs, oldSuccs, idx + 1)
    )
  }

  predicate SuccsValid(succs: seq<BT.G.Reference>, graph: map<BT.G.Reference, seq<BT.G.Reference>>)
  {
    forall ref | ref in succs :: ref in graph
  }

  lemma QueueSizeBound(self: IndirectionTable)
  requires Inv(self)
  ensures self.garbageQueue.Some? ==>
      |LruModel.I(self.garbageQueue.value)| <= 0x1_0000_0000;
  {
    if self.garbageQueue.Some? {
      SetInclusionImpliesSmallerCardinality(LruModel.I(self.garbageQueue.value), self.t.contents.Keys);
      assert |self.t.contents.Keys| == |self.t.contents|;
    }
  }

  lemma LemmaUpdateAndRemoveLocStuff(self: IndirectionTable, ref: BT.G.Reference, succs: seq<BT.G.Reference>)
  requires Inv(self)
  requires TrackingGarbage(self)
  requires |succs| <= MaxNumChildren()
  requires SuccsValid(succs, self.graph)
  requires self.t.count as nat <= MaxSize() - 1;
  ensures
    var oldEntry := MutableMapModel.Get(self.t, ref);
    var predCount := if oldEntry.Some? then oldEntry.value.predCount else 0;
    var t := MutableMapModel.Insert(self.t, ref, Entry(None, succs, predCount));
    var q := if oldEntry.Some? then self.garbageQueue.value else LruModel.Use(self.garbageQueue.value, ref);
    RefcountUpdateInv(t, q, ref, succs,
        if oldEntry.Some? then oldEntry.value.succs else [], 0, 0)
  ensures |LruModel.I(self.garbageQueue.value)| <= 0x1_0000_0000;
  {
    QueueSizeBound(self);

    var oldEntry := MutableMapModel.Get(self.t, ref);
    var predCount := if oldEntry.Some? then oldEntry.value.predCount else 0;
    var t := MutableMapModel.Insert(self.t, ref, Entry(None, succs, predCount));
    var q := if oldEntry.Some? then self.garbageQueue.value else LruModel.Use(self.garbageQueue.value, ref);

    LruModel.LruUse(self.garbageQueue.value, ref);

    assert oldEntry.Some? ==> oldEntry.value.succs == Graph(self.t)[ref];
    assert forall r | r != ref && r in Graph(t) :: r in Graph(self.t) && Graph(t)[r] == Graph(self.t)[r];

    var oldSuccs := if oldEntry.Some? then oldEntry.value.succs else [];

    var predCounts := PredCounts(t);
    var graph0 := Graph(self.t);
    var graph := Graph(t);

    forall r | r in predCounts
    ensures predCounts[r] == |PredecessorSet(graph, r)| + IsRoot(r)
          - SeqCount(succs, r, 0)
          + SeqCount(oldSuccs, r, 0)
    {
      SeqCountPlusPredecessorSetExcept(graph0, r, ref);
      SeqCountPlusPredecessorSetExcept(graph, r, ref);

      assert PredecessorSetExcept(graph0, r, ref)
          == PredecessorSetExcept(graph, r, ref);

      assert |PredecessorSet(graph0, r)| - SeqCount(oldSuccs, r, 0)
        == |PredecessorSetExcept(graph0, r, ref)|
        == |PredecessorSetExcept(graph, r, ref)|
        == |PredecessorSet(graph, r)| - SeqCount(succs, r, 0);
    }

    assert ValidPredCountsIntermediate(PredCounts(t), Graph(t), succs, oldSuccs, 0, 0);

    forall j | 0 <= j < |oldSuccs|
    ensures oldSuccs[j] in t.contents
    {
      assert oldSuccs[j] in graph0;
      assert oldSuccs[j] in graph;
    }

    assert RefcountUpdateInv(t, q, ref, succs, oldSuccs, 0, 0);
  }

  lemma LemmaValidPredCountsOfValidPredCountsIntermediate(
      predCounts: map<BT.G.Reference, int>,
      graph: map<BT.G.Reference, seq<BT.G.Reference>>,
      newSuccs: seq<BT.G.Reference>,
      oldSuccs: seq<BT.G.Reference>)
  requires ValidPredCountsIntermediate(predCounts, graph, newSuccs, oldSuccs, |newSuccs|, |oldSuccs|)
  ensures ValidPredCounts(predCounts, graph)
  {
  }

  lemma lemma_count_eq_graph_size(t: HashMap)
  requires MutableMapModel.Inv(t)
  ensures t.count as int == |Graph(t)|
  {
    assert Graph(t).Keys == t.contents.Keys;
    assert |Graph(t)|
        == |Graph(t).Keys|
        == |t.contents.Keys|
        == t.count as int;
  }

  function {:opaque} UpdateAndRemoveLoc(self: IndirectionTable, ref: BT.G.Reference, succs: seq<BT.G.Reference>) : (res : (IndirectionTable, Option<Location>))
  requires Inv(self)
  requires TrackingGarbage(self)
  requires |self.graph| < MaxSize()
  requires |succs| <= MaxNumChildren()
  requires SuccsValid(succs, self.graph)
  ensures var (self', oldLoc) := res;
    && Inv(self')
    && TrackingGarbage(self')
    && self'.locs == MapRemove1(self.locs, ref)
    && self'.graph == self.graph[ref := succs]
    && (oldLoc.None? ==> ref !in self.locs)
    && (oldLoc.Some? ==> ref in self.locs && self.locs[ref] == oldLoc.value)
  {
    lemma_count_eq_graph_size(self.t);
    LemmaUpdateAndRemoveLocStuff(self, ref, succs);

    var oldEntry := MutableMapModel.Get(self.t, ref);
    var predCount := if oldEntry.Some? then oldEntry.value.predCount else 0;
    var q := if oldEntry.Some? then self.garbageQueue.value else LruModel.Use(self.garbageQueue.value, ref);
    var t := MutableMapModel.Insert(self.t, ref, Entry(None, succs, predCount));

    var (t1, garbageQueue1) := UpdatePredCountsInc(t, q, ref, succs,
        if oldEntry.Some? then oldEntry.value.succs else [], 0);

    lemma_count_eq_graph_size(t);
    lemma_count_eq_graph_size(t1);

    LemmaValidPredCountsOfValidPredCountsIntermediate(PredCounts(t1), Graph(t1), succs,
        if oldEntry.Some? then oldEntry.value.succs else []);

    var refUpperBound' := if self.refUpperBound > ref then self.refUpperBound else ref;
    assert forall r | r in Graph(t1) :: r in self.graph || r == ref;

    var self' := FromHashMap(t1, Some(garbageQueue1), refUpperBound', None);
    var oldLoc := if oldEntry.Some? && oldEntry.value.loc.Some? then oldEntry.value.loc else None;
    (self', oldLoc)
  }

  function {:opaque} RemoveLoc(self: IndirectionTable, ref: BT.G.Reference) : (res : (IndirectionTable, Option<Location>))
  requires Inv(self)
  requires TrackingGarbage(self)
  requires ref in self.graph
  ensures var (self', oldLoc) := res;
    && Inv(self')
    && TrackingGarbage(self')
    && self'.locs == MapRemove1(self.locs, ref)
    && self'.graph == self.graph
    && (oldLoc.None? ==> ref !in self.locs)
    && (oldLoc.Some? ==> ref in self.locs && self.locs[ref] == oldLoc.value)
  {
    var it := MutableMapModel.FindSimpleIter(self.t, ref);
    var oldEntry := MutableMapModel.SimpleIterOutput(self.t, it);

    var predCount := oldEntry.value.predCount;
    var succs := oldEntry.value.succs;

    var t := MutableMapModel.UpdateByIter(self.t, it, Entry(None, succs, predCount));

    var self' := FromHashMap(t, self.garbageQueue, self.refUpperBound, None);
    var oldLoc := oldEntry.value.loc;

    assert PredCounts(t) == PredCounts(self.t);
    assert Graph(t) == Graph(self.t);

    (self', oldLoc)
  }

  ////// Parsing stuff

  function ComputeRefCountsEntryIterate(t: HashMap, succs: seq<BT.G.Reference>, i: uint64) : (t' : Option<HashMap>)
  requires MutableMapModel.Inv(t)
  requires 0 <= i as int <= |succs|
  requires |succs| <= MaxNumChildren()
  requires t.count as int <= MaxSize()
  requires forall ref | ref in t.contents :: t.contents[ref].predCount as int <= 0x1_0000_0000_0000 + i as int
  decreases |succs| - i as int
  {
    if i == |succs| as uint64 then (
      Some(t)
    ) else (
      var ref := succs[i];
      var oldEntry := MutableMapModel.Get(t, ref);
      if oldEntry.Some? then (
        var newEntry := oldEntry.value.(predCount := oldEntry.value.predCount + 1);
        var t0 := MutableMapModel.Insert(t, ref, newEntry);
        ComputeRefCountsEntryIterate(t0, succs, i + 1)
      ) else (
        None
      )
    )
  }

  predicate ComputeRefCountsIterateInv(t: HashMap, copy: HashMap, it: MutableMapModel.Iterator<Entry>)
  {
    && MutableMapModel.Inv(t)
    && MutableMapModel.Inv(copy)
    && MutableMapModel.WFIter(copy, it)
    && (forall ref | ref in copy.contents :: ref in t.contents)
    && (forall ref | ref in copy.contents :: t.contents[ref].loc == copy.contents[ref].loc)
    && (forall ref | ref in copy.contents :: t.contents[ref].succs == copy.contents[ref].succs)
    && (forall ref | ref in copy.contents :: t.contents[ref].predCount as int == |PredecessorSetRestricted(Graph(copy), ref, it.s)| + IsRoot(ref))
    && (forall ref | ref in copy.contents :: |copy.contents[ref].succs| <= MaxNumChildren())
    && (forall ref | ref in t.contents :: ref in copy.contents)
    && GraphClosedRestricted(Graph(copy), it.s)
    && (t.count == copy.count)
    && (t.count as int <= MaxSize())
  }

  lemma LemmaPredecessorSetRestrictedPartialAdd1Self(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference, domain: set<BT.G.Reference>, next: BT.G.Reference, j: int)
  requires next in graph
  requires 0 <= j < |graph[next]|
  requires dest == graph[next][j]
  requires next !in domain
  ensures |PredecessorSetRestrictedPartial(graph, dest, domain, next, j + 1)|
       == |PredecessorSetRestrictedPartial(graph, dest, domain, next, j)| + 1
  {
    assert PredecessorSetRestrictedPartial(graph, dest, domain, next, j + 1)
        == PredecessorSetRestrictedPartial(graph, dest, domain, next, j) + {PredecessorEdge(next, j)};
  }

  lemma LemmaPredecessorSetRestrictedPartialAdd1Other(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference, domain: set<BT.G.Reference>, next: BT.G.Reference, j: int)
  requires next in graph
  requires 0 <= j < |graph[next]|
  requires dest != graph[next][j]
  ensures |PredecessorSetRestrictedPartial(graph, dest, domain, next, j + 1)|
       == |PredecessorSetRestrictedPartial(graph, dest, domain, next, j)|
  {
    assert PredecessorSetRestrictedPartial(graph, dest, domain, next, j + 1)
        == PredecessorSetRestrictedPartial(graph, dest, domain, next, j);
  }

  lemma LemmaComputeRefCountsEntryIterateCorrectPartial(t: HashMap, copy: HashMap, it: MutableMapModel.Iterator<Entry>, i: uint64)
  requires it.next.Next?
  requires MutableMapModel.Inv(t)
  requires MutableMapModel.Inv(copy)
  requires MutableMapModel.WFIter(copy, it)
  requires (forall ref | ref in t.contents :: ref in copy.contents)
  requires (forall ref | ref in copy.contents :: ref in t.contents)
  requires (forall ref | ref in copy.contents :: t.contents[ref].succs == copy.contents[ref].succs)
  requires (forall ref | ref in t.contents :: t.contents[ref].loc == copy.contents[ref].loc)
  requires t.count == copy.count
  requires ComputeRefCountsEntryIterate.requires(t, copy.contents[it.next.key].succs, i)
  requires forall ref | ref in t.contents :: t.contents[ref].predCount as int == |PredecessorSetRestrictedPartial(Graph(copy), ref, it.s, it.next.key, i as int)| + IsRoot(ref)
  requires BT.G.Root() in t.contents
  ensures var t' := ComputeRefCountsEntryIterate(t, copy.contents[it.next.key].succs, i);
    && (t'.Some? ==>
      && MutableMapModel.Inv(t'.value)
      && (forall ref | ref in t'.value.contents :: t'.value.contents[ref].predCount as int == |PredecessorSetRestricted(Graph(copy), ref, it.s + {it.next.key})| + IsRoot(ref))
      && (forall ref | ref in t'.value.contents :: ref in copy.contents)
      && (forall ref | ref in copy.contents :: ref in t'.value.contents)
      && (forall ref | ref in t'.value.contents :: t'.value.contents[ref].loc == copy.contents[ref].loc)
      && (forall ref | ref in t'.value.contents :: t'.value.contents[ref].succs == copy.contents[ref].succs)
      && t'.value.count == copy.count
      && BT.G.Root() in t'.value.contents
    )
    && (t'.None? ==> !BC.GraphClosed(Graph(copy)))
  decreases |copy.contents[it.next.key].succs| - i as int
  {
    var succs := copy.contents[it.next.key].succs;
    if i == |succs| as uint64 {
      forall ref | ref in t.contents
      ensures t.contents[ref].predCount as int == |PredecessorSetRestricted(Graph(copy), ref, it.s + {it.next.key})| + IsRoot(ref)
      {
        assert PredecessorSetRestricted(Graph(copy), ref, it.s + {it.next.key}) == PredecessorSetRestrictedPartial(Graph(copy), ref, it.s, it.next.key, i as int);
      }
    } else {
      var ref := succs[i];
      var oldEntry := MutableMapModel.Get(t, ref);
      if oldEntry.Some? {
        var newEntry := oldEntry.value.(predCount := oldEntry.value.predCount + 1);
        var t0 := MutableMapModel.Insert(t, ref, newEntry);

        forall r | r in t0.contents
        ensures t0.contents[r].predCount as int == |PredecessorSetRestrictedPartial(Graph(copy), r, it.s, it.next.key, (i+1) as int)| + IsRoot(r)
        {
          if r == ref {
            LemmaPredecessorSetRestrictedPartialAdd1Self(Graph(copy), r, it.s, it.next.key, i as int);
          } else {
            LemmaPredecessorSetRestrictedPartialAdd1Other(Graph(copy), r, it.s, it.next.key, i as int);
          }
        }

        LemmaComputeRefCountsEntryIterateCorrectPartial(t0, copy, it, i+1);
      } else {
        //assert it.next.key in Graph(copy);
        assert ref in Graph(copy)[it.next.key];
      }
    }
  }

  lemma LemmaComputeRefCountsEntryIterateGraphClosed(t: HashMap, copy: HashMap, it: MutableMapModel.Iterator<Entry>, i: uint64)
  requires it.next.Next?
  requires MutableMapModel.Inv(t)
  requires MutableMapModel.Inv(copy)
  requires MutableMapModel.WFIter(copy, it)
  requires ComputeRefCountsEntryIterate.requires(t, copy.contents[it.next.key].succs, i)
  requires (forall ref | ref in t.contents :: ref in copy.contents)
  requires (forall ref | ref in copy.contents :: ref in t.contents)
  requires (forall ref | ref in copy.contents :: t.contents[ref].succs == copy.contents[ref].succs)
  requires GraphClosedRestrictedPartial(Graph(copy), it.s, it.next.key, i as int)
  ensures var t' := ComputeRefCountsEntryIterate(t, copy.contents[it.next.key].succs, i);
    && (t'.Some? ==>
      && GraphClosedRestricted(Graph(copy), it.s + {it.next.key})
    )
  decreases |copy.contents[it.next.key].succs| - i as int
  {
    var succs := copy.contents[it.next.key].succs;
    if i == |succs| as uint64 {
      /*var graph := Graph(copy);
      var domain := it.s + {it.next.key};
      forall ref | ref in graph && ref in domain
      ensures forall j | 0 <= j < |graph[ref]| :: graph[ref][j] in graph
      {
        forall j | 0 <= j < |graph[ref]|
        ensures graph[ref][j] in graph
        {
          if ref == it.next.key {
            assert j < i as int;
            assert forall j | 0 <= j < i as int :: graph[it.next.key][j] in graph;
            assert graph[it.next.key][j] in graph;
            assert graph[ref][j] in graph;
          } else {
            assert ref in it.s;
            assert graph[ref][j] in graph;
          }
        }
      }*/
    } else {
      var ref := succs[i];
      var oldEntry := MutableMapModel.Get(t, ref);
      if oldEntry.Some? {
        var newEntry := oldEntry.value.(predCount := oldEntry.value.predCount + 1);
        var t0 := MutableMapModel.Insert(t, ref, newEntry);

        var graph := Graph(t0);
        forall k | 0 <= k < i+1
        ensures graph[it.next.key][k] in graph
        {
          if k == i {
            assert graph[it.next.key][k] in graph;
          } else {
            assert Graph(copy)[it.next.key][k] in Graph(copy);
            assert graph[it.next.key][k] in graph;
          }
        }
        LemmaComputeRefCountsEntryIterateGraphClosed(t0, copy, it, i+1);
      } else {
        //assert it.next.key in Graph(copy);
        assert ref in Graph(copy)[it.next.key];
      }
    }
  }

  lemma LemmaComputeRefCountsEntryIterateCorrect(t: HashMap, copy: HashMap, it: MutableMapModel.Iterator<Entry>)
  requires it.next.Next?
  requires ComputeRefCountsIterateInv(t, copy, it)
  requires ComputeRefCountsEntryIterate.requires(t, copy.contents[it.next.key].succs, 0)
  requires forall ref | ref in t.contents :: t.contents[ref].predCount as int == |PredecessorSetRestricted(Graph(copy), ref, it.s)| + IsRoot(ref)
  requires BT.G.Root() in t.contents
  ensures var t' := ComputeRefCountsEntryIterate(t, copy.contents[it.next.key].succs, 0);
    && (t'.Some? ==>
      && MutableMapModel.Inv(t'.value)
      && (forall ref | ref in t'.value.contents :: t'.value.contents[ref].predCount as int == |PredecessorSetRestricted(Graph(copy), ref, it.s + {it.next.key})| + IsRoot(ref))
      && (forall ref | ref in t'.value.contents :: ref in copy.contents)
      && (forall ref | ref in copy.contents :: ref in t'.value.contents)
      && (forall ref | ref in t'.value.contents :: t'.value.contents[ref].loc == t.contents[ref].loc)
      && (forall ref | ref in t'.value.contents :: t'.value.contents[ref].succs == t.contents[ref].succs)
      && t'.value.count == copy.count
      && GraphClosedRestricted(Graph(copy), it.s + {it.next.key})
    )
    && (t'.None? ==> !BC.GraphClosed(Graph(copy)))
  {
    forall ref | ref in t.contents
    ensures t.contents[ref].predCount as int == |PredecessorSetRestrictedPartial(Graph(copy), ref, it.s, it.next.key, 0)| + IsRoot(ref)
    {
      assert PredecessorSetRestrictedPartial(Graph(copy), ref, it.s, it.next.key, 0)
          == PredecessorSetRestricted(Graph(copy), ref, it.s);
    }
    LemmaComputeRefCountsEntryIterateCorrectPartial(t, copy, it, 0);
    LemmaComputeRefCountsEntryIterateGraphClosed(t, copy, it, 0);
  }

  lemma LemmaComputeRefCountsIterateStuff(t: HashMap, copy: HashMap, it: MutableMapModel.Iterator<Entry>)
  requires ComputeRefCountsIterateInv(t, copy, it)
  requires BT.G.Root() in t.contents
  ensures forall ref | ref in t.contents :: t.contents[ref].predCount as int <= 0x1_0000_0000_0000
  ensures it.next.Next? ==>
    var succs := it.next.value.succs;
    var t0 := ComputeRefCountsEntryIterate(t, succs, 0);
    && (t0.Some? ==> ComputeRefCountsIterateInv(t0.value, copy, MutableMapModel.IterInc(copy, it)))
    && (t0.None? ==> !BC.GraphClosed(Graph(copy)))
  {
    forall ref | ref in t.contents
    ensures t.contents[ref].predCount as int <= 0x1_0000_0000_0000;
    {
      lemma_count_eq_graph_size(copy);
      PredecessorSetRestrictedSizeBound(Graph(copy), ref, it.s);
    }
    if it.next.Next? {
      assert |copy.contents[it.next.key].succs| <= MaxNumChildren();
      LemmaComputeRefCountsEntryIterateCorrect(t, copy, it);
    }
  }

  lemma LemmaComputeRefCountsIterateValidPredCounts(
    t: HashMap, copy: HashMap, it: MutableMapModel.Iterator<Entry>)
  requires ComputeRefCountsIterateInv(t, copy, it)
  ensures it.next.Done? ==> ValidPredCounts(PredCounts(t), Graph(t))
  {
    if it.next.Done? {
      var predCounts := PredCounts(t);
      var graph := Graph(t);
      forall ref | ref in predCounts
      ensures predCounts[ref] == |PredecessorSet(graph, ref)| + IsRoot(ref)
      {
        assert PredecessorSet(graph, ref)
            //== PredecessorSetRestricted(graph, ref, it.s)
            == PredecessorSetRestricted(Graph(copy), ref, it.s);
      }
    }
  }

  // Copy is the original, with zero-ed out predCounts.
  // t is the one that we're actually filling in.
  // We don't really need to make a copy, but it's easier\
  // as we don't need to prove anything about iterator preservation.
  function ComputeRefCountsIterate(t: HashMap, copy: HashMap, it: MutableMapModel.Iterator<Entry>) : (t' : Option<HashMap>)
  requires ComputeRefCountsIterateInv(t, copy, it)
  requires BT.G.Root() in t.contents
  ensures t'.Some? ==> MutableMapModel.Inv(t'.value)
  ensures t'.Some? <==> BC.GraphClosed(Graph(copy))
  ensures t'.Some? ==> Graph(copy) == Graph(t'.value)
  ensures t'.Some? ==> Locs(copy) == Locs(t'.value)
  ensures t'.Some? ==> ValidPredCounts(PredCounts(t'.value), Graph(t'.value))
  ensures t'.Some? ==> BT.G.Root() in t'.value.contents
  decreases it.decreaser
  {
    LemmaComputeRefCountsIterateStuff(t, copy, it);
    LemmaComputeRefCountsIterateValidPredCounts(t, copy, it);

    if it.next.Done? then (
      Some(t)
    ) else (
      var succs := it.next.value.succs;
      var t0 := ComputeRefCountsEntryIterate(t, succs, 0);
      if t0.Some? then (
        ComputeRefCountsIterate(t0.value, copy, MutableMapModel.IterInc(copy, it))
      ) else (
        None
      )
    )
  }

  lemma LemmaComputeRefCountsIterateInvInit(t: HashMap)
  requires MutableMapModel.Inv(t)
  requires forall ref | ref in t.contents :: t.contents[ref].predCount == 0
  requires forall ref | ref in t.contents :: |t.contents[ref].succs| <= MaxNumChildren()
  requires t.count as int <= MaxSize()
  requires BT.G.Root() in t.contents
  ensures
    var oldEntry := t.contents[BT.G.Root()];
    var t0 := MutableMapModel.Insert(t, BT.G.Root(), oldEntry.(predCount := 1));
    ComputeRefCountsIterateInv(t0, t, MutableMapModel.IterStart(t))
  {
    var oldEntry := t.contents[BT.G.Root()];
    var t0 := MutableMapModel.Insert(t, BT.G.Root(), oldEntry.(predCount := 1));

    var it := MutableMapModel.IterStart(t);
    forall ref | ref in t0.contents
    ensures t0.contents[ref].predCount as int
        == |PredecessorSetRestricted(Graph(t0), ref, it.s)| + IsRoot(ref)
    {
      assert PredecessorSetRestricted(Graph(t0), ref, it.s) == {};
    }
  }

  function ComputeRefCounts(t: HashMap) : (t' : Option<HashMap>)
  requires MutableMapModel.Inv(t)
  requires forall ref | ref in t.contents :: t.contents[ref].predCount == 0
  requires forall ref | ref in t.contents :: |t.contents[ref].succs| <= MaxNumChildren()
  requires t.count as int <= MaxSize()
  requires BT.G.Root() in t.contents
  ensures BC.GraphClosed(Graph(t)) <==> t'.Some?
  ensures t'.Some? ==> Graph(t) == Graph(t'.value)
  ensures t'.Some? ==> Locs(t) == Locs(t'.value)
  ensures t'.Some? ==> ValidPredCounts(PredCounts(t'.value), Graph(t'.value))
  ensures t'.Some? ==> BT.G.Root() in t'.value.contents
  {
    LemmaComputeRefCountsIterateInvInit(t);

    var oldEntry := t.contents[BT.G.Root()];
    var t0 := MutableMapModel.Insert(t, BT.G.Root(), oldEntry.(predCount := 1));

    ComputeRefCountsIterate(t0, t, MutableMapModel.IterStart(t))
  }

  function {:fuel ValInGrammar,3} valToHashMap(a: seq<V>) : (s : Option<HashMap>)
  requires |a| <= MaxSize()
  requires forall i | 0 <= i < |a| :: ValidVal(a[i])
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GTuple([GUint64, GUint64, GUint64, GUint64Array]))
  ensures s.Some? ==> s.value.count as int == |a|
  ensures s.Some? ==> forall v | v in s.value.contents.Values :: v.loc.Some? && ValidNodeLocation(v.loc.value)
  ensures s.Some? ==> forall ref | ref in s.value.contents :: s.value.contents[ref].predCount == 0
  ensures s.Some? ==> forall ref | ref in s.value.contents :: |s.value.contents[ref].succs| <= MaxNumChildren()
  ensures s.Some? ==> Marshalling.valToIndirectionTableMaps(a) == Some(IHashMap(s.value))
  ensures s.None? ==> Marshalling.valToIndirectionTableMaps(a).None?
  {
    if |a| == 0 then
      var s := Some(MutableMapModel.Constructor(1024));
      assert Locs(s.value) == map[];
      assert Graph(s.value) == map[];
      //assert s.Some? ==> Marshalling.valToIndirectionTableMaps(a) == Some(IHashMap(s.value));
      s
    else (
      var res := valToHashMap(DropLast(a));
      match res {
        case Some(table) => (
          var tuple := Last(a);
          var ref := tuple.t[0].u;
          var lba := tuple.t[1].u;
          var len := tuple.t[2].u;
          var succs := tuple.t[3].ua;
          var loc := Location(lba, len);
          if ref in table.contents || !ValidNodeLocation(loc) || |succs| as int > MaxNumChildren() then (
            None
          ) else (
            var res := MutableMapModel.Insert(table, ref, Entry(Some(loc), succs, 0));
            assert Locs(res) == Locs(table)[ref := loc];
            assert Graph(res) == Graph(table)[ref := succs];
            //assert Marshalling.valToIndirectionTableMaps(a) == Some(IHashMap(res));
            Some(res)
          )
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

  function makeGarbageQueueIterate(t: HashMap, q: LruModel.LruQueue, it: MutableMapModel.Iterator<Entry>) : LruModel.LruQueue
  requires MutableMapModel.Inv(t)
  requires MutableMapModel.WFIter(t, it)
  requires LruModel.WF(q)
  decreases it.decreaser
  {
    if it.next.Done? then
      q
    else (
      var q' := (if it.next.value.predCount == 0 then
        LruModel.LruUse(q, it.next.key);
        LruModel.Use(q, it.next.key)
      else
        q);
      var it' := MutableMapModel.IterInc(t, it);
      makeGarbageQueueIterate(t, q', it')
    )
  }

  function {:opaque} makeGarbageQueue(t: HashMap) : LruModel.LruQueue
  requires MutableMapModel.Inv(t)
  {
    makeGarbageQueueIterate(t, LruModel.Empty(), MutableMapModel.IterStart(t))
  }

  lemma makeGarbageQueueIterateCorrect(t: HashMap, q: LruModel.LruQueue, it: MutableMapModel.Iterator<Entry>)
  requires MutableMapModel.Inv(t)
  requires MutableMapModel.WFIter(t, it)
  requires LruModel.WF(q)
  requires (forall ref | ref in t.contents && t.contents[ref].predCount == 0 && ref in it.s :: ref in LruModel.I(q))
  requires (forall ref | ref in LruModel.I(q) :: ref in t.contents && t.contents[ref].predCount == 0 && ref in it.s)
  ensures var q' := makeGarbageQueueIterate(t, q, it);
    && LruModel.WF(q')
    && (forall ref | ref in t.contents && t.contents[ref].predCount == 0 :: ref in LruModel.I(q'))
    && (forall ref | ref in LruModel.I(q') :: ref in t.contents && t.contents[ref].predCount == 0)
  decreases it.decreaser
  {
    if it.next.Done? {
    } else {
      var q' := (if it.next.value.predCount == 0 then
        LruModel.LruUse(q, it.next.key);
        LruModel.Use(q, it.next.key)
      else
        q);
      var it' := MutableMapModel.IterInc(t, it);
      makeGarbageQueueIterateCorrect(t, q', it');
    }
  }

  lemma lemmaMakeGarbageQueueCorrect(t: HashMap)
  requires MutableMapModel.Inv(t)
  ensures var q := makeGarbageQueue(t);
    && LruModel.WF(q)
    && (forall ref | ref in t.contents && t.contents[ref].predCount == 0 :: ref in LruModel.I(q))
    && (forall ref | ref in LruModel.I(q) :: ref in t.contents && t.contents[ref].predCount == 0)
  {
    reveal_makeGarbageQueue();
    makeGarbageQueueIterateCorrect(t, LruModel.Empty(), MutableMapModel.IterStart(t));
  }

  function computeRefUpperBoundIterate(t: HashMap, it: MutableMapModel.Iterator<Entry>, refUpperBound: uint64) : (r: uint64)
  requires MutableMapModel.Inv(t)
  requires MutableMapModel.WFIter(t, it)
  requires forall ref | ref in it.s :: ref <= refUpperBound
  ensures forall ref | ref in t.contents :: ref <= r
  decreases it.decreaser
  {
    if it.next.Next? then (
      computeRefUpperBoundIterate(t, MutableMapModel.IterInc(t, it),
          if it.next.key > refUpperBound then it.next.key else refUpperBound)
    ) else (
      refUpperBound
    )
  }

  function computeRefUpperBound(t: HashMap) : (r: uint64)
  requires MutableMapModel.Inv(t)
  ensures forall ref | ref in t.contents :: ref <= r
  {
    computeRefUpperBoundIterate(t, MutableMapModel.IterStart(t), 0)
  }

  function valToIndirectionTable(v: V) : (s : Option<IndirectionTable>)
  requires ValidVal(v)
  requires ValInGrammar(v, IndirectionTableGrammar())
  ensures s.Some? ==> Inv(s.value)
  ensures s.Some? ==> TrackingGarbage(s.value)
  ensures s.Some? ==> BC.WFCompleteIndirectionTable(I(s.value))
  ensures s.Some? ==> Marshalling.valToIndirectionTable(v) == Some(I(s.value))
  ensures s.None? ==> Marshalling.valToIndirectionTable(v).None?
  {
    if |v.a| <= MaxSize() then (
      var t := valToHashMap(v.a);
      match t {
        case Some(t) => (
          if BT.G.Root() in t.contents then (
            var t1 := ComputeRefCounts(t);
            if t1.Some? then (
              lemmaMakeGarbageQueueCorrect(t1.value);
              lemma_count_eq_graph_size(t);
              lemma_count_eq_graph_size(t1.value);
              var refUpperBound := computeRefUpperBound(t1.value);
              var res := FromHashMap(t1.value, Some(makeGarbageQueue(t1.value)), refUpperBound, None);
              Some(res)
            ) else (
              None
            )
          ) else (
            None
          )
        )
        case None => None
      }
    ) else (
      None
    )
  }

  // To bitmap

  predicate IsLocAllocIndirectionTable(indirectionTable: IndirectionTable, i: int)
  {
    // Can't use the lower values, so they're always marked "allocated"
    || 0 <= i < MinNodeBlockIndex()
    || (!(
      forall ref | ref in indirectionTable.locs ::
        indirectionTable.locs[ref].addr as int != i * NodeBlockSize() as int
    ))
  }

  predicate IsLocAllocBitmap(bm: BitmapModel.BitmapModelT, i: int)
  {
    && 0 <= i < BitmapModel.Len(bm)
    && BitmapModel.IsSet(bm, i)
  }

  function BitmapInitUpToIterate(bm: BitmapModel.BitmapModelT, i: uint64, upTo: uint64) : (res:BitmapModel.BitmapModelT)
  requires 0 <= i as int <= upTo as int <= BitmapModel.Len(bm)
  ensures BitmapModel.Len(res) == BitmapModel.Len(bm)
  decreases upTo - i
  {
    if i == upTo then
      bm
    else
      BitmapInitUpToIterate(BitmapModel.BitSet(bm, i as int), i+1, upTo)
  }

  function {:opaque} BitmapInitUpTo(bm: BitmapModel.BitmapModelT, upTo: uint64) : (res:BitmapModel.BitmapModelT)
  requires upTo as int <= BitmapModel.Len(bm)
  ensures BitmapModel.Len(res) == BitmapModel.Len(bm)
  {
    BitmapInitUpToIterate(bm, 0, upTo)
  }

  function InitLocBitmapIterate(indirectionTable: IndirectionTable,
      it: MutableMapModel.Iterator<Entry>,
      bm: BitmapModel.BitmapModelT)
  : (res : (bool, BitmapModel.BitmapModelT))
  requires Inv(indirectionTable)
  requires MutableMapModel.WFIter(indirectionTable.t, it)
  requires BC.WFCompleteIndirectionTable(I(indirectionTable))
  requires BitmapModel.Len(bm) == NumBlocks()
  ensures BitmapModel.Len(res.1) == NumBlocks()
  decreases it.decreaser
  {
    if it.next.Done? then (
      (true, bm)
    ) else (
      assert it.next.key in I(indirectionTable).locs;

      var loc: uint64 := it.next.value.loc.value.addr;
      var locIndex: uint64 := loc / NodeBlockSize() as uint64;
      if locIndex < NumBlocks() as uint64 && !BitmapModel.IsSet(bm, locIndex as int) then (
        InitLocBitmapIterate(indirectionTable,
            MutableMapModel.IterInc(indirectionTable.t, it),
            BitmapModel.BitSet(bm, locIndex as int))
      ) else (
        (false, bm)
      )
    )
  }

  function {:opaque} InitLocBitmap(indirectionTable: IndirectionTable) : (res : (bool, BitmapModel.BitmapModelT))
  requires Inv(indirectionTable)
  requires BC.WFCompleteIndirectionTable(I(indirectionTable))
  ensures BitmapModel.Len(res.1) == NumBlocks()
  {
    var bm := BitmapModel.EmptyBitmap(NumBlocks());
    var bm' := BitmapInitUpTo(bm, MinNodeBlockIndexUint64());
    InitLocBitmapIterate(indirectionTable,
        MutableMapModel.IterStart(indirectionTable.t),
        bm')
  }

  predicate IsLocAllocIndirectionTablePartial(indirectionTable: IndirectionTable, i: int, s: set<uint64>)
  {
    || 0 <= i < MinNodeBlockIndex() // these blocks can't be used
    || !(
      forall ref | ref in indirectionTable.locs && ref in s ::
        indirectionTable.locs[ref].addr as int != i * NodeBlockSize() as int
    )
  }

  lemma InitLocBitmapIterateCorrect(indirectionTable: IndirectionTable,
      it: MutableMapModel.Iterator<Entry>,
      bm: BitmapModel.BitmapModelT)
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
    BitmapModel.reveal_BitSet();
    BitmapModel.reveal_IsSet();

    var (succ, bm') := InitLocBitmapIterate(indirectionTable, it, bm);
    if it.next.Done? {
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
        assert it.next.key in indirectionTable.locs;
        var loc: uint64 := it.next.value.loc.value.addr;
        var locIndex: uint64 := loc / NodeBlockSize() as uint64;

        //assert I(indirectionTable).locs[kv.0] == kv.1.0.value;
        reveal_ValidNodeAddr();
        assert ValidNodeLocation(it.next.value.loc.value);
        assert locIndex as int * NodeBlockSize() == loc as int;

        //assert locIndex < NumBlocks() as uint64;
        //assert !BitmapModel.IsSet(bm, locIndex as int);

        var bm0 := BitmapModel.BitSet(bm, locIndex as int);
        var it0 := MutableMapModel.IterInc(indirectionTable.t, it);

        forall i: int
        | IsLocAllocIndirectionTablePartial(indirectionTable, i, it0.s)
        ensures IsLocAllocBitmap(bm0, i)
        {
          // This triggers all the right stuff:
          if IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s) { }
          /*
          if i != 0 {
            var ref :| ref in indirectionTable.contents && indirectionTable.contents[ref].0.Some? && ref in it0.s && indirectionTable.contents[ref].0.value.addr as int == i * NodeBlockSize() as int;
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
            var ref := it.next.key;
            assert indirectionTable.t.contents[ref].loc.Some?;
            assert ref in it0.s;
            assert indirectionTable.t.contents[ref] == it.next.value;
            assert indirectionTable.t.contents[ref].loc.value.addr as int == i * NodeBlockSize() as int;

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
                var j1 := DiskLayout.ValidNodeAddrDivisor(I(indirectionTable).locs[r1].addr);
                var j2 := DiskLayout.ValidNodeAddrDivisor(I(indirectionTable).locs[r2].addr);
                if r1 !in it.s {
                  assert r2 in it.s;
                  assert !BitmapModel.IsSet(bm, j1);
                  assert IsLocAllocBitmap(bm, j2);
                  assert BitmapModel.IsSet(bm, j2);
                  assert false;
                } else {
                  assert r1 in it.s;
                  assert !BitmapModel.IsSet(bm, j2);
                  assert IsLocAllocBitmap(bm, j1);
                  assert BitmapModel.IsSet(bm, j1);
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

  lemma BitmapInitUpToIterateResult(bm: BitmapModel.BitmapModelT, i: uint64, upTo: uint64, j: uint64)
  requires 0 <= i as int <= upTo as int <= BitmapModel.Len(bm)
  requires 0 <= j as int < BitmapModel.Len(bm)
  ensures var bm' := BitmapInitUpToIterate(bm, i, upTo);
    && BitmapModel.Len(bm') == BitmapModel.Len(bm)
    && (i <= j < upTo ==> BitmapModel.IsSet(bm', j as int))
    && (!(i <= j < upTo) ==> BitmapModel.IsSet(bm', j as int) == BitmapModel.IsSet(bm, j as int))
  decreases upTo - i
  {
    BitmapModel.reveal_BitSet();
    BitmapModel.reveal_IsSet();
    if i == upTo {
    } else {
      BitmapInitUpToIterateResult(BitmapModel.BitSet(bm, i as int), i+1, upTo, j);
    }
  }

  lemma BitmapInitUpToResult(bm: BitmapModel.BitmapModelT, upTo: uint64, j: uint64)
  requires upTo as int <= BitmapModel.Len(bm)
  requires 0 <= j as int < BitmapModel.Len(bm)
  ensures var bm' := BitmapInitUpTo(bm, upTo);
    && BitmapModel.Len(bm') == BitmapModel.Len(bm)
    && (j < upTo ==> BitmapModel.IsSet(bm', j as int))
    && (j >= upTo ==> BitmapModel.IsSet(bm', j as int) == BitmapModel.IsSet(bm, j as int))
  {
    reveal_BitmapInitUpTo();
    BitmapInitUpToIterateResult(bm, 0, upTo, j);
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
    BitmapModel.reveal_BitSet();
    BitmapModel.reveal_IsSet();

    var it := MutableMapModel.IterStart(indirectionTable.t);

    var bm := BitmapModel.EmptyBitmap(NumBlocks());
    var bm' := BitmapInitUpTo(bm, MinNodeBlockIndexUint64());

    forall i: int | IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s)
    ensures IsLocAllocBitmap(bm', i)
    {
      BitmapInitUpToResult(bm, MinNodeBlockIndexUint64(), i as uint64);
      assert i < MinNodeBlockIndex();
      assert BitmapModel.IsSet(bm', i);
    }

    forall i: int | IsLocAllocBitmap(bm', i)
    ensures IsLocAllocIndirectionTablePartial(indirectionTable, i, it.s)
    {
      BitmapInitUpToResult(bm, MinNodeBlockIndexUint64(), i as uint64);
      assert i < MinNodeBlockIndex();
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

  function {:opaque} FindDeallocable(self: IndirectionTable)
  : (ref: Option<BT.G.Reference>)
  requires Inv(self)
  requires TrackingGarbage(self)
  {
    LruModel.NextOpt(self.garbageQueue.value)
  }

  lemma FindDeallocableCorrect(self: IndirectionTable)
  requires Inv(self)
  requires TrackingGarbage(self)
  ensures var ref := FindDeallocable(self);
      && (ref.Some? ==> ref.value in I(self).graph)
      && (ref.Some? ==> deallocable(self, ref.value))
      && (ref.None? ==> forall r | r in I(self).graph :: !deallocable(self, r))
  {
    reveal_FindDeallocable();
    var ref := FindDeallocable(self);
    if ref.None? {
      forall r | r in I(self).graph ensures !deallocable(self, r)
      {
        assert self.t.contents[r].predCount != 0;
        if r == BT.G.Root() {
          assert !deallocable(self, r);
        } else {
          assert |PredecessorSet(self.graph, r)| > 0;
          assert PredecessorSet(self.graph, r) != {};
          var y : PredecessorEdge :| y in PredecessorSet(self.graph, r);
          assert y.src in I(self).graph;
          assert r in I(self).graph[y.src];
          assert !deallocable(self, r);
        }
      }
    } else {
      assert ref.value in PredCounts(self.t);
      assert self.predCounts[ref.value] == |PredecessorSet(self.graph, ref.value)| + IsRoot(ref.value);
      assert self.t.contents[ref.value].predCount == 0;
      forall r | r in I(self).graph ensures ref.value !in I(self).graph[r]
      {
        if ref.value in I(self).graph[r] {
          var i :| 0 <= i < |I(self).graph[r]| && I(self).graph[r][i] == ref.value;
          assert PredecessorEdge(r, i) in PredecessorSet(self.graph, ref.value);
        }
      }
    }
  }

  lemma LemmaRemoveRefStuff(self: IndirectionTable, ref: BT.G.Reference)
  requires Inv(self)
  requires TrackingGarbage(self)
  requires ref in self.t.contents
  requires deallocable(self, ref)
  requires self.t.count as nat < 0x1_0000_0000_0000_0000 / 8 - 1;
  ensures
    var (t, oldEntry) := MutableMapModel.RemoveAndGet(self.t, ref);
    var q := LruModel.Remove(self.garbageQueue.value, ref);
    RefcountUpdateInv(t, q, ref, [], oldEntry.value.succs, 0, 0)
  {
    var (t, oldEntry) := MutableMapModel.RemoveAndGet(self.t, ref);

    LruModel.LruRemove(self.garbageQueue.value, ref);

    assert |Graph(self.t)[ref]| <= MaxNumChildren();

    forall ref | ref in Graph(t)
    ensures |Graph(t)[ref]| <= MaxNumChildren()
    {
      assert Graph(t)[ref] == Graph(self.t)[ref];
    }

    var graph0 := Graph(self.t);
    var graph1 := Graph(t);
    var succs0 := Graph(self.t)[ref];
    var succs1 := [];
    var predCounts1 := PredCounts(t);
    forall r | r in predCounts1
    ensures predCounts1[r] == |PredecessorSet(graph1, r)| + IsRoot(r)
          - SeqCount(succs1, r, 0)
          + SeqCount(succs0, r, 0)
    {
      SeqCountPlusPredecessorSetExcept(graph0, r, ref);
      SeqCountPlusPredecessorSetExcept(graph1, r, ref);

      assert PredecessorSetExcept(graph0, r, ref)
          == PredecessorSetExcept(graph1, r, ref);
    }
    assert ValidPredCountsIntermediate(PredCounts(t), Graph(t), [], succs0, 0, 0);

    forall j | 0 <= j < |succs0|
    ensures succs0[j] in t.contents
    {
      if succs0[j] == ref {
        assert ref in I(self).graph[ref];
        assert false;
      }
      assert succs0[j] == self.t.contents[ref].succs[j];
      assert succs0[j] in self.t.contents[ref].succs;
      assert succs0[j] in self.t.contents;
    }

    forall r, succ | r in Graph(t) && succ in Graph(t)[r]
    ensures succ in Graph(t)
    {
      if succ == ref {
        assert ref in I(self).graph[r];
        assert false;
      }
      assert succ in Graph(self.t)[r];
      assert succ in Graph(self.t);
    }
  }

  function {:opaque} RemoveRef(self: IndirectionTable, ref: BT.G.Reference)
    : (res : (IndirectionTable, Option<Location>))
  requires Inv(self)
  requires TrackingGarbage(self)
  requires deallocable(self, ref)
  ensures var (self', oldLoc) := res;
    && Inv(self')
    && TrackingGarbage(self')
    && self'.graph == MapRemove1(self.graph, ref)
    && self'.locs == MapRemove1(self.locs, ref)
    && (ref in self.locs ==> oldLoc == Some(self.locs[ref]))
    && (ref !in self.locs ==> oldLoc == None)
  {
    lemma_count_eq_graph_size(self.t);

    LemmaRemoveRefStuff(self, ref);

    var (t, oldEntry) := MutableMapModel.RemoveAndGet(self.t, ref);
    var q := LruModel.Remove(self.garbageQueue.value, ref);
    var (t1, q1) := UpdatePredCountsInc(t, q, ref, [], oldEntry.value.succs, 0);

    lemma_count_eq_graph_size(t);
    lemma_count_eq_graph_size(t1);

    LemmaValidPredCountsOfValidPredCountsIntermediate(PredCounts(t1), Graph(t1), [], oldEntry.value.succs);

    var self' := FromHashMap(t1, Some(q1), self.refUpperBound, None);
    var oldLoc := if oldEntry.Some? then oldEntry.value.loc else None;
    assert self'.graph == MapRemove1(self.graph, ref);
    (self', oldLoc)
  }

  // When we clone an ephemeral indirection table to a frozen one, we don't need
  // to clone the garbageQueue.
  function {:opaque} clone(self: IndirectionTable) : (self' : IndirectionTable)
  requires Inv(self)
  ensures Inv(self')
  ensures self'.graph == self.graph
  ensures self'.locs == self.locs
  {
    FromHashMap(self.t, None, self.refUpperBound, None)
  }

  function FindRefWithNoLocIterate(
      self: IndirectionTable,
      it: MutableMapModel.SimpleIterator)
     : (res: (IndirectionTable, Option<BT.G.Reference>))
  requires Inv(self)
  requires MutableMapModel.WFSimpleIter(self.t, it)
  requires forall r | r in it.s :: r in self.locs
  decreases it.decreaser
  ensures var (self', ref) := res;
    && Inv(self')
    && self'.locs == self.locs
    && self'.graph == self.graph
    && (ref.Some? ==> ref.value in self.graph)
    && (ref.Some? ==> ref.value !in self.locs)
    && (ref.None? ==> forall r | r in self.graph && r !in it.s :: r in self.locs)
  {
    var next := MutableMapModel.SimpleIterOutput(self.t, it);
    if next.Next? then (
      if next.value.loc.None? then (
        var self' := self.(findLoclessIterator := Some(it));
        (self', Some(next.key))
      ) else (
        FindRefWithNoLocIterate(self,
            MutableMapModel.SimpleIterInc(self.t, it))
      )
    ) else (
      var self' := self.(findLoclessIterator := Some(it));
      (self', None)
    )
  }

  function {:opaque} FindRefWithNoLoc(self: IndirectionTable) : (res: (IndirectionTable, Option<BT.G.Reference>))
  requires Inv(self)
  ensures var (self', ref) := res;
    && Inv(self')
    && self'.locs == self.locs
    && self'.graph == self.graph
    && (ref.Some? ==> ref.value in self.graph)
    && (ref.Some? ==> ref.value !in self.locs)
    && (ref.None? ==> forall r | r in self.graph :: r in self.locs)
  {
    var it := if self.findLoclessIterator.Some? then (
      self.findLoclessIterator.value
    ) else (
      MutableMapModel.SimpleIterStart(self.t)
    );
    FindRefWithNoLocIterate(self, it)
  }

  function {:opaque} ConstructorRootOnly(loc: Location) : (self' : IndirectionTable)
  ensures Inv(self')
  ensures self'.graph == map[BT.G.Root() := []]
  ensures self'.locs == map[BT.G.Root() := loc]
  {
    var t0 := MutableMapModel.Constructor(128);
    var t1 := MutableMapModel.Insert(t0, BT.G.Root(),
        Entry(Some(loc), [], 1));
    var self' := FromHashMap(t1, None, BT.G.Root(), None);

    self'
  }

  function {:opaque} getRefUpperBound(self: IndirectionTable) : (r: uint64)
  requires Inv(self)
  ensures forall ref | ref in self.graph :: ref <= r
  {
    self.refUpperBound
  }
}
