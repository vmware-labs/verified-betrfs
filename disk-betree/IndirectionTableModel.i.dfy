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
  import SetBijectivity

  datatype Entry = Entry(loc: Option<BC.Location>, succs: seq<BT.G.Reference>, predCount: uint64)
  type HashMap = MutableMapModel.LinearHashMap<Entry>

  // TODO move bitmap in here?
  datatype IndirectionTable = IndirectionTable(
    t: HashMap,
    garbageQueue: LruModel.LruQueue,

    // These are for easy access in proof code, but all the relevant data
    // is contained in the `t: HashMap` field.
    ghost locs: map<BT.G.Reference, BC.Location>,
    ghost graph: map<BT.G.Reference, seq<BT.G.Reference>>,
    ghost predCounts: map<BT.G.Reference, int>
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

  protected predicate Inv(self: IndirectionTable)
  ensures Inv(self) ==> (forall ref | ref in self.locs :: ref in self.graph)
  {
    Inv1(self)
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
    && LruModel.WF(self.garbageQueue)
    && (forall ref | ref in self.t.contents && self.t.contents[ref].predCount == 0 :: ref in LruModel.I(self.garbageQueue))
    && (forall ref | ref in LruModel.I(self.garbageQueue) :: ref in self.t.contents && self.t.contents[ref].predCount == 0)
    && BT.G.Root() in self.t.contents
  }

  lemma reveal_Inv(self: IndirectionTable)
  ensures Inv(self) == Inv1(self)
  {
  }

  function IHashMap(m: HashMap) : BC.IndirectionTable
  {
    BC.IndirectionTable(Locs(m), Graph(m))
  }

  function I(self: IndirectionTable) : BC.IndirectionTable
  {
    BC.IndirectionTable(self.locs, self.graph)
  }

  function FromHashMap(m: HashMap, q: LruModel.LruQueue) : IndirectionTable
  {
    IndirectionTable(m, q, Locs(m), Graph(m), PredCounts(m))
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
    assume self.t.count as nat < 0x1_0000_0000_0000_0000 / 8;
    var oldEntry := MutableMapModel.Get(self.t, ref);
    var t := (if oldEntry.Some? then
      MutableMapModel.Insert(self.t, ref, Entry(None, oldEntry.value.succs, oldEntry.value.predCount))
    else
      self.t);

    assert Graph(t) == Graph(self.t);
    assert PredCounts(t) == PredCounts(self.t);

    FromHashMap(t, self.garbageQueue)
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
    assume self.t.count as nat < 0x1_0000_0000_0000_0000 / 8;
    var oldEntry := MutableMapModel.Get(self.t, ref);
    var added := oldEntry.Some? && oldEntry.value.loc.None?;
    var t := (if added then
      MutableMapModel.Insert(self.t, ref, Entry(Some(loc), oldEntry.value.succs, oldEntry.value.predCount))
    else
      self.t);

    assert Graph(t) == Graph(self.t);
    assert PredCounts(t) == PredCounts(self.t);

    (FromHashMap(t, self.garbageQueue), added)
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
    && t.count as nat < 0x1_0000_0000_0000_0000 / 8
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
  {
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

      assume t.contents[newSuccs[idx]].predCount < 0xffff_ffff_ffff_ffff;

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

  function UpdatePredCountsInc(
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

  lemma LemmaUpdateAndRemoveLocStuff(self: IndirectionTable, ref: BT.G.Reference, succs: seq<BT.G.Reference>)
  requires Inv(self)
  requires |succs| <= MaxNumChildren()
  requires SuccsValid(succs, self.graph)
  requires self.t.count as nat < 0x1_0000_0000_0000_0000 / 8 - 1;
  ensures
    var oldEntry := MutableMapModel.Get(self.t, ref);
    var predCount := if oldEntry.Some? then oldEntry.value.predCount else 0;
    var t := MutableMapModel.Insert(self.t, ref, Entry(None, succs, predCount));
    var q := if oldEntry.Some? then self.garbageQueue else LruModel.Use(self.garbageQueue, ref);
    RefcountUpdateInv(t, q, ref, succs,
        if oldEntry.Some? then oldEntry.value.succs else [], 0, 0)
  {
    var oldEntry := MutableMapModel.Get(self.t, ref);
    var predCount := if oldEntry.Some? then oldEntry.value.predCount else 0;
    var t := MutableMapModel.Insert(self.t, ref, Entry(None, succs, predCount));
    var q := if oldEntry.Some? then self.garbageQueue else LruModel.Use(self.garbageQueue, ref);

    LruModel.LruUse(self.garbageQueue, ref);

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

  function {:opaque} UpdateAndRemoveLoc(self: IndirectionTable, ref: BT.G.Reference, succs: seq<BT.G.Reference>) : (res : (IndirectionTable, Option<BC.Location>))
  requires Inv(self)
  requires |succs| <= MaxNumChildren()
  requires SuccsValid(succs, self.graph)
  ensures var (self', oldLoc) := res;
    && Inv(self')
    && self'.locs == MapRemove1(self.locs, ref)
    && self'.graph == self.graph[ref := succs]
    && (oldLoc.None? ==> ref !in self.locs)
    && (oldLoc.Some? ==> ref in self.locs && self.locs[ref] == oldLoc.value)
  {
    assume self.t.count as nat < 0x1_0000_0000_0000_0000 / 8 - 1;
    LemmaUpdateAndRemoveLocStuff(self, ref, succs);

    var oldEntry := MutableMapModel.Get(self.t, ref);
    var predCount := if oldEntry.Some? then oldEntry.value.predCount else 0;
    var q := if oldEntry.Some? then self.garbageQueue else LruModel.Use(self.garbageQueue, ref);
    var t := MutableMapModel.Insert(self.t, ref, Entry(None, succs, predCount));

    var (t1, garbageQueue1) := UpdatePredCountsInc(t, q, ref, succs,
        if oldEntry.Some? then oldEntry.value.succs else [], 0);

    LemmaValidPredCountsOfValidPredCountsIntermediate(PredCounts(t1), Graph(t1), succs,
        if oldEntry.Some? then oldEntry.value.succs else []);

    var self' := FromHashMap(t1, garbageQueue1);
    var oldLoc := if oldEntry.Some? && oldEntry.value.loc.Some? then oldEntry.value.loc else None;
    (self', oldLoc)
  }

  ////// Parsing stuff

  function ComputeRefCountsEntryIterate(t: HashMap, succs: seq<BT.G.Reference>, i: uint64) : (t' : Option<HashMap>)
  requires MutableMapModel.Inv(t)
  requires 0 <= i as int <= |succs|
  requires |succs| <= MaxNumChildren()
  requires t.count as int <= NumBlocks()
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
    && (forall ref | ref in copy.contents :: t.contents[ref].predCount as int == |PredecessorSetRestricted(Graph(copy), ref, it.s)|)
    && (forall ref | ref in copy.contents :: |copy.contents[ref].succs| <= MaxNumChildren())
    && (forall ref | ref in t.contents :: ref in copy.contents)
    && GraphClosedRestricted(Graph(copy), it.s)
    && (t.count == copy.count)
    && (t.count as int <= NumBlocks())
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
  requires it.next.Some?
  requires MutableMapModel.Inv(t)
  requires MutableMapModel.Inv(copy)
  requires MutableMapModel.WFIter(copy, it)
  requires (forall ref | ref in t.contents :: ref in copy.contents)
  requires (forall ref | ref in copy.contents :: ref in t.contents)
  requires (forall ref | ref in copy.contents :: t.contents[ref].succs == copy.contents[ref].succs)
  requires (forall ref | ref in t.contents :: t.contents[ref].loc == copy.contents[ref].loc)
  requires t.count == copy.count
  requires ComputeRefCountsEntryIterate.requires(t, copy.contents[it.next.value.0].succs, i)
  requires forall ref | ref in t.contents :: t.contents[ref].predCount as int == |PredecessorSetRestrictedPartial(Graph(copy), ref, it.s, it.next.value.0, i as int)|
  ensures var t' := ComputeRefCountsEntryIterate(t, copy.contents[it.next.value.0].succs, i);
    && (t'.Some? ==>
      && MutableMapModel.Inv(t'.value)
      && (forall ref | ref in t'.value.contents :: t'.value.contents[ref].predCount as int == |PredecessorSetRestricted(Graph(copy), ref, it.s + {it.next.value.0})|)
      && (forall ref | ref in t'.value.contents :: ref in copy.contents)
      && (forall ref | ref in copy.contents :: ref in t'.value.contents)
      && (forall ref | ref in t'.value.contents :: t'.value.contents[ref].loc == copy.contents[ref].loc)
      && (forall ref | ref in t'.value.contents :: t'.value.contents[ref].succs == copy.contents[ref].succs)
      && t'.value.count == copy.count
    )
    && (t'.None? ==> !BC.GraphClosed(Graph(copy)))
  decreases |copy.contents[it.next.value.0].succs| - i as int
  {
    var succs := copy.contents[it.next.value.0].succs;
    if i == |succs| as uint64 {
      forall ref | ref in t.contents
      ensures t.contents[ref].predCount as int == |PredecessorSetRestricted(Graph(copy), ref, it.s + {it.next.value.0})|
      {
        assert PredecessorSetRestricted(Graph(copy), ref, it.s + {it.next.value.0}) == PredecessorSetRestrictedPartial(Graph(copy), ref, it.s, it.next.value.0, i as int);
      }
    } else {
      var ref := succs[i];
      var oldEntry := MutableMapModel.Get(t, ref);
      if oldEntry.Some? {
        var newEntry := oldEntry.value.(predCount := oldEntry.value.predCount + 1);
        var t0 := MutableMapModel.Insert(t, ref, newEntry);

        forall r | r in t0.contents
        ensures t0.contents[r].predCount as int == |PredecessorSetRestrictedPartial(Graph(copy), r, it.s, it.next.value.0, (i+1) as int)|
        {
          if r == ref {
            LemmaPredecessorSetRestrictedPartialAdd1Self(Graph(copy), r, it.s, it.next.value.0, i as int);
          } else {
            LemmaPredecessorSetRestrictedPartialAdd1Other(Graph(copy), r, it.s, it.next.value.0, i as int);
          }
        }

        LemmaComputeRefCountsEntryIterateCorrectPartial(t0, copy, it, i+1);
      } else {
        //assert it.next.value.0 in Graph(copy);
        assert ref in Graph(copy)[it.next.value.0];
      }
    }
  }

lemma LemmaComputeRefCountsEntryIterateGraphClosed(t: HashMap, copy: HashMap, it: MutableMapModel.Iterator<Entry>, i: uint64)
  requires it.next.Some?
  requires MutableMapModel.Inv(t)
  requires MutableMapModel.Inv(copy)
  requires MutableMapModel.WFIter(copy, it)
  requires ComputeRefCountsEntryIterate.requires(t, copy.contents[it.next.value.0].succs, i)
  requires (forall ref | ref in t.contents :: ref in copy.contents)
  requires (forall ref | ref in copy.contents :: ref in t.contents)
  requires (forall ref | ref in copy.contents :: t.contents[ref].succs == copy.contents[ref].succs)
  requires GraphClosedRestrictedPartial(Graph(copy), it.s, it.next.value.0, i as int)
  ensures var t' := ComputeRefCountsEntryIterate(t, copy.contents[it.next.value.0].succs, i);
    && (t'.Some? ==>
      && GraphClosedRestricted(Graph(copy), it.s + {it.next.value.0})
    )
  decreases |copy.contents[it.next.value.0].succs| - i as int
  {
    var succs := copy.contents[it.next.value.0].succs;
    if i == |succs| as uint64 {
      /*var graph := Graph(copy);
      var domain := it.s + {it.next.value.0};
      forall ref | ref in graph && ref in domain
      ensures forall j | 0 <= j < |graph[ref]| :: graph[ref][j] in graph
      {
        forall j | 0 <= j < |graph[ref]|
        ensures graph[ref][j] in graph
        {
          if ref == it.next.value.0 {
            assert j < i as int;
            assert forall j | 0 <= j < i as int :: graph[it.next.value.0][j] in graph;
            assert graph[it.next.value.0][j] in graph;
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
        ensures graph[it.next.value.0][k] in graph
        {
          if k == i {
            assert graph[it.next.value.0][k] in graph;
          } else {
            assert Graph(copy)[it.next.value.0][k] in Graph(copy);
            assert graph[it.next.value.0][k] in graph;
          }
        }
        LemmaComputeRefCountsEntryIterateGraphClosed(t0, copy, it, i+1);
      } else {
        //assert it.next.value.0 in Graph(copy);
        assert ref in Graph(copy)[it.next.value.0];
      }
    }
  }

  lemma LemmaComputeRefCountsEntryIterateCorrect(t: HashMap, copy: HashMap, it: MutableMapModel.Iterator<Entry>)
  requires it.next.Some?
  requires ComputeRefCountsIterateInv(t, copy, it)
  requires ComputeRefCountsEntryIterate.requires(t, copy.contents[it.next.value.0].succs, 0)
  requires forall ref | ref in t.contents :: t.contents[ref].predCount as int == |PredecessorSetRestricted(Graph(copy), ref, it.s)|
  ensures var t' := ComputeRefCountsEntryIterate(t, copy.contents[it.next.value.0].succs, 0);
    && (t'.Some? ==>
      && MutableMapModel.Inv(t'.value)
      && (forall ref | ref in t'.value.contents :: t'.value.contents[ref].predCount as int == |PredecessorSetRestricted(Graph(copy), ref, it.s + {it.next.value.0})|)
      && (forall ref | ref in t'.value.contents :: ref in copy.contents)
      && (forall ref | ref in copy.contents :: ref in t'.value.contents)
      && (forall ref | ref in t'.value.contents :: t'.value.contents[ref].loc == t.contents[ref].loc)
      && (forall ref | ref in t'.value.contents :: t'.value.contents[ref].succs == t.contents[ref].succs)
      && t'.value.count == copy.count
      && GraphClosedRestricted(Graph(copy), it.s + {it.next.value.0})
    )
    && (t'.None? ==> !BC.GraphClosed(Graph(copy)))
  {
    forall ref | ref in t.contents
    ensures t.contents[ref].predCount as int == |PredecessorSetRestrictedPartial(Graph(copy), ref, it.s, it.next.value.0, 0)|
    {
      assert PredecessorSetRestrictedPartial(Graph(copy), ref, it.s, it.next.value.0, 0)
          == PredecessorSetRestricted(Graph(copy), ref, it.s);
    }
    LemmaComputeRefCountsEntryIterateCorrectPartial(t, copy, it, 0);
    LemmaComputeRefCountsEntryIterateGraphClosed(t, copy, it, 0);
  }

  lemma LemmaComputeRefCountsIterateStuff(t: HashMap, copy: HashMap, it: MutableMapModel.Iterator<Entry>)
  requires ComputeRefCountsIterateInv(t, copy, it)
  ensures forall ref | ref in t.contents :: t.contents[ref].predCount as int <= 0x1_0000_0000_0000
  ensures it.next.Some? ==>
    var succs := it.next.value.1.succs;
    var t0 := ComputeRefCountsEntryIterate(t, succs, 0);
    && (t0.Some? ==> ComputeRefCountsIterateInv(t0.value, copy, MutableMapModel.IterInc(copy, it)))
    && (t0.None? ==> !BC.GraphClosed(Graph(copy)))
  {
    assume forall ref | ref in t.contents :: t.contents[ref].predCount as int <= 0x1_0000_0000_0000;
    if it.next.Some? {
      assert |copy.contents[it.next.value.0].succs| <= MaxNumChildren();
      LemmaComputeRefCountsEntryIterateCorrect(t, copy, it);
    }
  }

  lemma LemmaComputeRefCountsIterateValidPredCounts(
    t: HashMap, copy: HashMap, it: MutableMapModel.Iterator<Entry>)
  requires ComputeRefCountsIterateInv(t, copy, it)
  ensures it.next.None? ==> ValidPredCounts(PredCounts(t), Graph(t))
  {
    if it.next.None? {
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
  ensures t'.Some? ==> MutableMapModel.Inv(t'.value)
  ensures t'.Some? <==> BC.GraphClosed(Graph(copy))
  ensures t'.Some? ==> Graph(copy) == Graph(t'.value)
  ensures t'.Some? ==> Locs(copy) == Locs(t'.value)
  ensures t'.Some? ==> ValidPredCounts(PredCounts(t'.value), Graph(t'.value))
  decreases it.decreaser
  {
    LemmaComputeRefCountsIterateStuff(t, copy, it);
    LemmaComputeRefCountsIterateValidPredCounts(t, copy, it);

    if it.next.None? then (
      Some(t)
    ) else (
      var succs := it.next.value.1.succs;
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
  requires t.count as int <= NumBlocks()
  ensures ComputeRefCountsIterateInv(t, t, MutableMapModel.IterStart(t))
  {
    var it := MutableMapModel.IterStart(t);
    forall ref | ref in t.contents
    ensures t.contents[ref].predCount as int
        == |PredecessorSetRestricted(Graph(t), ref, it.s)|
    {
      assert PredecessorSetRestricted(Graph(t), ref, it.s) == {};
    }
  }

  function ComputeRefCounts(t: HashMap) : (t' : Option<HashMap>)
  requires MutableMapModel.Inv(t)
  requires forall ref | ref in t.contents :: t.contents[ref].predCount == 0
  requires forall ref | ref in t.contents :: |t.contents[ref].succs| <= MaxNumChildren()
  requires t.count as int <= NumBlocks()
  ensures BC.GraphClosed(Graph(t)) <==> t'.Some?
  ensures t'.Some? ==> Graph(t) == Graph(t'.value)
  ensures t'.Some? ==> Locs(t) == Locs(t'.value)
  ensures t'.Some? ==> ValidPredCounts(PredCounts(t'.value), Graph(t'.value))
  {
    LemmaComputeRefCountsIterateInvInit(t);

    ComputeRefCountsIterate(t, t, MutableMapModel.IterStart(t))
  }

  function {:fuel ValInGrammar,3} valToHashMap(a: seq<V>) : (s : Option<HashMap>)
  requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GTuple([GUint64, GUint64, GUint64, GUint64Array]))
  ensures s.Some? ==> forall v | v in s.value.contents.Values :: v.loc.Some? && BC.ValidLocationForNode(v.loc.value)
  ensures s.Some? ==> forall ref | ref in s.value.contents :: s.value.contents[ref].predCount == 0
  ensures s.Some? ==> forall ref | ref in s.value.contents :: |s.value.contents[ref].succs| <= MaxNumChildren()
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
              if ref in table.contents || lba == 0 || !LBAType.ValidLocation(loc) || |succs| as int > MaxNumChildren() then (
                None
              ) else (
                assume table.count as nat < 0x1_0000_0000_0000_0000 / 8;
                Some(MutableMapModel.Insert(table, ref, Entry(Some(loc), succs, 0)))
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

  function makeGarbageQueueIterate(t: HashMap, q: LruModel.LruQueue, it: MutableMapModel.Iterator<Entry>) : LruModel.LruQueue
  requires MutableMapModel.Inv(t)
  requires MutableMapModel.WFIter(t, it)
  requires LruModel.WF(q)
  decreases it.decreaser
  {
    if it.next.None? then
      q
    else (
      var q' := (if it.next.value.1.predCount == 0 then
        LruModel.LruUse(q, it.next.value.0);
        LruModel.Use(q, it.next.value.0)
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
    if it.next.None? {
    } else {
      var q' := (if it.next.value.1.predCount == 0 then
        LruModel.LruUse(q, it.next.value.0);
        LruModel.Use(q, it.next.value.0)
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

  function valToIndirectionTable(v: V) : (s : Option<IndirectionTable>)
  requires ValInGrammar(v, IndirectionTableGrammar())
  ensures s.Some? ==> Inv(s.value)
  ensures s.Some? ==> BC.WFCompleteIndirectionTable(I(s.value))
  {
    var t := valToHashMap(v.a);
    match t {
      case Some(t) => (
        if BT.G.Root() in t.contents
            && t.count <= NumBlocksUint64() then (
          var t1 := ComputeRefCounts(t);
          if t1.Some? then (
            lemmaMakeGarbageQueueCorrect(t1.value);
            var res := FromHashMap(t1.value, makeGarbageQueue(t1.value));
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

  function {:opaque} FindDeallocable(self: IndirectionTable)
  : (ref: Option<BT.G.Reference>)
  requires Inv(self)
  {
    LruModel.NextOpt(self.garbageQueue)
  }

  lemma FindDeallocableCorrect(self: IndirectionTable)
  requires Inv(self)
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
      }
    }
  }

  lemma LemmaRemoveRefStuff(self: IndirectionTable, ref: BT.G.Reference)
  requires Inv(self)
  requires ref in self.t.contents
  requires deallocable(self, ref)
  requires self.t.count as nat < 0x1_0000_0000_0000_0000 / 8 - 1;
  ensures
    var (t, oldEntry) := MutableMapModel.RemoveAndGet(self.t, ref);
    var q := LruModel.Remove(self.garbageQueue, ref);
    RefcountUpdateInv(t, q, ref, [], oldEntry.value.succs, 0, 0)
  {
    var (t, oldEntry) := MutableMapModel.RemoveAndGet(self.t, ref);

    LruModel.LruRemove(self.garbageQueue, ref);

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
    ensures predCounts1[r] == |PredecessorSet(graph1, r)|
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
    : (res : (IndirectionTable, Option<BC.Location>))
  requires Inv(self)
  requires deallocable(self, ref)
  ensures var (self', oldLoc) := res;
    && Inv(self')
    && self'.graph == MapRemove1(self.graph, ref)
    && self'.locs == MapRemove1(self.locs, ref)
    && (ref in self.locs ==> oldLoc == Some(self.locs[ref]))
    && (ref !in self.locs ==> oldLoc == None)
  {
    assume self.t.count as nat < 0x1_0000_0000_0000_0000 / 8 - 1;

    LemmaRemoveRefStuff(self, ref);

    var (t, oldEntry) := MutableMapModel.RemoveAndGet(self.t, ref);
    var q := LruModel.Remove(self.garbageQueue, ref);
    var (t1, q1) := UpdatePredCountsInc(t, q, ref, [], oldEntry.value.succs, 0);

    LemmaValidPredCountsOfValidPredCountsIntermediate(PredCounts(t1), Graph(t1), [], oldEntry.value.succs);

    var self' := FromHashMap(t1, q1);
    var oldLoc := if oldEntry.Some? then oldEntry.value.loc else None;
    (self', oldLoc)
  }
}
