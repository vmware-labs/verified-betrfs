// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/DebugAccumulator.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../lib/Base/Sequences.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/LinearOption.i.dfy"
include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Lang/LinearMaybe.s.dfy"
include "../lib/Lang/LinearBox.i.dfy"
include "../lib/Math/Nonlinear.i.dfy"
include "../lib/Math/Math.i.dfy"
include "../lib/DataStructures/LinearMutableMap.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "../lib/DataStructures/BitmapImpl.i.dfy"
include "../lib/DataStructures/LinearUSeq.i.dfy"
include "../BlockCacheSystem/BlockCache.i.dfy"
include "../BlockCacheSystem/SectorType.i.dfy"
include "../ByteBlockCacheSystem/Marshalling.i.dfy"
//
// The heap-y implementation of IndirectionTableModel.
//

module IndirectionTable {
  import DebugAccumulator
  import opened Maps
  import opened Sets
  import opened Options
  import opened LinearOption
  import opened LinearBox
  import opened Sequences
  import opened NativeTypes
  import ReferenceType`Internal
  import SectorType
  import BT = PivotBetreeSpec`Internal
  import BC = BlockCache
  import LinearMutableMap
  import opened DiskLayout
  import opened GenericMarshalling
  import BitmapModel
  import BitmapImpl
  import opened Bounds
  import opened NativePackedInts
  import USeq
  import SetBijectivity
  import Marshalling
  import NonlinearLemmas
  import Math

  datatype Entry = Entry(loc: Option<Location>, succs: seq<BT.G.Reference>, predCount: uint64)
  type HashMap = LinearMutableMap.LinearHashMap<Entry>
  type GarbageQueue = USeq.USeq

  // == UTILS ==
  function MapLocs(t: map<uint64, Entry>) : map<BT.G.Reference, Location>

  {
    map ref | ref in t && t[ref].loc.Some? :: t[ref].loc.value
  }

  function Locs(t: HashMap) : map<BT.G.Reference, Location>
  {
    map ref | ref in t.contents && t.contents[ref].loc.Some? :: t.contents[ref].loc.value
  }

  function {:timeLimitMultiplier 8} MapGraph(t: map<uint64, Entry>) : map<BT.G.Reference, seq<BT.G.Reference>>
  {
    map ref | ref in t :: t[ref].succs
  }

  function Graph(t: HashMap) : map<BT.G.Reference, seq<BT.G.Reference>>
  {
    map ref | ref in t.contents :: t.contents[ref].succs
  }

  function {:opaque} PredCounts(t: HashMap) : (m: map<BT.G.Reference, int>)
  {
    map ref | ref in t.contents :: t.contents[ref].predCount as int
  }

  datatype PredecessorEdge = PredecessorEdge(src: BT.G.Reference, ghost idx: int)

  function {:timeLimitMultiplier 8} PredecessorSet(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference) : set<PredecessorEdge>
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

  predicate {:timeLimitMultiplier 8} GraphClosedRestricted(graph: map<BT.G.Reference, seq<BT.G.Reference>>, domain: set<BT.G.Reference>)
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

  predicate {:timeLimitMultiplier 8} ValidPredCounts(predCounts: map<BT.G.Reference, int>, graph: map<BT.G.Reference, seq<BT.G.Reference>>)
  {
    forall ref | ref in predCounts ::
        predCounts[ref] == |PredecessorSet(graph, ref)| + IsRoot(ref)
  }
  // =============

  function MaxSize() : int
  {
    IndirectionTableMaxSize()
  }

  function method {:timeLimitMultiplier 8} MaxSizeUint64() : uint64
  {
    IndirectionTableMaxSizeUint64()
  }

  // TODO move bitmap in here?
  linear datatype IndirectionTable = IndirectionTable(
    linear t: HashMap,
    linear garbageQueue: lOption<GarbageQueue>,
    refUpperBound: uint64,
    findLoclessIterator: Option<LinearMutableMap.SimpleIterator>,

    ghost locs: map<BT.G.Reference, Location>,
    ghost graph: map<BT.G.Reference, seq<BT.G.Reference>>,
    ghost predCounts: map<BT.G.Reference, int>)
  {

    // method DebugAccumulate()
    // returns (acc:DebugAccumulator.DebugAccumulator)
    // requires false
    // {
    //   acc := DebugAccumulator.EmptyAccumulator();
    //   var a := new DebugAccumulator.AccRec(t.Count, "Entry");
    //   acc := DebugAccumulator.AccPut(acc, "t", a);
    //   var r := garbageQueue.DebugAccumulate();
    //   a := new DebugAccumulator.AccRec.Index(r);
    //   acc := DebugAccumulator.AccPut(acc, "garbageQueue", a);
    // }

    function I(): SectorType.IndirectionTable
    {
      SectorType.IndirectionTable(this.locs, this.graph)
    }

    predicate {:opaque} Inv()
    ensures Inv() ==> this.locs.Keys <= this.graph.Keys
    {
      && LinearMutableMap.Inv(this.t)
      && this.locs == Locs(this.t)
      && this.graph == Graph(this.t)
      && this.predCounts == PredCounts(this.t)
      && (this.garbageQueue.lSome? ==> this.garbageQueue.value.Inv())
      && ValidPredCounts(this.predCounts, this.graph)
      && BC.GraphClosed(this.graph)
      && (forall ref | ref in this.graph :: |this.graph[ref]| <= MaxNumChildren())
      && (this.garbageQueue.lSome? ==> (
        // && (GarbageQueueInv(this.garbageQueue.value))
        && (forall ref | ref in this.t.contents && this.t.contents[ref].predCount == 0 :: ref in this.garbageQueue.value.I())
        && (forall ref | ref in this.garbageQueue.value.I() :: ref in this.t.contents && this.t.contents[ref].predCount == 0)
      ))
      && BT.G.Root() in this.t.contents
      && this.t.count as int <= MaxSize()
      && (forall ref | ref in this.graph :: ref <= this.refUpperBound)
      && (this.findLoclessIterator.Some? ==>
          && LinearMutableMap.WFSimpleIter(this.t,
              this.findLoclessIterator.value)
          && (forall r | r in this.findLoclessIterator.value.s ::
              r in this.locs)
        )
    }

    lemma UpperBounded()
    requires Inv()
    ensures (forall ref | ref in this.graph :: ref <= this.refUpperBound)
    {
      reveal Inv();
    }

    static method Alloc(loc: Location) returns (linear r: IndirectionTable)
    ensures r.Inv()
    ensures r.graph == map[BT.G.Root() := []]
    ensures r.locs == map[BT.G.Root() := loc]
    ensures r.refUpperBound ==  BT.G.Root()
    {
      linear var hashMap := LinearMutableMap.Constructor<Entry>(128);
      LinearMutableMap.Insert(inout hashMap, BT.G.Root(), Entry(Some(loc), [], 1));

      r := IndirectionTable(
        hashMap,
        lNone,
        /* refUpperBound = */ BT.G.Root(),
        /* findLoclessIterator */ None,
        /* r.locs */ Locs(hashMap),
        /* r.graph */ Graph(hashMap),
        /* r.predCounts */ PredCounts(hashMap));

      assert r.Inv() by { 
        reveal r.Inv();
        reveal_PredCounts();
      }
    }

    // Dummy constructor only used when ImplVariables is in a state with no indirection
    // table. We could use a null indirection table instead, it's just slightly more
    // annoying to do that because we'd need additional invariants.
    static method AllocEmpty() returns (linear r: IndirectionTable)
    ensures r.Inv()
    {
      linear var hashMap := LinearMutableMap.Constructor<Entry>(128);
      // This is not important, but needed to satisfy the Inv:
      LinearMutableMap.Insert(inout hashMap, BT.G.Root(), Entry(None, [], 1));

      r := IndirectionTable(
        hashMap,
        lNone,
        /* refUpperBound = */ 0,
        /* findLoclessIterator */ None,
        /* r.locs */ Locs(hashMap),
        /* r.graph */ Graph(hashMap),
        /* r.predCounts */ PredCounts(hashMap));

      assert r.Inv() by {
        reveal r.Inv();
        reveal_PredCounts();
      }
    }

    linear method Free()
    {
      linear var IndirectionTable(
        t, garbageQueue, refUpperBound, findLoclessIterator, _, _, _) := this;
      LinearMutableMap.Destructor(t);
      linear match garbageQueue {
        case lNone => {}
        case lSome(gq) => {gq.Free();}
      }
    }

    shared method Clone()
    returns (linear cloned : IndirectionTable)
    requires this.Inv()
    ensures cloned.Inv()
    ensures cloned.graph == this.graph
    ensures cloned.locs == this.locs
    ensures cloned.I() == this.I()
    {
      reveal Inv();
      shared var IndirectionTable(
        t, garbageQueue, refUpperBound, findLoclessIterator, locs, graph, predCounts) := this;
      linear var t' := LinearMutableMap.Clone(t);
      cloned := IndirectionTable(t', lNone, refUpperBound, None, locs, graph, predCounts);
    }

    shared method GetEntry(ref: BT.G.Reference) returns (e : Option<Entry>)
    requires this.Inv()
    ensures e.None? ==> ref !in this.graph
    ensures e.Some? ==> ref in this.graph
    ensures e.Some? ==> this.graph[ref] == e.value.succs
    ensures e.Some? && e.value.loc.Some? ==>
        ref in this.locs && this.locs[ref] == e.value.loc.value
    ensures ref in this.locs ==> e.Some? && e.value.loc.Some?
    {
      reveal Inv();
      e := LinearMutableMap.Get(this.t, ref);
    }

    shared method HasEmptyLoc(ref: BT.G.Reference) returns (b: bool)
    requires this.Inv()
    ensures b == (ref in this.graph && ref !in this.locs)
    {
      reveal Inv();
      var entry := LinearMutableMap.Get(this.t, ref);
      b := entry.Some? && entry.value.loc.None?;
    }

    predicate TrackingGarbage()
    {
      this.garbageQueue.lSome?
    }

    linear inout method UpdateGhost()
    ensures self == old_self.(locs := Locs(self.t), graph := Graph(self.t), predCounts := PredCounts(self.t))
    {
      inout ghost self.locs := Locs(self.t);
      inout ghost self.graph := Graph(self.t);
      inout ghost self.predCounts :=  PredCounts(self.t);
    }

    linear inout method RemoveLoc(ref: BT.G.Reference) returns (oldLoc: Option<Location>)
    requires old_self.Inv()
    requires old_self.TrackingGarbage()
    requires ref in old_self.graph
    ensures self.Inv()
    ensures self.locs == MapRemove1(old_self.locs, ref)
    ensures self.TrackingGarbage()
    ensures self.graph == old_self.graph
    ensures self.refUpperBound == old_self.refUpperBound
    ensures (oldLoc.None? ==> ref !in old_self.locs)
    ensures (oldLoc.Some? ==> ref in old_self.locs && old_self.locs[ref] == oldLoc.value)
    {
      reveal old_self.Inv();
      var it := LinearMutableMap.FindSimpleIter(self.t, ref);
      var oldEntry := LinearMutableMap.SimpleIterOutput(self.t, it);
       
      var predCount := oldEntry.value.predCount;
      var succs := oldEntry.value.succs;

      LinearMutableMap.UpdateByIter(inout self.t, it, Entry(None, succs, predCount));
      inout self.findLoclessIterator := None;
      inout self.UpdateGhost();

      oldLoc := oldEntry.value.loc;

      assert PredCounts(self.t) == PredCounts(old_self.t) by { reveal_PredCounts(); }
      assert Graph(self.t) == Graph(old_self.t);
    }

    linear inout method AddLocIfPresent(ref: BT.G.Reference, loc: Location)
    returns (added: bool)
    requires old_self.Inv()
    ensures self.Inv()
    ensures added == (ref in old_self.graph && ref !in old_self.locs)
    ensures self.graph == old_self.graph
    ensures self.refUpperBound == old_self.refUpperBound
    ensures (added ==> self.locs == old_self.locs[ref := loc])
    ensures (!added ==> self.locs == old_self.locs)
    ensures (old_self.TrackingGarbage() ==> self.TrackingGarbage())
    {
      reveal old_self.Inv();

      var it := LinearMutableMap.FindSimpleIter(self.t, ref);
      var oldEntry := LinearMutableMap.SimpleIterOutput(self.t, it);

      added := oldEntry.Next? && oldEntry.value.loc.None?;
      if added {
        LinearMutableMap.UpdateByIter(inout self.t, it, Entry(Some(loc), oldEntry.value.succs, oldEntry.value.predCount));
        inout self.UpdateGhost();
      }

      assert Graph(self.t) == Graph(old_self.t);

      assert self.Inv() by {
        reveal self.Inv();
        reveal_PredCounts();
      }
    }

    predicate DeallocableRef(ref: BT.G.Reference)
    {
      && ref in this.graph
      && ref != BT.G.Root()
      && (forall r | r in this.graph :: ref !in this.graph[r])
    }

    static lemma TCountEqGraphSize(t: HashMap)
    requires LinearMutableMap.Inv(t)
    ensures t.count as int == |Graph(t)|
    {
      assert Graph(t).Keys == t.contents.Keys;
      assert |Graph(t)|
          == |Graph(t).Keys|
          == |t.contents.Keys|
          == t.count as int;
    }

    /////// Reference count updating

    static function SeqCountSet(s: seq<BT.G.Reference>, ref: BT.G.Reference, lb: int) : set<int>
    requires 0 <= lb <= |s|
    {
      set i | lb <= i < |s| && s[i] == ref
    }

    static function SeqCount(s: seq<BT.G.Reference>, ref: BT.G.Reference, lb: int) : int
    requires 0 <= lb <= |s|
    {
      |SeqCountSet(s, ref, lb)|
    }

    static function PredecessorSetExcept(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference, except: BT.G.Reference) : set<PredecessorEdge>
    {
      set src, idx | src in graph && 0 <= idx < |graph[src]| && graph[src][idx] == dest && src != except :: PredecessorEdge(src, idx)
    }


    static lemma SeqCountPlusPredecessorSetExcept(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference, except: BT.G.Reference)
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

    static predicate ValidPredCountsIntermediate(
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

    static predicate RefcountUpdateInv(
        t: HashMap,
        garbageQueueI: seq<uint64>,
        changingRef: BT.G.Reference,
        newSuccs: seq<BT.G.Reference>,
        oldSuccs: seq<BT.G.Reference>,
        newIdx: int,
        oldIdx: int)
    {
      && LinearMutableMap.Inv(t)
      // && LruModel.WF(q)
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
      && (forall ref | ref in t.contents && t.contents[ref].predCount == 0 :: ref in Set(garbageQueueI))
      && (forall ref | ref in Set(garbageQueueI) :: ref in t.contents && t.contents[ref].predCount == 0)
      && BT.G.Root() in t.contents
    }

    linear inout method RemoveRef(ref: BT.G.Reference)
    returns (oldLoc : Option<Location>)
    requires old_self.Inv()
    requires old_self.TrackingGarbage()
    requires old_self.DeallocableRef(ref)
    ensures self.Inv()
    ensures self.TrackingGarbage()
    ensures self.graph == MapRemove1(old_self.graph, ref)
    ensures self.locs == MapRemove1(old_self.locs, ref)
    ensures (ref in old_self.locs ==> oldLoc == Some(old_self.locs[ref]))
    ensures (ref !in old_self.locs ==> oldLoc == None)
    ensures self.refUpperBound == old_self.refUpperBound
    {
      reveal old_self.Inv();
      TCountEqGraphSize(self.t);

      // == mutation ==
      var oldEntry := LinearMutableMap.RemoveAndGet(inout self.t, ref);
      // ==============
      TCountEqGraphSize(self.t);

      assert |Graph(old_self.t)[ref]| <= MaxNumChildren();

      forall ref | ref in Graph(self.t)
      ensures |Graph(self.t)[ref]| <= MaxNumChildren()
      {
        assert Graph(self.t)[ref] == Graph(old_self.t)[ref];
      }

      ghost var graph0 := Graph(old_self.t);
      ghost var graph1 := Graph(self.t);
      ghost var succs0 := Graph(old_self.t)[ref];
      ghost var succs1 := [];
      ghost var predCounts1 := PredCounts(self.t);
      forall r | r in predCounts1
      ensures predCounts1[r] == |PredecessorSet(graph1, r)| + IsRoot(r)
            - SeqCount(succs1, r, 0)
            + SeqCount(succs0, r, 0)
      {
        reveal_PredCounts();

        SeqCountPlusPredecessorSetExcept(graph0, r, ref);
        SeqCountPlusPredecessorSetExcept(graph1, r, ref);

        assert PredecessorSetExcept(graph0, r, ref)
            == PredecessorSetExcept(graph1, r, ref);
      }
      assert ValidPredCountsIntermediate(PredCounts(self.t), Graph(self.t), [], succs0, 0, 0);

      forall j | 0 <= j < |succs0|
      ensures succs0[j] in self.t.contents
      {
        if succs0[j] == ref {
          assert ref in old_self.graph[ref];
          assert false;
        }
        assert succs0[j] == old_self.t.contents[ref].succs[j];
        assert succs0[j] in old_self.t.contents[ref].succs;
        assert succs0[j] in old_self.t.contents;
      }

      forall r, succ | r in Graph(self.t) && succ in Graph(self.t)[r]
      ensures succ in Graph(self.t)
      {
        if succ == ref {
          assert ref in old_self.graph[r];
          assert false;
        }
        assert succ in Graph(old_self.t)[r];
        assert succ in Graph(old_self.t);
      }

      // == mutation ==
      inout self.garbageQueue.value.Remove(ref);
      assert self.t.count as int <= MaxSize();
      inout self.UpdatePredCounts(ref, [], oldEntry.value.succs);
      // ==============

      TCountEqGraphSize(self.t);

      oldLoc := if oldEntry.Some? then oldEntry.value.loc else None;

      // == mutation ==
      inout self.findLoclessIterator := None;
      inout self.UpdateGhost();
      // ==============

      assert self.graph == MapRemove1(old_self.graph, ref); // observe
      reveal self.Inv();
    }

    static predicate UnchangedExceptTAndGarbageQueue(old_self: IndirectionTable, self: IndirectionTable) {
      self == old_self.(t := self.t, garbageQueue := self.garbageQueue)
    }

    linear inout method PredInc(ref: BT.G.Reference)
    requires old_self.t.Inv()
    requires old_self.TrackingGarbage()
    requires old_self.garbageQueue.value.Inv()
    requires old_self.t.count as nat < 0x1_0000_0000_0000_0000 / 8
    requires ref in old_self.t.contents
    requires old_self.t.contents[ref].predCount < 0xffff_ffff_ffff_ffff
    ensures self.t.Inv()
    ensures self.TrackingGarbage()
    ensures self.garbageQueue.value.Inv()
    ensures UnchangedExceptTAndGarbageQueue(old_self, self)
    ensures (
      var oldEntry := old_self.t.contents[ref];
      self.t.contents == old_self.t.contents[ref := oldEntry.(predCount := oldEntry.predCount + 1)])
    ensures if old_self.t.contents[ref].predCount == 0
      then self.garbageQueue.value.I() == RemoveOneValue(old_self.garbageQueue.value.I(), ref)
      else self.garbageQueue.value.I() == old_self.garbageQueue.value.I()
    {
      var oldEntryOpt := LinearMutableMap.Get(self.t, ref);
      var oldEntry := oldEntryOpt.value;
      var newEntry := oldEntry.(predCount := oldEntry.predCount + 1);
      LinearMutableMap.Insert(inout self.t, ref, newEntry);
      if oldEntry.predCount == 0 {
        inout self.garbageQueue.value.Remove(ref);
      }
    }

    linear inout method PredDec(ref: BT.G.Reference)
    requires old_self.t.Inv()
    requires old_self.TrackingGarbage()
    requires old_self.garbageQueue.value.Inv()
    requires old_self.t.count as nat < 0x1_0000_0000_0000_0000 / 8
    requires ref in old_self.t.contents
    requires old_self.t.contents[ref].predCount > 0
    requires |old_self.garbageQueue.value.I()| <= 0x1_0000_0000;
    ensures self.t.Inv()
    ensures self.TrackingGarbage()
    ensures self.garbageQueue.value.Inv()
    ensures UnchangedExceptTAndGarbageQueue(old_self, self)
    ensures (
      var oldEntry := old_self.t.contents[ref];
      self.t.contents == old_self.t.contents[ref := oldEntry.(predCount := oldEntry.predCount - 1)])
    ensures if (old_self.t.contents[ref].predCount == 1 && ref !in old_self.garbageQueue.value.I())
      then self.garbageQueue.value.I() == old_self.garbageQueue.value.I() + [ref]
      else self.garbageQueue.value.I() == old_self.garbageQueue.value.I()
    {
      var oldEntryOpt := LinearMutableMap.Get(self.t, ref);
      var oldEntry := oldEntryOpt.value;
      var newEntry := oldEntry.(predCount := oldEntry.predCount - 1);
      LinearMutableMap.Insert(inout self.t, ref, newEntry);
      if oldEntry.predCount == 1 {
        inout self.garbageQueue.value.Add(ref);
      }
    }

    static lemma SeqCountLePredecessorSet(
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

    static lemma SeqCountInc(
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

    static lemma SeqCountIncOther(
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

    static lemma PredecessorSetRestrictedSizeBound(graph: map<BT.G.Reference, seq<BT.G.Reference>>,
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

      assert |PredecessorSetRestricted(graph, dest, domain)| == |s1| <= |s3| == |graph.Keys| * MaxNumChildren(); // observe
    }

    static lemma PredecessorSetSizeBound(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference)
    requires |graph| <= MaxSize()
    requires forall ref | ref in graph :: |graph[ref]| <= MaxNumChildren()
    ensures |PredecessorSet(graph, dest)| <= MaxSize() * MaxNumChildren()
    {
      PredecessorSetRestrictedSizeBound(graph, dest, graph.Keys);
      assert PredecessorSet(graph, dest) == PredecessorSetRestricted(graph, dest, graph.Keys);
    }

    static lemma SeqCountBound(s: seq<BT.G.Reference>, ref: BT.G.Reference, lb: int)
    requires 0 <= lb <= |s|
    ensures SeqCount(s, ref, lb) <= |s|
    {
      var s1 := SeqCountSet(s, ref, lb);
      var s2 := SetRange(|s|);
      assert s1 <= s2;
      SetInclusionImpliesSmallerCardinality(s1, s2);
      CardinalitySetRange(|s|);
    }

    linear inout method UpdatePredCounts(ghost changingRef: BT.G.Reference, newSuccs: seq<BT.G.Reference>, oldSuccs: seq<BT.G.Reference>)
    requires old_self.t.Inv()
    requires old_self.TrackingGarbage()
    requires old_self.garbageQueue.value.Inv()
    requires RefcountUpdateInv(old_self.t, old_self.garbageQueue.value.I(), changingRef, newSuccs, oldSuccs, 0, 0)
    ensures self.t.Inv()
    ensures self.TrackingGarbage()
    ensures self.garbageQueue.value.Inv()
    ensures RefcountUpdateInv(self.t, self.garbageQueue.value.I(), changingRef, newSuccs, oldSuccs, |newSuccs|, |oldSuccs|)
    // ?? ensures if changingRef in old_self.t.contents
    // ??   then changingRef in self.t.contents && self.t.contents[changingRef] == old_self.t.contents[changingRef]
    // ??   else changingRef !in self.t.contents
    ensures UnchangedExceptTAndGarbageQueue(old_self, self)
    ensures Graph(self.t) == Graph(old_self.t)
    ensures Locs(self.t) == Locs(old_self.t)
    {
      var idx: uint64 := 0;

      while idx < |newSuccs| as uint64
      invariant self.t.Inv()
      invariant self.TrackingGarbage()
      invariant self.garbageQueue.value.Inv()
      invariant RefcountUpdateInv(self.t, self.garbageQueue.value.I(), changingRef, newSuccs, oldSuccs, idx as int, 0)
      invariant UnchangedExceptTAndGarbageQueue(old_self, self)
      invariant Graph(self.t) == Graph(old_self.t)
      invariant Locs(self.t) == Locs(old_self.t)
      decreases |newSuccs| - idx as int
      {
        var ref := newSuccs[idx];

        ghost var graph := Graph(self.t);

        assert ref in graph;
        assert ref in self.t.contents;

        assert self.t.contents[ref].predCount as int
          == |PredecessorSet(graph, ref)| + IsRoot(ref)
            - SeqCount(newSuccs, ref, idx as nat)
            + SeqCount(oldSuccs, ref, 0) by { reveal_PredCounts(); }

        SeqCountInc(newSuccs, ref, idx as nat);
        assert SeqCount(newSuccs, ref, idx as nat + 1)
            == SeqCount(newSuccs, ref, idx as nat) - 1;

        TCountEqGraphSize(self.t);
        PredecessorSetSizeBound(graph, ref);
        SeqCountBound(oldSuccs, ref, 0);
        assert self.t.contents[ref].predCount < 0xffff_ffff_ffff_ffff;

        // ?? assert t.contents[ref].predCount != 0;
        ghost var self_before := self;

        // == mutation ==
        inout self.PredInc(ref);
        // ==============

        assert Graph(self.t) == Graph(self_before.t);

        ghost var predCounts := PredCounts(self_before.t);
        ghost var predCounts' := PredCounts(self.t);
        forall r | r in predCounts'
        ensures predCounts'[r] == |PredecessorSet(graph, r)| + IsRoot(r)
            - SeqCount(newSuccs, r, idx as nat + 1)
            + SeqCount(oldSuccs, r, 0)
        {
          reveal_PredCounts();

          if r == ref {
          } else {
            SeqCountIncOther(newSuccs, r, idx as nat);
          }
        }

        assert RefcountUpdateInv(self.t, self.garbageQueue.value.I(), changingRef, newSuccs, oldSuccs, idx as nat + 1, 0);
        // == mutation ==
        idx := idx + 1;
        // ==============

      }

      var idx2: uint64 := 0;

      while idx2 < |oldSuccs| as uint64
      invariant self.t.Inv()
      invariant self.TrackingGarbage()
      invariant self.garbageQueue.value.Inv()
      invariant RefcountUpdateInv(self.t, self.garbageQueue.value.I(), changingRef, newSuccs, oldSuccs, |newSuccs|, idx2 as int)
      invariant UnchangedExceptTAndGarbageQueue(old_self, self)
      invariant Graph(self.t) == Graph(old_self.t)
      invariant Locs(self.t) == Locs(old_self.t)
      decreases |oldSuccs| - idx2 as int
      {
        assert Set(self.garbageQueue.value.I()) <= self.t.contents.Keys;
        SetInclusionImpliesSmallerCardinality(Set(self.garbageQueue.value.I()), self.t.contents.Keys);
        NoDupesSetCardinality(self.garbageQueue.value.I());
        assert |self.t.contents.Keys| == |self.t.contents|;

        ghost var graph := Graph(self.t);

        assert oldSuccs[idx2] in graph;

        assert oldSuccs[idx2] in self.t.contents;

        ghost var ref := oldSuccs[idx2];
        assert self.t.contents[ref].predCount as int
          == |PredecessorSet(graph, ref)| + IsRoot(ref)
            - SeqCount(newSuccs, ref, |newSuccs|)
            + SeqCount(oldSuccs, ref, idx2 as nat) by {
          reveal_PredCounts();
        }

        if changingRef in graph {
          SeqCountLePredecessorSet(graph, ref, changingRef, |newSuccs|);
          assert |PredecessorSet(graph, ref)|
              >= SeqCount(graph[changingRef], ref, |newSuccs|);
        }

        SeqCountInc(oldSuccs, ref, idx2 as nat);
        assert SeqCount(oldSuccs, ref, idx2 as nat + 1)
            == SeqCount(oldSuccs, ref, idx2 as nat) - 1;

        assert self.t.contents[oldSuccs[idx2]].predCount > 0;

        ghost var self_before := self;

        // == mutation ==
        inout self.PredDec(oldSuccs[idx2]);
        // ==============

        if self_before.t.contents[ref].predCount == 1 {
          assert NoDupes([ref]) by { reveal_NoDupes(); }
          // (doc) assert self.t.contents[ref].predCount == 0;
          DisjointConcatenation(self_before.garbageQueue.value.I(), [ref]);
        }
        assert Graph(self_before.t) == Graph(self.t);

        ghost var predCounts := PredCounts(self_before.t);
        ghost var predCounts' := PredCounts(self.t);
        forall r | r in predCounts'
        ensures predCounts'[r] == |PredecessorSet(graph, r)| + IsRoot(r)
            - SeqCount(newSuccs, r, |newSuccs| as nat)
            + SeqCount(oldSuccs, r, idx2 as nat + 1)
        {
          reveal_PredCounts();
          if r == ref {
          } else {
            SeqCountIncOther(oldSuccs, r, idx2 as nat);
            assert SeqCount(oldSuccs, r, idx2 as nat) == SeqCount(oldSuccs, r, idx2 as nat + 1);
          }
        }

        // == mutation ==
        idx2 := idx2 + 1;
        // ==============
      }
    }

    static predicate SuccsValid(succs: seq<BT.G.Reference>, graph: map<BT.G.Reference, seq<BT.G.Reference>>)
    {
      forall ref | ref in succs :: ref in graph
    }

    lemma QueueSizeBound()
    requires this.Inv()
    ensures this.garbageQueue.lSome? ==>
        |this.garbageQueue.value.I()| <= 0x1_0000_0000;
    {
      reveal this.Inv();

      if this.garbageQueue.lSome? {
        NoDupesSetCardinality(this.garbageQueue.value.I());
        SetInclusionImpliesSmallerCardinality(Set(this.garbageQueue.value.I()), this.t.contents.Keys);
        assert |this.t.contents.Keys| == |this.t.contents|;
      }
    }

    linear inout method {:timeLimitMultiplier 8} UpdateAndRemoveLoc(ref: BT.G.Reference, succs: seq<BT.G.Reference>)
    returns (oldLoc : Option<Location>)
    requires old_self.Inv()
    requires old_self.TrackingGarbage()
    requires |succs| <= MaxNumChildren()
    requires |old_self.graph| < MaxSize()
    requires SuccsValid(succs, old_self.graph)
    ensures self.Inv()
    ensures self.TrackingGarbage()
    // ?? ensures |self.garbageQueue.value| <= 0x1_0000_0000;
    ensures self.Inv()
    ensures self.TrackingGarbage()
    ensures self.locs == MapRemove1(old_self.locs, ref)
    ensures self.graph == old_self.graph[ref := succs]
    ensures self.refUpperBound == if ref > old_self.refUpperBound then ref else old_self.refUpperBound
    ensures (oldLoc.None? ==> ref !in old_self.locs)
    ensures (oldLoc.Some? ==> ref in old_self.locs && old_self.locs[ref] == oldLoc.value)
    {
      reveal old_self.Inv();

      self.QueueSizeBound();
      TCountEqGraphSize(self.t);

      // TODO use the iterator instead?
      var oldEntry := LinearMutableMap.Get(self.t, ref);
      var predCount := if oldEntry.Some? then oldEntry.value.predCount else 0;

      // == mutation ==
      if oldEntry.None? {
        inout self.garbageQueue.value.Add(ref);
      }
      LinearMutableMap.Insert(inout self.t, ref, Entry(None, succs, predCount));
      // ==============

      assert oldEntry.Some? ==> oldEntry.value.succs == Graph(old_self.t)[ref];
      assert forall r | r != ref && r in Graph(self.t) :: r in Graph(old_self.t) && Graph(self.t)[r] == Graph(old_self.t)[r];

      TCountEqGraphSize(self.t);

      ghost var oldSuccs := if oldEntry.Some? then oldEntry.value.succs else [];

      ghost var predCounts := PredCounts(self.t);
      ghost var graph0 := Graph(old_self.t);
      ghost var graph := Graph(self.t);

      forall r | r in predCounts
      ensures predCounts[r] == |PredecessorSet(graph, r)| + IsRoot(r)
            - SeqCount(succs, r, 0)
            + SeqCount(oldSuccs, r, 0)
      {
        reveal_PredCounts();

        SeqCountPlusPredecessorSetExcept(graph0, r, ref);
        SeqCountPlusPredecessorSetExcept(graph, r, ref);

        assert PredecessorSetExcept(graph0, r, ref)
            == PredecessorSetExcept(graph, r, ref);

        assert |PredecessorSet(graph0, r)| - SeqCount(oldSuccs, r, 0)
          == |PredecessorSetExcept(graph0, r, ref)|
          == |PredecessorSetExcept(graph, r, ref)|
          == |PredecessorSet(graph, r)| - SeqCount(succs, r, 0);
      }

      assert ValidPredCountsIntermediate(PredCounts(self.t), Graph(self.t), succs, oldSuccs, 0, 0);

      forall j | 0 <= j < |oldSuccs|
      ensures oldSuccs[j] in self.t.contents
      {
        assert oldSuccs[j] in graph0;
        assert oldSuccs[j] in graph;
      }

      assert RefcountUpdateInv(self.t, self.garbageQueue.value.I(), ref, succs, oldSuccs, 0, 0);

      // == mutation ==
      inout self.UpdatePredCounts(ref, succs, if oldEntry.Some? then oldEntry.value.succs else []);
      // ==============

      TCountEqGraphSize(self.t);

      assert ValidPredCounts(PredCounts(self.t), Graph(self.t));

      if ref > self.refUpperBound {
        inout self.refUpperBound := ref;
      }

      oldLoc := if oldEntry.Some? && oldEntry.value.loc.Some? then oldEntry.value.loc else None;

      // == mutation ==
      inout self.findLoclessIterator := None;
      inout self.UpdateGhost();
      // ==============
      reveal self.Inv();
    }

    static predicate ValIsHashMap(a: seq<V>, s: Option<HashMap>)
    requires |a| <= MaxSize()
    requires forall i | 0 <= i < |a| :: ValidVal(a[i])
    requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GTuple([GUint64, GUint64, GUint64, GUint64Array]))
    {
      // TODO(andrea) does this need to say something about s.value.count == |s.value.contents| ?
      && ValIsMap(a, MapOption(s, (x: HashMap) => x.contents))
    }

    // // Parsing and marshalling
    static predicate ValIsMap(a: seq<V>, s: Option<map<uint64, Entry>>)
    requires |a| <= MaxSize()
    requires forall i | 0 <= i < |a| :: ValidVal(a[i])
    requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GTuple([GUint64, GUint64, GUint64, GUint64Array]))
    {
      && (s.Some? ==> |s.value| as int == |a|)
      && (s.Some? ==> forall v | v in s.value.Values :: v.loc.Some? && ValidNodeLocation(v.loc.value))
      && (s.Some? ==> forall ref | ref in s.value :: s.value[ref].predCount == 0)
      && (s.Some? ==> forall ref | ref in s.value :: |s.value[ref].succs| <= MaxNumChildren())
      && (s.Some? ==> Marshalling.valToIndirectionTableMaps(a).Some?)
      && (s.Some? ==> 
        (
          var left := Marshalling.valToIndirectionTableMaps(a).value;
          var right := IMapAsIndirectionTable(s.value);
          && left.graph == right.graph
          && left.locs == right.locs
        ))
      && (s.None? ==> Marshalling.valToIndirectionTableMaps(a).None?)
    }

    static lemma lemma_valToHashMapNonePrefix(a: seq<V>, i: int)
    requires forall i | 0 <= i < |a| :: ValidVal(a[i])
    requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GTuple([GUint64, GUint64, GUint64, GUint64Array]))
    requires 0 <= i <= |a| <= MaxSize()
    requires ValIsHashMap(a[..i], None)
    ensures ValIsHashMap(a, None)
    decreases |a| - i
    {
      if (i == |a|) {
        assert a[..i] == a;
      } else {
        assert ValIsHashMap(a[..i+1], None) by {
          assert DropLast(a[..i+1]) == a[..i];
          assert Last(a[..i+1]) == a[i];
        }
        lemma_valToHashMapNonePrefix(a, i+1);
      }
    }

    static method {:fuel ValInGrammar,3} ValToHashMap(a: seq<V>) returns (linear s : lOption<HashMap>)
    requires |a| <= MaxSize()
    requires forall i | 0 <= i < |a| :: ValidVal(a[i])
    requires forall i | 0 <= i < |a| :: ValInGrammar(a[i], GTuple([GUint64, GUint64, GUint64, GUint64Array]))
    ensures ValIsHashMap(a, s.Option())
    ensures s.lSome? ==> s.value.Inv()
    ensures s.lSome? ==> s.value.count as nat < 0x1_0000_0000_0000_0000 / 8
    {
      var i: uint64 := 0;
      var success := true;
      linear var mutMap := LinearMutableMap.Constructor<Entry>(1024); // TODO(alattuada) magic numbers

      assert Locs(mutMap) == map[]; // observe
      assert Graph(mutMap) == map[]; // observe

      while i < |a| as uint64
      invariant 0 <= i as int <= |a|
      invariant mutMap.Inv()
      invariant ValIsHashMap(a[..i], Some(mutMap))
      {
        var tuple := a[i];
        var ref := tuple.t[0 as uint64].u;
        var addr := tuple.t[1 as uint64].u;
        var len := tuple.t[2 as uint64].u;
        var succs := tuple.t[3 as uint64].ua;
        var graphRef := LinearMutableMap.Get(mutMap, ref);
        var loc := Location(addr, len);

        assert ValidVal(tuple);
        assert ValidVal(tuple.t[3]);
        assert |succs| < 0x1_0000_0000_0000_0000;

        assert DropLast(a[..i+1]) == a[..i];
        assert Last(a[..i+1]) == a[i];

        if graphRef.Some? || !ValidNodeLocation(loc)
            || |succs| as uint64 > MaxNumChildrenUint64() {
          lemma_valToHashMapNonePrefix(a, (i+1) as int);
          success := false;
          break;
        } else {
          ghost var mutMapBeforeInsert := mutMap;
          LinearMutableMap.Insert(inout mutMap, ref, Entry(Some(loc), succs, 0));
          assert Locs(mutMap) == Locs(mutMapBeforeInsert)[ref := loc];
          assert Graph(mutMap) == Graph(mutMapBeforeInsert)[ref := succs];
          i := i + 1;
        }
      }

      if success {
        assert a[..i] == a;
        s := lSome(mutMap);
      } else {
        LinearMutableMap.Destructor(mutMap);
        s := lNone;
      }
    }

    /*lemma LemmaComputeRefCountsOuterLoopInvInit(t: HashMap)
    requires LinearMutableMap.Inv(t)
    requires forall ref | ref in t.contents :: t.contents[ref].predCount == 0
    requires forall ref | ref in t.contents :: |t.contents[ref].succs| <= MaxNumChildren()
    requires t.count as int <= MaxSize()
    requires BT.G.Root() in t.contents
    ensures
      var oldEntry := t.contents[BT.G.Root()];
      var t0 := LinearMutableMap.Insert(t, BT.G.Root(), oldEntry.(predCount := 1));
      ComputeRefCountsOuterLoopInv(t0, t, LinearMutableMap.IterStart(t))
    {
    }*/

    static lemma lemma_count_eq_graph_size(t: HashMap)
    requires LinearMutableMap.Inv(t)
    ensures t.count as int == |Graph(t)|
    {
      assert Graph(t).Keys == t.contents.Keys;
      assert |Graph(t)|
          == |Graph(t).Keys|
          == |t.contents.Keys|
          == t.count as int;
    }

    static lemma RevealComputeRefCountsSharedDomainInv(tbl': HashMap, tbl: HashMap)
    requires ComputeRefCountsSharedInv(tbl', tbl)
    ensures forall ref | ref in tbl.contents :: ref in tbl'.contents
    ensures forall ref | ref in tbl'.contents :: ref in tbl.contents
    {
      reveal_ComputeRefCountsSharedInv();
    }

    static predicate {:opaque} ComputeRefCountsSharedInv(tbl': HashMap, tbl: HashMap)
    ensures ComputeRefCountsSharedInv(tbl', tbl) ==> tbl'.count as int <= MaxSize()
    {
      && (tbl'.count as int <= MaxSize())
      && (forall ref | ref in tbl.contents :: ref in tbl'.contents)
      && (forall ref | ref in tbl'.contents :: ref in tbl.contents)
      && (forall ref | ref in tbl.contents :: tbl'.contents[ref].loc == tbl.contents[ref].loc)
      && (forall ref | ref in tbl.contents :: tbl'.contents[ref].succs == tbl.contents[ref].succs)
      && (forall ref | ref in tbl.contents :: |tbl.contents[ref].succs| <= MaxNumChildren())
    }

    static predicate {:opaque} ComputeRefCountsOuterLoopInv0(tbl': HashMap, tbl: HashMap, it: LinearMutableMap.Iterator<Entry>)
    requires (forall ref | ref in tbl.contents :: ref in tbl'.contents)
    {
      && (forall ref | ref in tbl'.contents :: tbl'.contents[ref].predCount as int <= 0x1_0000_0000_0000) // ???
      && (forall ref | ref in tbl.contents :: tbl'.contents[ref].predCount as int == |PredecessorSetRestricted(Graph(tbl), ref, it.s)| + IsRoot(ref))
    }

    static predicate ComputeRefCountsOuterLoopInv(tbl': HashMap, tbl: HashMap, it: LinearMutableMap.Iterator<Entry>)
    {
      && LinearMutableMap.Inv(tbl')
      && LinearMutableMap.Inv(tbl)
      && LinearMutableMap.WFIter(tbl, it)
      && BT.G.Root() in tbl'.contents
      && ComputeRefCountsSharedInv(tbl', tbl)
      && (RevealComputeRefCountsSharedDomainInv(tbl', tbl);
          ComputeRefCountsOuterLoopInv0(tbl', tbl, it))
      && GraphClosedRestricted(Graph(tbl), it.s)
      && tbl'.count as int <= MaxSize()
      && (tbl'.count == tbl.count)
    }

    static predicate {:opaque} ComputeRefCountsInnerLoopInv0(tbl': HashMap, tbl: HashMap, it: LinearMutableMap.Iterator<Entry>, succs: seq<BT.G.Reference>, i: uint64)
    requires it.next.Next?
    requires ComputeRefCountsSharedInv(tbl', tbl)
    {
      && (forall ref | ref in tbl'.contents :: tbl'.contents[ref].predCount as int <= 0x1_0000_0000_0000 + i as int)
      && (RevealComputeRefCountsSharedDomainInv(tbl', tbl);
          forall ref | ref in tbl'.contents :: tbl'.contents[ref].loc == tbl.contents[ref].loc)
      && (forall ref | ref in tbl'.contents :: tbl'.contents[ref].predCount as int == |PredecessorSetRestrictedPartial(Graph(tbl), ref, it.s, it.next.key, i as int)| + IsRoot(ref))
    }

    static predicate ComputeRefCountsInnerLoopInv(tbl': HashMap, tbl: HashMap, it: LinearMutableMap.Iterator<Entry>, succs: seq<BT.G.Reference>, i: uint64)
    requires it.next.Next?
    {
      && LinearMutableMap.Inv(tbl')
      && LinearMutableMap.Inv(tbl)
      && LinearMutableMap.WFIter(tbl, it)
      && 0 <= i as int <= |succs|
      && |succs| <= MaxNumChildren()
      && (tbl'.count == tbl.count)
      && BT.G.Root() in tbl'.contents
      && ComputeRefCountsSharedInv(tbl', tbl)
      && (RevealComputeRefCountsSharedDomainInv(tbl', tbl);
          ComputeRefCountsInnerLoopInv0(tbl', tbl, it, succs, i))
      && succs == Graph(tbl)[it.next.key]
      && GraphClosedRestrictedPartial(Graph(tbl), it.s, it.next.key, i as int)
    }

    static lemma ComputeRefCountsOuterLoopInvImpliesInnerLoopInv(
      tbl': HashMap, tbl: HashMap, it: LinearMutableMap.Iterator<Entry>, succs: seq<BT.G.Reference>)
    requires it.next.Next?
    requires succs == it.next.value.succs
    requires ComputeRefCountsOuterLoopInv(tbl', tbl, it)
    ensures ComputeRefCountsInnerLoopInv(tbl', tbl, it, succs, 0)
    {
      reveal_ComputeRefCountsSharedInv();
      reveal_ComputeRefCountsInnerLoopInv0();
      reveal_ComputeRefCountsOuterLoopInv0();

      forall ref | ref in tbl'.contents
      ensures  tbl'.contents[ref].predCount as int == |PredecessorSetRestrictedPartial(Graph(tbl), ref, it.s, it.next.key, 0)| + IsRoot(ref) {
        assert PredecessorSetRestricted(Graph(tbl), ref, it.s) == PredecessorSetRestrictedPartial(Graph(tbl), ref, it.s, it.next.key, 0);
      }
    }

    static lemma ComputeRefCountsInnerLoopInvImpliesOuterLoopInv(
      tbl': HashMap,
      tbl: HashMap,
      it: LinearMutableMap.Iterator<Entry>,
      it':  LinearMutableMap.Iterator<Entry>,
      succs: seq<BT.G.Reference>,
      i: uint64)
    requires it.next.Next?
    requires succs == it.next.value.succs
    requires LinearMutableMap.WFIter(tbl, it')
    requires it'.s == it.s + {it.next.key}
    requires it'.decreaser < it.decreaser
    requires it'.next.Done? ==> it'.s == tbl.contents.Keys
    requires i as int == |succs|
    requires ComputeRefCountsInnerLoopInv(tbl', tbl, it, succs, i)
    requires BT.G.Root() in tbl'.contents
    ensures ComputeRefCountsOuterLoopInv(tbl', tbl, it')
    {
      RevealComputeRefCountsSharedDomainInv(tbl', tbl);
      forall ref | ref in tbl.contents
      ensures tbl'.contents[ref].predCount as int == |PredecessorSetRestricted(Graph(tbl), ref, it'.s)| + IsRoot(ref) {
        reveal_ComputeRefCountsInnerLoopInv0();
        assert PredecessorSetRestricted(Graph(tbl), ref, it.s + {it.next.key}) == PredecessorSetRestrictedPartial(Graph(tbl), ref, it.s, it.next.key, i as int);
      }
      assert ComputeRefCountsOuterLoopInv0(tbl', tbl, it') by {
        reveal_ComputeRefCountsOuterLoopInv0();

        forall ref | ref in tbl'.contents
        ensures tbl'.contents[ref].predCount as int <= 0x1_0000_0000_0000 {
          lemma_count_eq_graph_size(tbl);
          assert forall ref | ref in Graph(tbl) :: |Graph(tbl)[ref]| <= MaxNumChildren() by {
            reveal_ComputeRefCountsSharedInv();
          }
          PredecessorSetRestrictedSizeBound(Graph(tbl), ref, it'.s);
        }
      }
    }

    static lemma LemmaPredecessorSetRestrictedPartialAdd1Self(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference, domain: set<BT.G.Reference>, next: BT.G.Reference, j: int)
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

    static lemma {:timeLimitMultiplier 8} LemmaPredecessorSetRestrictedPartialAdd1Other(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference, domain: set<BT.G.Reference>, next: BT.G.Reference, j: int)
    requires next in graph
    requires 0 <= j < |graph[next]|
    requires dest != graph[next][j]
    ensures |PredecessorSetRestrictedPartial(graph, dest, domain, next, j + 1)|
         == |PredecessorSetRestrictedPartial(graph, dest, domain, next, j)|
    {
      assert PredecessorSetRestrictedPartial(graph, dest, domain, next, j + 1)
          == PredecessorSetRestrictedPartial(graph, dest, domain, next, j);
    }

    static method {:timeLimitMultiplier 8} ComputeRefCountsInnerLoop(linear inout tbl': HashMap, shared tbl: HashMap, it: LinearMutableMap.Iterator<Entry>)
    returns (success: bool, it': LinearMutableMap.Iterator<Entry>)
    requires it.next.Next?
    requires ComputeRefCountsOuterLoopInv(old_tbl', tbl, it)
    ensures LinearMutableMap.Inv(tbl')
    ensures success ==> (
      && ComputeRefCountsOuterLoopInv(tbl', tbl, it')
      && BT.G.Root() in tbl'.contents
    )
    ensures success ==> it'.decreaser < it.decreaser
    ensures LinearMutableMap.WFIter(tbl, it')
    ensures !success ==> !BC.GraphClosed(Graph(tbl))
    {
      var succs := it.next.value.succs;
      var i: uint64 := 0;

      assert |succs| <= MaxNumChildren() by {
        reveal_ComputeRefCountsSharedInv();
      }
      ComputeRefCountsOuterLoopInvImpliesInnerLoopInv(tbl', tbl, it, succs);

      success := true;
      while i < |succs| as uint64
      invariant i as int <= |succs|
      invariant LinearMutableMap.Inv(tbl)
      invariant LinearMutableMap.WFIter(tbl, it)
      invariant BT.G.Root() in tbl'.contents
      invariant ComputeRefCountsInnerLoopInv(tbl', tbl, it, succs, i)
      decreases |succs| - i as int
      {
        var ref := succs[i];
        var oldEntry := LinearMutableMap.Get(tbl', ref);
        if oldEntry.Some? {
          assert Graph(tbl)[it.next.key][i] in Graph(tbl) by {
            RevealComputeRefCountsSharedDomainInv(tbl', tbl);
          }

          reveal_ComputeRefCountsInnerLoopInv0();
          var newEntry := oldEntry.value.(predCount := oldEntry.value.predCount + 1);
          LinearMutableMap.Insert(inout tbl', ref, newEntry);

          forall r | r in tbl'.contents
          ensures tbl'.contents[r].predCount as int == |PredecessorSetRestrictedPartial(Graph(tbl), r, it.s, it.next.key, (i+1) as int)| + IsRoot(r)
          {
            if r == ref {
              LemmaPredecessorSetRestrictedPartialAdd1Self(Graph(tbl), r, it.s, it.next.key, i as int);
            } else {
              LemmaPredecessorSetRestrictedPartialAdd1Other(Graph(tbl), r, it.s, it.next.key, i as int);
            }
          }

          i := i + 1;

          assert ComputeRefCountsInnerLoopInv(tbl', tbl, it, succs, i) by {
            assert ComputeRefCountsSharedInv(tbl', tbl) by {
              reveal_ComputeRefCountsSharedInv();
            }
            assert ComputeRefCountsInnerLoopInv0(tbl', tbl, it, succs, i);
          }
        } else {
          assert tbl'.contents.Keys == tbl.contents.Keys by {
            reveal_ComputeRefCountsSharedInv();
          }
          assert ref in Graph(tbl)[it.next.key];
          // (doc) assert !BC.GraphClosed(Graph(tbl));
          success := false;
          break;
        }
      }

      it' := LinearMutableMap.IterInc(tbl, it);
      
      if (success) {
        ComputeRefCountsInnerLoopInvImpliesOuterLoopInv(tbl', tbl, it, it', succs, i);
      }
    }

    static method {:timeLimitMultiplier 8} ComputeRefCounts(shared tbl: HashMap)
      returns (linear tbl' : lOption<HashMap>)
      requires tbl.Inv()
      requires forall ref | ref in tbl.contents :: tbl.contents[ref].predCount == 0
      requires forall ref | ref in tbl.contents :: |tbl.contents[ref].succs| <= MaxNumChildren()
      requires tbl.count as int <= MaxSize()
      requires BT.G.Root() in tbl.contents

      ensures tbl'.lSome? ==> (
        && tbl'.value.Inv()
        && |tbl'.value.contents| <= 0x1_0000_0000)
      ensures BC.GraphClosed(Graph(tbl)) <==> tbl'.lSome?
      ensures tbl'.lSome? ==> Graph(tbl) == Graph(tbl'.value)
      ensures tbl'.lSome? ==> Locs(tbl) == Locs(tbl'.value)
      ensures tbl'.lSome? ==> ValidPredCounts(PredCounts(tbl'.value), Graph(tbl'.value))
      ensures tbl'.lSome? ==> BT.G.Root() in tbl'.value.contents
    {
      linear var t1 := LinearMutableMap.Clone(tbl);

      var oldEntryOpt := LinearMutableMap.Get(t1, BT.G.Root());
      var oldEntry := oldEntryOpt.value;
      LinearMutableMap.Insert(inout t1, BT.G.Root(), oldEntry.(predCount := 1));

      var it := LinearMutableMap.IterStart(tbl);

      assert ComputeRefCountsOuterLoopInv(t1, tbl, it) by {
        forall ref | ref in t1.contents
        ensures t1.contents[ref].predCount as int
            == |PredecessorSetRestricted(Graph(t1), ref, it.s)| + IsRoot(ref)
        {
          assert PredecessorSetRestricted(Graph(t1), ref, it.s) == {};
        }
        reveal_ComputeRefCountsSharedInv();
        reveal_ComputeRefCountsOuterLoopInv0();
      }

      var success := true;
      while it.next.Next?
      invariant ComputeRefCountsOuterLoopInv(t1, tbl, it)
      decreases it.decreaser
      {
        success, it := ComputeRefCountsInnerLoop(inout t1, tbl, it);
        if (!success) {
          break;
        }

        assert ComputeRefCountsOuterLoopInv(t1, tbl, it);
      }

      if success {
        tbl' := lSome(t1);

        assert (
          && Graph(tbl) == Graph(tbl'.value)
          && Locs(tbl) == Locs(tbl'.value)
        ) by {
          reveal_ComputeRefCountsSharedInv();
        }
        assert ValidPredCounts(PredCounts(tbl'.value), Graph(tbl'.value)) by {
          reveal_ComputeRefCountsSharedInv();
          reveal_ComputeRefCountsOuterLoopInv0();
          reveal_PredCounts();
          forall ref | ref in PredCounts(tbl'.value)
          ensures PredCounts(tbl'.value)[ref] == |PredecessorSet(Graph(tbl'.value), ref)| + IsRoot(ref)
          {
            assert PredecessorSetRestricted(Graph(tbl'.value), ref, it.s) == 
              PredecessorSet(Graph(tbl'.value), ref); // observe
          }
        }
        assert BC.GraphClosed(Graph(tbl));
      } else {
        LinearMutableMap.Destructor(t1);
        tbl' := lNone;

        assert !BC.GraphClosed(Graph(tbl));
      }
    }

    static method {:timeLimitMultiplier 8} MakeGarbageQueue(shared t: HashMap)
    returns (linear q : USeq.USeq)
    requires t.Inv()
    requires |t.contents| <= 0x1_0000_0000
    ensures q.Inv()
    ensures forall ref | ref in t.contents && t.contents[ref].predCount == 0 :: ref in q.I()
    ensures forall ref | ref in q.I() :: ref in t.contents && t.contents[ref].predCount == 0
    {
      q := USeq.USeq.Alloc();
      var it := LinearMutableMap.IterStart(t);
      while it.next.Next?
      invariant q.Inv()
      invariant LinearMutableMap.Inv(t)
      invariant LinearMutableMap.WFIter(t, it)
      invariant Set(q.I()) <= t.contents.Keys
      invariant |t.contents| <= 0x1_0000_0000
      invariant forall ref | ref in t.contents && t.contents[ref].predCount == 0 && ref in it.s :: ref in q.I()
      invariant forall ref | ref in q.I() :: ref in t.contents && t.contents[ref].predCount == 0 && ref in it.s
      decreases it.decreaser
      {
        if it.next.value.predCount == 0 {
          NoDupesSetCardinality(q.I());
          SetInclusionImpliesSmallerCardinality(Set(q.I()), t.contents.Keys);
          assert |t.contents.Keys| == |t.contents|;

          inout q.Add(it.next.key);
        }
        it := LinearMutableMap.IterInc(t, it);
      }
    }

    static method ComputeRefUpperBound(shared t: HashMap)
    returns (r: uint64)
    requires t.Inv()
    ensures forall ref | ref in t.contents :: ref <= r
    {
      var it := LinearMutableMap.IterStart(t);
      var refUpperBound := 0;
      while it.next.Next?
      invariant LinearMutableMap.Inv(t)
      invariant LinearMutableMap.WFIter(t, it)
      invariant forall ref | ref in it.s :: ref <= refUpperBound
      decreases it.decreaser
      {
        if it.next.key > refUpperBound {
          refUpperBound := it.next.key;
        }
        it := LinearMutableMap.IterInc(t, it);
      }
      r := refUpperBound;
    }

    static method {:timeLimitMultiplier 8} ValToIndirectionTable(v: V)
    returns (linear s : lOption<IndirectionTable>)
    requires ValidVal(v)
    requires ValInGrammar(v, IndirectionTableGrammar())
    ensures s.lSome? ==> s.value.Inv()
    ensures s.lSome? ==> Marshalling.valToIndirectionTable(v) == Some(s.value.I())
    ensures s.lSome? ==> s.value.TrackingGarbage()
    ensures s.lNone? ==> Marshalling.valToIndirectionTable(v).None?
    {
      if |v.a| as uint64 <= MaxSizeUint64() {
        linear var res := ValToHashMap(v.a);
        linear match res {
          case lSome(t) => {
            var rootRef := LinearMutableMap.Get(t, BT.G.Root());
            if rootRef.Some? {
              linear var t1opt := ComputeRefCounts(t);
              LinearMutableMap.Destructor(t);
              linear match t1opt {
                case lSome(t1) => {
                  assert t1.Inv();
                  assert |t1.contents| <= 0x1_0000_0000;

                  linear var q := MakeGarbageQueue(t1);
                  var refUpperBound := ComputeRefUpperBound(t1);
                  s := lSome(IndirectionTable(
                    t1, lSome(q), refUpperBound, None,
                    /* r.locs */ Locs(t1),
                    /* r.graph */ Graph(t1),
                    /* r.predCounts */ PredCounts(t1)));

                  assert s.lSome? ==> s.value.Inv() by {
                    reveal s.value.Inv();
                  }
                }
                case lNone => {
                  s := lNone;
                }
              }
            } else {
              LinearMutableMap.Destructor(t);
              s := lNone;
            }
          }
          case lNone => {
            s := lNone;
          }
        }
      } else {
        s := lNone;
      }
    }

    static function {:timeLimitMultiplier 8} MaxIndirectionTableByteSize() : int {
      8 + MaxSize() * (8 + 8 + 8 + (8 + MaxNumChildren() * 8))
    }

    static lemma {:timeLimitMultiplier 8} lemma_SeqSum_prefix_array(a: array<V>, i: int)
    requires 0 < i <= a.Length
    ensures SeqSum(a[..i-1]) + SizeOfV(a[i-1]) == SeqSum(a[..i])
    {
      lemma_SeqSum_prefix(a[..i-1], a[i-1]);
      assert a[..i-1] + [a[i-1]] == a[..i];
    }

    static lemma {:fuel SizeOfV,5} lemma_tuple_size(a: uint64, b: uint64, c: uint64, succs: seq<BT.G.Reference>)
    requires|succs| <= MaxNumChildren()
    ensures SizeOfV(VTuple([VUint64(a), VUint64(b), VUint64(c), VUint64Array(succs)]))
         == (8 + 8 + 8 + (8 + |succs| * 8))
    {
    }

    static lemma lemma_SeqSum_empty()
    ensures SeqSum([]) == 0;
    {
      reveal_SeqSum();
    }

    static function {:timeLimitMultiplier 8} IMapAsIndirectionTable(m: map<uint64, Entry>) : SectorType.IndirectionTable
    {
      SectorType.IndirectionTable(MapLocs(m), MapGraph(m)) // TODO: yizhou7
    }

    static function method IndirectionTableGrammar() : G
    ensures ValidGrammar(IndirectionTableGrammar())
    {
      // (Reference, address, len, successor-list) triples
      GArray(GTuple([GUint64, GUint64, GUint64, GUint64Array]))
    }

    // NOTE(travis): I found that the above method which marshalls
    // directly from indirection table to bytes is much faster
    // than converting to a V and using the GenericMarshalling
    // framework. I did some work on proving it (above),
    // but it's kind of annoying. However, I think that it won't
    // be a big deal as long as most syncs are journaling syncs?
    // So I've moved back to this one which is slower but cleaner.
    shared method {:timeLimitMultiplier 8} IndirectionTableToVal()  // HashMapToVal
    returns (v : V, size: uint64)
    requires this.Inv()
    requires BC.WFCompleteIndirectionTable(this.I())
    ensures ValInGrammar(v, IndirectionTableGrammar())
    ensures ValidVal(v)
    ensures Marshalling.valToIndirectionTable(v).Some?
    ensures Marshalling.valToIndirectionTable(v).value == this.I()
    ensures SizeOfV(v) <= MaxIndirectionTableByteSize()
    ensures SizeOfV(v) == size as int
    {
      reveal Inv();
      assert this.t.count <= MaxSizeUint64();
      lemma_SeqSum_empty();
      var count := this.t.count as uint64;
      var a: array<V> := new V[count];
      var it := LinearMutableMap.IterStart(this.t);
      var i: uint64 := 0;
      size := 0;

      ghost var partial := map[];

      assert MapLocs(map[]) == map[];
      assert MapGraph(map[]) == map[];
      assert ValIsMap(a[..i], Some(partial));

      while it.next.Next?
      // TODO(remove)?
      invariant this.Inv()
      invariant BC.WFCompleteIndirectionTable(this.I())
      invariant 0 <= i as int <= a.Length
      invariant LinearMutableMap.WFIter(this.t, it);
      invariant forall j | 0 <= j < i :: ValidVal(a[j])
      invariant forall j | 0 <= j < i :: ValInGrammar(a[j], GTuple([GUint64, GUint64, GUint64, GUint64Array]))
      invariant |partial.Keys| == i as nat
      invariant partial.Keys == it.s
      invariant partial.Keys <= this.t.contents.Keys
      invariant ValIsMap(a[..i], Some(partial))
      invariant forall r | r in partial :: r in this.t.contents
          && partial[r].loc == this.t.contents[r].loc
          && partial[r].succs == this.t.contents[r].succs
      invariant size as int <=
          |it.s| * (8 + 8 + 8 + (8 + MaxNumChildren() * 8))
      invariant SeqSum(a[..i]) == size as int;
      decreases it.decreaser
      {
        var (ref, locOptGraph: Entry) := (it.next.key, it.next.value);
        assert ref in this.I().locs;
        // NOTE: deconstructing in two steps to work around c# translation bug
        var locOpt := locOptGraph.loc;
        var succs := locOptGraph.succs;
        var loc := locOpt.value;
        //ghost var predCount := locOptGraph.predCount;
        var childrenVal := VUint64Array(succs);

        assert |succs| <= MaxNumChildren();

        //assert I(this).locs[ref] == loc;
        //assert I(this).graph[ref] == succs;

        //assert IndirectionTableModel.I(I(this)).locs[ref] == loc;
        //assert IndirectionTableModel.I(I(this)).graph[ref] == succs;

        assert ValidNodeLocation(loc);
        /*ghost var t0 := IndirectionTableModel.valToHashMap(a[..i]);
        assert ref !in t0.value.contents;
        assert loc.addr != 0;
        assert LBAType.ValidLocation(loc);*/

        LinearMutableMap.LemmaIterIndexLtCount(this.t, it);

        assert |succs| < 0x1_0000_0000_0000_0000;
        assert ValidVal(VTuple([VUint64(ref), VUint64(loc.addr), VUint64(loc.len), childrenVal]));

        // assert |LinearMutableMap.IterInc(this.t, it).s| == |it.s| + 1;

        var vi := VTuple([VUint64(ref), VUint64(loc.addr), VUint64(loc.len), childrenVal]);

        //assert SizeOfV(vi) <= (8 + 8 + 8 + (8 + MaxNumChildren() * 8));

        ghost var partialBefore := partial;

        // == mutation ==
        ghost var itBeforeInc := it;
        partial := partial[ref := Entry(locOpt, succs, 0)];
        a[i] := vi;
        i := i + 1;
        it := LinearMutableMap.IterInc(this.t, it);
        // ==============

        assert |itBeforeInc.s| + 1 == |it.s|;

        assert a[..i-1] == DropLast(a[..i]); // observe

        calc {
          SeqSum(a[..i]);
          {
            lemma_SeqSum_prefix_array(a, i as int);
          }
          SeqSum(a[..i-1]) + SizeOfV(a[i-1]);
          SeqSum(a[..i-1]) + SizeOfV(vi);
          {
            lemma_tuple_size(ref, loc.addr, loc.len, succs);
          }
          size as int + (8 + 8 + 8 + (8 + 8 * |succs|));
        }

        size := size + 32 + 8 * |succs| as uint64;

        assert ValIsMap(a[..i], Some(partial)) by {
          ghost var aBefore := Marshalling.valToIndirectionTableMaps(DropLast(a[..i]));
          assert aBefore.value.locs[ref := loc] == MapLocs(partial); // observe
          assert aBefore.value.graph[ref := succs] == MapGraph(partial); // observe
        }
      }

      /* (doc) assert |partial.Keys| == |this.t.contents.Keys|; */
      SetInclusionAndEqualCardinalityImpliesSetEquality(partial.Keys, this.t.contents.Keys);

      assert a[..i] == a[..]; // observe
      v := VArray(a[..]);

      /*ghost var t0 := IndirectionTableModel.valToHashMap(v.value.a);
      assert t0.Some?;
      assert BT.G.Root() in t0.value.contents;
      assert t0.value.count <= MaxSizeUint64();
      ghost var t1 := IndirectionTableModel.ComputeRefCounts(t0.value);
      assert t1.Some?;*/

      assert |it.s| <= MaxSize();

      size := size + 8;

      // assert this.I() == IMapAsIndirectionTable(partial); // observe

      assert Marshalling.valToIndirectionTable(v).Some?;
      // assert Marshalling.valToIndirectionTable(v) == Some(this.I());

      // assert Marshalling.valToIndirectionTable(v).value.locs == this.I().locs;
      // assert Marshalling.valToIndirectionTable(v).value.graph == this.I().graph;
    }

    // // To bitmap

    static predicate IsLocAllocBitmap(bm: BitmapModel.BitmapModelT, i: int)
    {
      && 0 <= i < BitmapModel.Len(bm)
      && BitmapModel.IsSet(bm, i)
    }

    // static method BitmapInitUpToIterate(bm: BitmapImpl.Bitmap, i: uint64, upTo: uint64)
    // requires bm.Inv()
    // requires 0 <= i as int <= upTo as int <= BitmapModel.Len(bm.I())
    // modifies bm.Repr
    // ensures bm.Inv()
    // ensures bm.I() == IndirectionTableModel.BitmapInitUpToIterate(old(bm.I()), i, upTo)
    // ensures bm.Repr == old(bm.Repr)
    // decreases upTo - i
    // {
    //   if i == upTo {
    //   } else {
    //     bm.Set(i);
    //     BitmapInitUpToIterate(bm, i+1, upTo);
    //   }
    // }

    static method {:timeLimitMultiplier 8} BitmapInitUpTo(linear inout bm: BitmapImpl.Bitmap, upTo: uint64)
    requires old_bm.Inv()
    requires upTo as int <= BitmapModel.Len(old_bm.I())
    ensures bm.Inv()
    ensures BitmapModel.Len(old_bm.I()) == BitmapModel.Len(bm.I())
    ensures forall j: nat | j < BitmapModel.Len(old_bm.I()) :: (
      && (j < upTo as nat ==> BitmapModel.IsSet(bm.I(), j as int))
      && (j >= upTo as nat ==> BitmapModel.IsSet(bm.I(), j as int) == BitmapModel.IsSet(old_bm.I(), j as int))
    )
    {
      var i := 0;
      while i < upTo
      invariant i <= upTo
      invariant bm.Inv()
      invariant upTo as int <= BitmapModel.Len(bm.I())
      invariant BitmapModel.Len(old_bm.I()) == BitmapModel.Len(bm.I())
      invariant forall j: nat | j < BitmapModel.Len(old_bm.I()) :: (
        && (j < i as nat ==> BitmapModel.IsSet(bm.I(), j as int))
        && (j >= i as nat ==> BitmapModel.IsSet(bm.I(), j as int) == BitmapModel.IsSet(old_bm.I(), j as int))
      )
      {
        inout bm.Set(i);
        i := i + 1;

        BitmapModel.reveal_BitSet();
        BitmapModel.reveal_IsSet();
      }
    }


    predicate IsLocAllocIndirectionTablePartial(i: int, s: set<uint64>)
    {
      || 0 <= i < MinNodeBlockIndex() // these blocks can't be used
      || !(
        forall ref | ref in this.locs && ref in s ::
          this.locs[ref].addr as int != i * NodeBlockSize() as int
      )
    }

    shared method {:timeLimitMultiplier 8} InitLocBitmap()
    returns (success: bool, linear bm: BitmapImpl.Bitmap)
    requires this.Inv()
    requires BC.WFCompleteIndirectionTable(this.I())
    ensures bm.Inv()
    ensures BitmapModel.Len(bm.I()) == NumBlocks()
    ensures (success ==>
      && (forall i: nat :: I().IsLocAllocIndirectionTable(i) <==> IsLocAllocBitmap(bm.I(), i))
      && BC.AllLocationsForDifferentRefsDontOverlap(I())
    )
    {
      reveal this.Inv();
      bm := BitmapImpl.Bitmap.Constructor(NumBlocksUint64());
      assert BitmapModel.Len(bm.I()) == NumBlocks();

      MinNodeBlockIndex_le_NumBlocks();
      BitmapInitUpTo(inout bm, MinNodeBlockIndexUint64());
      var it := LinearMutableMap.IterStart(this.t);

      assert BitmapModel.Len(bm.I()) == NumBlocks();
      assert NumBlocks() == NumBlocksUint64() as int;

      success := true;

      forall i: nat
      ensures IsLocAllocIndirectionTablePartial(i, it.s) <==> IsLocAllocBitmap(bm.I(), i)
      {
        assert IsLocAllocIndirectionTablePartial(i, it.s) ==> 0 <= i < BitmapModel.Len(bm.I());
        assert IsLocAllocBitmap(bm.I(), i) ==> 0 <= i < BitmapModel.Len(bm.I());
      }

      forall r: uint64 | r in this.I().locs
      ensures (
        && var li := this.t.contents[r].loc.value.addr as int / NodeBlockSize();
        && (MinNodeBlockIndex() <= li)
        && (li < NumBlocks() ==> (r in it.s <==> BitmapModel.IsSet(bm.I(), li)))
      )
      {
        assert ValidNodeLocation(this.t.contents[r].loc.value);
        assert ValidNodeAddr(this.t.contents[r].loc.value.addr);
        var li := ValidNodeAddrDivisor(this.t.contents[r].loc.value.addr);
        Math.lemma_mul_invert(this.t.contents[r].loc.value.addr as int, NodeBlockSize(), li);
        assert li == this.t.contents[r].loc.value.addr as int / NodeBlockSize();
        assert MinNodeBlockIndex() <= li;
        if li < NumBlocks() {
          if r in it.s {
            assert false;
          } else {
            assert !BitmapModel.IsSet(bm.I(), li);
          }
        }
      }

      while it.next.Next?
      invariant this.t.Inv()
      invariant BC.WFCompleteIndirectionTable(this.I())
      invariant bm.Inv()
      invariant LinearMutableMap.WFIter(this.t, it)
      invariant BitmapModel.Len(bm.I()) == NumBlocks()
      // invariant success ==> forall r: uint64 | r in this.I().locs :: (
      //   var li := this.t.contents[r].loc.value.addr as int / NodeBlockSize();
      //   && MinNodeBlockIndex() <= li
      //   && (li < NumBlocks() ==> (r in it.s <==> BitmapModel.IsSet(bm.I(), li)))
      // )
      // invariant forall r: uint64 | r in this.I().locs && MinNodeBlockIndex() <= this.t.contents[r].loc.value.addr as int / NodeBlockSize() < NumBlocks() ::
      //     r !in it.s ==> !BitmapModel.IsSet(bm.I(), this.t.contents[r].loc.value.addr as int / NodeBlockSize())
      invariant forall i: nat :: IsLocAllocIndirectionTablePartial(i, it.s) <==> IsLocAllocBitmap(bm.I(), i)
      invariant success ==> forall r1, r2 | r1 in this.I().locs && r2 in this.I().locs ::
          r1 in it.s && r2 in it.s ==>
          BC.LocationsForDifferentRefsDontOverlap(this.I(), r1, r2)
      decreases it.decreaser
      {
        assert it.next.key in this.I().locs;

        var loc: uint64 := it.next.value.loc.value.addr;
        assert 0 <= loc as nat / NodeBlockSize() < Uint64UpperBound() by {
          NonlinearLemmas.div_ge_0(loc as nat, NodeBlockSize());
          NonlinearLemmas.div_denom_ge_1(loc as nat, NodeBlockSize());
        }
        assert loc as int % NodeBlockSize() == 0 by {
          reveal_ValidNodeAddr();
          assert ValidNodeLocation(it.next.value.loc.value);
        }
        var locIndex: uint64 := loc / NodeBlockSizeUint64();
        if locIndex < NumBlocksUint64() {
          var isSet := bm.GetIsSet(locIndex);
          if !isSet {
            ghost var it0 := it;
            ghost var bm0 := bm;

            it := LinearMutableMap.IterInc(this.t, it);
            inout bm.Set(locIndex);
            
            assert forall i: nat :: IsLocAllocIndirectionTablePartial(i, it0.s) <==> IsLocAllocBitmap(bm0.I(), i);

            forall i: nat | IsLocAllocIndirectionTablePartial(i, it.s) 
            ensures IsLocAllocBitmap(bm.I(), i) {
              BitmapModel.reveal_BitSet();
              BitmapModel.reveal_IsSet();

              if i == locIndex as nat {
                assert IsLocAllocBitmap(bm.I(), i);
              } else {
                if 0 <= i < MinNodeBlockIndex() {
                  if IsLocAllocIndirectionTablePartial(i, it0.s) { }
                } else {
                  assert MinNodeBlockIndex() <= i;
                  
                  assert exists ref | ref in this.locs && ref in it.s ::
                    !(this.locs[ref].addr as int != i * NodeBlockSize() as int);

                  assert loc as int / NodeBlockSize() == locIndex as int;
                  assert loc as int / NodeBlockSize() != i;

                  assert loc as int % NodeBlockSize() == 0;
                  NonlinearLemmas.div_invert(loc as int, NodeBlockSize(), i);
                  // TODO(andrea) use ValidNodeAddrDivisor?
                  assert loc as int != i * NodeBlockSize();
                  assert it.s == it0.s + { it0.next.key };

                  assert IsLocAllocIndirectionTablePartial(i, it0.s) by {
                    assert exists ref | ref in this.locs && ref in it0.s ::
                      !(this.locs[ref].addr as int != i * NodeBlockSize() as int);
                  }
                }
              }
            }

            forall i: nat | IsLocAllocBitmap(bm.I(), i)
            ensures IsLocAllocIndirectionTablePartial(i, it.s)  {
              BitmapModel.reveal_BitSet();
              BitmapModel.reveal_IsSet();

              if IsLocAllocBitmap(bm0.I(), i) { }
              if IsLocAllocIndirectionTablePartial(i, it0.s) { }

              if i == locIndex as int {
                var ref := it0.next.key;
                assert this.t.contents[ref].loc.Some?;
                assert ref in it.s;
                assert this.t.contents[ref] == it0.next.value;
                assert this.t.contents[ref].loc.value.addr as int / NodeBlockSize() == i;
                assert this.t.contents[ref].loc.value.addr == loc;
                assert loc as int % NodeBlockSize() == 0;
                // TODO(andrea) use ValidNodeAddrDivisor?
                NonlinearLemmas.div_invert(loc as int, NodeBlockSize(), i);
                assert this.t.contents[ref].loc.value.addr as int == i * NodeBlockSize() as int;

                assert IsLocAllocIndirectionTablePartial(i, it.s);
              } else {
                assert IsLocAllocIndirectionTablePartial(i, it.s);
              }
            }

            forall r1, r2 | r1 in this.I().locs && r2 in this.I().locs && r1 in it.s && r2 in it.s
            ensures BC.LocationsForDifferentRefsDontOverlap(this.I(), r1, r2)
            {
              if r1 != r2 {
                if r1 in it0.s && r2 in it0.s {
                  assert BC.LocationsForDifferentRefsDontOverlap(this.I(), r1, r2);
                } else {
                  reveal_ValidNodeAddr();
                  if this.I().locs[r1].addr == this.I().locs[r2].addr {
                    assert ValidNodeLocation(this.t.contents[r1].loc.value);
                    assert ValidNodeAddr(this.t.contents[r1].loc.value.addr);
                    var j1 := DiskLayout.ValidNodeAddrDivisor(this.I().locs[r1].addr);
                    var j2 := DiskLayout.ValidNodeAddrDivisor(this.I().locs[r2].addr);
                    Math.lemma_mul_invert(this.t.contents[r1].loc.value.addr as int, NodeBlockSize(), j1);
                    Math.lemma_mul_invert(this.t.contents[r2].loc.value.addr as int, NodeBlockSize(), j2);
                    if r1 !in it0.s {
                      assert r2 in it0.s;
                      assert !BitmapModel.IsSet(bm0.I(), j1);
                      assert IsLocAllocBitmap(bm0.I(), j2);
                      assert BitmapModel.IsSet(bm0.I(), j2);
                      assert false;
                    } else {
                      assert r1 in it0.s;
                      assert !BitmapModel.IsSet(bm0.I(), j2);
                      assert IsLocAllocBitmap(bm0.I(), j1);
                      assert BitmapModel.IsSet(bm0.I(), j1);
                      assert false;
                    }
                  } else {
                    assert BC.LocationsForDifferentRefsDontOverlap(this.I(), r1, r2);
                  }
                }
              }
            }

          } else {
            success := false;
            break;
          }
        } else {
          success := false;
          break;
        }
      }
    }
    // 
    // ///// Dealloc stuff

    predicate deallocable(ref: BT.G.Reference)
    {
      && ref in this.I().graph
      && ref != BT.G.Root()
      && (forall r | r in this.I().graph :: ref !in this.I().graph[r])
    }

    shared method {:timeLimitMultiplier 8} FindDeallocable() returns (ref: Option<BT.G.Reference>)
    requires this.Inv()
    requires this.TrackingGarbage()
    ensures ref.Some? ==> ref.value in this.I().graph
    ensures ref.Some? ==> this.deallocable(ref.value)
    ensures ref.None? ==> forall r | r in this.I().graph :: !this.deallocable(r)
    {
      reveal this.Inv();

      ref := this.garbageQueue.value.FirstOpt();
      if ref.None? {
        forall r | r in this.I().graph ensures !this.deallocable(r)
        {
          assert this.t.contents[r].predCount != 0;
          if r == BT.G.Root() {
            assert !this.deallocable(r);
          } else {
            reveal_PredCounts();
            var y : PredecessorEdge :| y in PredecessorSet(this.graph, r); // observe
          }
        }
      } else {
        reveal_PredCounts();
        assert this.predCounts[ref.value] == |PredecessorSet(this.graph, ref.value)| + IsRoot(ref.value);
        forall r | r in this.I().graph ensures ref.value !in this.I().graph[r]
        {
          if ref.value in this.I().graph[r] {
            var i :| 0 <= i < |this.I().graph[r]| && this.I().graph[r][i] == ref.value;
            assert PredecessorEdge(r, i) in PredecessorSet(this.graph, ref.value);
          }
        }
      }
    }

    shared function method GetSize() : (size: uint64)
    requires this.Inv()
    ensures size as int == |this.I().graph|
    {
      reveal this.Inv();
      lemma_count_eq_graph_size(this.t);
      this.t.count
    }

    linear inout method FindRefWithNoLoc() returns (ref: Option<BT.G.Reference>)
    requires old_self.Inv()
    ensures self.Inv()
    ensures self.I() == old_self.I()
    ensures ref.Some? ==> ref.value in old_self.graph
    ensures ref.Some? ==> ref.value !in old_self.locs
    ensures ref.None? ==> forall r | r in old_self.graph :: r in old_self.locs
    {
      reveal old_self.Inv();
      var findLoclessIterator := self.findLoclessIterator;
      var it;
      if findLoclessIterator.Some? {
        it := findLoclessIterator.value;
      } else {
        it := LinearMutableMap.SimpleIterStart(self.t);
      }

      while true
      invariant self.Inv()
      invariant self == old_self.(t := self.t)
      invariant LinearMutableMap.WFSimpleIter(self.t, it)
      invariant forall r | r in it.s :: r in self.I().locs
      decreases it.decreaser
      {
        var next := LinearMutableMap.SimpleIterOutput(self.t, it);
        if next.Next? {
          if next.value.loc.None? {
            inout self.findLoclessIterator := Some(it);
            ref := Some(next.key);
            break;
          } else {
            it := LinearMutableMap.SimpleIterInc(self.t, it);
          }
        } else {
          inout self.findLoclessIterator := Some(it);
          ref := None;
          break;
        }
      }
      reveal self.Inv();
    }

    function {:opaque} {:timeLimitMultiplier 8} getRefUpperBound() : (r: uint64)
    requires Inv()
    ensures forall ref | ref in this.graph :: ref <= r
    {
      reveal Inv();
      this.refUpperBound
    }

    shared method {:timeLimitMultiplier 8} GetRefUpperBound() returns (r: uint64)
    requires this.Inv()
    ensures r == this.getRefUpperBound()
    {
      reveal_getRefUpperBound();
      r := this.refUpperBound;
    }
  }
}
