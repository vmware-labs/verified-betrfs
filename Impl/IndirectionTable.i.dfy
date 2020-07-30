include "../lib/Base/DebugAccumulator.i.dfy"
include "../lib/Base/Maps.s.dfy"
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/LinearOption.i.dfy"
include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Lang/LinearMaybe.s.dfy"
include "../lib/Lang/LinearBox.i.dfy"
include "../lib/DataStructures/LinearMutableMap.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "../lib/DataStructures/BitmapImpl.i.dfy"
include "../lib/DataStructures/LinearUSeq.i.dfy"
include "../BlockCacheSystem/BlockCache.i.dfy"
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

  datatype Entry = Entry(loc: Option<Location>, succs: seq<BT.G.Reference>, predCount: uint64)
  type HashMap = LinearMutableMap.LinearHashMap<Entry>
  type GarbageQueue = USeq.USeq

  // == UTILS ==
  function Locs(t: HashMap) : map<BT.G.Reference, Location>
  {
    map ref | ref in t.contents && t.contents[ref].loc.Some? :: t.contents[ref].loc.value
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
  // =============

  function MaxSize() : int
  {
    IndirectionTableMaxSize()
  }

  function method MaxSizeUint64() : uint64
  {
    IndirectionTableMaxSizeUint64()
  }

  // // Dummy constructor only used when ImplVariables is in a state with no indirection
  // // table. We could use a null indirection table instead, it's just slightly more
  // // annoying to do that because we'd need additional invariants.
  // function method IndirectionTableEmptyConstructor() : linear indirectionTable
  // ensures It.Inv(IndirectionTableEmptyConstructor())
  // {
  //   linear var t0 := LinearMutableMap.Constructor<Entry>(128);
  //   // This is not important, but needed to satisfy the Inv:
  //   linear var t1 := LinearMutableMap.Insert(t0, BT.G.Root(), Entry(None, [], 1));

  //   indirectionTable(
  //     t1,
  //     lNone,
  //     /* refUpperBound = */ 0,
  //     None)
  // }



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

    protected predicate Inv()
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

    static method Alloc(loc: Location) returns (linear r: IndirectionTable)
    ensures r.Inv()
    ensures r.graph == map[BT.G.Root() := []]
    ensures r.locs == map[BT.G.Root() := loc]
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
    }

    // TODO useful? var res := IndirectionTableModel.FromHashMap(me.t, MapOption(me.garbageQueue.Option(), x => USeq.I(x)), me.refUpperBound, me.findLoclessIterator);

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
    ensures this.Inv()
    ensures cloned.graph == this.graph
    ensures cloned.locs == this.locs
    {
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
      e := LinearMutableMap.Get(this.t, ref);
    }

    shared method HasEmptyLoc(ref: BT.G.Reference) returns (b: bool)
    requires this.Inv()
    ensures b == (ref in this.graph && ref !in this.locs)
    {
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
    ensures (oldLoc.None? ==> ref !in old_self.locs)
    ensures (oldLoc.Some? ==> ref in old_self.locs && old_self.locs[ref] == oldLoc.value)
    {
      var it := LinearMutableMap.FindSimpleIter(self.t, ref);
      var oldEntry := LinearMutableMap.SimpleIterOutput(self.t, it);
       
      var predCount := oldEntry.value.predCount;
      var succs := oldEntry.value.succs;

      LinearMutableMap.UpdateByIter(inout self.t, it, Entry(None, succs, predCount));
      inout self.findLoclessIterator := None;
      inout self.UpdateGhost();

      oldLoc := oldEntry.value.loc;

      assert PredCounts(self.t) == PredCounts(old_self.t);
      assert Graph(self.t) == Graph(old_self.t);
    }

    linear inout method AddLocIfPresent(ref: BT.G.Reference, loc: Location)
    returns (added: bool)
    requires old_self.Inv()
    ensures self.Inv()
    ensures added == (ref in old_self.graph && ref !in old_self.locs)
    ensures self.graph == old_self.graph
    ensures (added ==> self.locs == old_self.locs[ref := loc])
    ensures (!added ==> self.locs == old_self.locs)
    ensures (old_self.TrackingGarbage() ==> self.TrackingGarbage())
    {
      var it := LinearMutableMap.FindSimpleIter(self.t, ref);
      var oldEntry := LinearMutableMap.SimpleIterOutput(self.t, it);

      added := oldEntry.Next? && oldEntry.value.loc.None?;
      if added {
        LinearMutableMap.UpdateByIter(inout self.t, it, Entry(Some(loc), oldEntry.value.succs, oldEntry.value.predCount));
        inout self.UpdateGhost();
      }

      assert Graph(self.t) == Graph(old_self.t);
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

    // lemma LemmaRemoveRefStuff(ref: BT.G.Reference)
    // requires Inv(this)
    // requires TrackingGarbage(this)
    // requires ref in this.t.contents
    // requires deallocable(this, ref)
    // requires this.t.count as nat < 0x1_0000_0000_0000_0000 / 8 - 1;
    // ensures
    //   var RemoveResult(t, oldEntry) := LinearMutableMap.RemoveAndGet(this.t, ref);
    //   var q := RemoveOneValue(this.garbageQueue.value, ref);
    //   RefcountUpdateInv(t, q, ref, [], oldEntry.value.succs, 0, 0)
    // {
    //   var RemoveResult(t, oldEntry) := LinearMutableMap.RemoveAndGet(this.t, ref);

    //   // LruModel.LruRemove(this.garbageQueue.value, ref);

    //   assert |Graph(this.t)[ref]| <= MaxNumChildren();

    //   forall ref | ref in Graph(t)
    //   ensures |Graph(t)[ref]| <= MaxNumChildren()
    //   {
    //     assert Graph(t)[ref] == Graph(this.t)[ref];
    //   }

    //   var graph0 := Graph(this.t);
    //   var graph1 := Graph(t);
    //   var succs0 := Graph(this.t)[ref];
    //   var succs1 := [];
    //   var predCounts1 := PredCounts(t);
    //   forall r | r in predCounts1
    //   ensures predCounts1[r] == |PredecessorSet(graph1, r)| + IsRoot(r)
    //         - SeqCount(succs1, r, 0)
    //         + SeqCount(succs0, r, 0)
    //   {
    //     SeqCountPlusPredecessorSetExcept(graph0, r, ref);
    //     SeqCountPlusPredecessorSetExcept(graph1, r, ref);

    //     assert PredecessorSetExcept(graph0, r, ref)
    //         == PredecessorSetExcept(graph1, r, ref);
    //   }
    //   assert ValidPredCountsIntermediate(PredCounts(t), Graph(t), [], succs0, 0, 0);

    //   forall j | 0 <= j < |succs0|
    //   ensures succs0[j] in t.contents
    //   {
    //     if succs0[j] == ref {
    //       assert ref in I(this).graph[ref];
    //       assert false;
    //     }
    //     assert succs0[j] == this.t.contents[ref].succs[j];
    //     assert succs0[j] in this.t.contents[ref].succs;
    //     assert succs0[j] in this.t.contents;
    //   }

    //   forall r, succ | r in Graph(t) && succ in Graph(t)[r]
    //   ensures succ in Graph(t)
    //   {
    //     if succ == ref {
    //       assert ref in I(this).graph[r];
    //       assert false;
    //     }
    //     assert succ in Graph(this.t)[r];
    //     assert succ in Graph(this.t);
    //   }
    // }

    linear inout method RemoveRef(ref: BT.G.Reference)
    returns (oldLoc : Option<Location>)
    requires old_self.Inv()
    requires old_self.TrackingGarbage()
    requires old_self.DeallocableRef(ref)
    ensures self.Inv()
    ensures self.TrackingGarbage()
    ensures self.graph == MapRemove1(old_self.graph, ref)
    ensures self.locs == MapRemove1(old_self.locs, ref)
    ensures (ref in self.locs ==> oldLoc == Some(self.locs[ref]))
    ensures (ref !in self.locs ==> oldLoc == None)
    {
      TCountEqGraphSize(self.t);
      // TODO LemmaRemoveRefStuff(I(me), ref);

      var oldEntry := LinearMutableMap.RemoveAndGet(inout self.t, ref);

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

      // ?? inout self.garbageQueue.value.Remove(ref);
      assert RefcountUpdateInv(old_self.t, old_self.garbageQueue.value.I(), ref, [], oldEntry.value.succs, 0, 0);
      UpdatePredCounts(inout self, ref, [], oldEntry.value.succs);

      TCountEqGraphSize(self.t);

      oldLoc := if oldEntry.Some? then oldEntry.value.loc else None;
      inout self.findLoclessIterator := None;

      inout self.UpdateGhost();
    }

    static predicate UnchangedExceptTAndGarbageQueue(old_self: IndirectionTable, self: IndirectionTable) {
      && old_self.refUpperBound       == self.refUpperBound
      && old_self.findLoclessIterator == self.findLoclessIterator
      && old_self.locs                == self.locs
      && old_self.graph               == self.graph
      && old_self.predCounts          == self.predCounts
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
    // ?? ensures ref !in self.garbageQueue.value.I()
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
    {
      var oldEntryOpt := LinearMutableMap.Get(self.t, ref);
      var oldEntry := oldEntryOpt.value;
      var newEntry := oldEntry.(predCount := oldEntry.predCount - 1);
      LinearMutableMap.Insert(inout self.t, ref, newEntry);
      if oldEntry.predCount == 1 {
        inout self.garbageQueue.value.Add(ref);
      }
    }

    // lemma LemmaUpdatePredCountsIncStuff(
    //     t: HashMap,
    //     q: GarbageQueueModel,
    //     changingRef: BT.G.Reference,
    //     newSuccs: seq<BT.G.Reference>,
    //     oldSuccs: seq<BT.G.Reference>,
    //     idx: int)
    // requires RefcountUpdateInv(t, q, changingRef, newSuccs, oldSuccs, idx, 0)
    // requires GarbageQueueInv(q)
    // ensures idx < |newSuccs| ==> newSuccs[idx] in t.contents
    // ensures idx < |newSuccs| ==> t.contents[newSuccs[idx]].predCount < 0xffff_ffff_ffff_ffff
    // ensures idx < |newSuccs| ==>
    //   var (t', q') := PredInc(t, q, newSuccs[idx]);
    //   && RefcountUpdateInv(t', q', changingRef, newSuccs, oldSuccs, idx + 1, 0)
    //   && GarbageQueueInv(q')
    // ensures LinearMutableMap.Inv(t)
    // ensures 0 <= idx <= |newSuccs|
    // {
    //   if idx < |newSuccs| {
    //     var graph := Graph(t);

    //     assert newSuccs[idx] in graph;
    //     assert newSuccs[idx] in t.contents;

    //     var ref := newSuccs[idx];
    //     assert t.contents[ref].predCount as int
    //       == |PredecessorSet(graph, ref)| + IsRoot(ref)
    //         - SeqCount(newSuccs, ref, idx)
    //         + SeqCount(oldSuccs, ref, 0);

    //     SeqCountInc(newSuccs, ref, idx);
    //     assert SeqCount(newSuccs, ref, idx + 1)
    //         == SeqCount(newSuccs, ref, idx) - 1;

    //     lemma_count_eq_graph_size(t);
    //     PredecessorSetSizeBound(graph, ref);
    //     SeqCountBound(oldSuccs, ref, 0);
    //     assert t.contents[ref].predCount < 0xffff_ffff_ffff_ffff;

  ////       assert t.contents[ref].predCount != 0;
    //     
    //     var (t', q') := PredInc(t, q, newSuccs[idx]);
    //     // assert GarbageQueueInv(q') by {
    //     //   reveal_NoDupes();
    //     //   var _ := RemoveValueMultiset(q, ref);
    //     // }
    //     assert Graph(t) == Graph(t');

    //     var predCounts := PredCounts(t);
    //     var predCounts' := PredCounts(t');
    //     forall r | r in predCounts'
    //     ensures predCounts'[r] == |PredecessorSet(graph, r)| + IsRoot(r)
    //         - SeqCount(newSuccs, r, idx + 1)
    //         + SeqCount(oldSuccs, r, 0)
    //     {
    //       if r == ref {
    //       } else {
    //         SeqCountIncOther(newSuccs, r, idx);
    //       }
    //     }

    //     // LruModel.LruRemove(q, ref);
    //   }
    // }

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

    linear inout method UpdatePredCounts(ghost changingRef: BT.G.Reference, newSuccs: seq<BT.G.Reference>, oldSuccs: seq<BT.G.Reference>)
    requires old_self.t.Inv()
    requires old_self.TrackingGarbage()
    requires old_self.garbageQueue.value.Inv()
    requires RefcountUpdateInv(old_self.t, old_self.garbageQueue.value.I(), changingRef, newSuccs, oldSuccs, 0, 0)
    ensures self.t.Inv()
    ensures self.TrackingGarbage()
    ensures self.garbageQueue.value.Inv()
    ensures RefcountUpdateInv(self.t, self.garbageQueue.value.I(), changingRef, newSuccs, oldSuccs, |newSuccs|, |oldSuccs|)
    ensures UnchangedExceptTAndGarbageQueue(old_self, self)
    {
      var idx: uint64 := 0;

      while idx < |newSuccs| as uint64
      invariant self.t.Inv()
      invariant self.TrackingGarbage()
      invariant self.garbageQueue.value.Inv()
      invariant RefcountUpdateInv(self.t, self.garbageQueue.value.I(), changingRef, newSuccs, oldSuccs, idx as int, 0)
      // invariant IndirectionTableModel.UpdatePredCountsInc(t, USeq.I(q), changingRef, newSuccs, oldSuccs, 0)
      //        == IndirectionTableModel.UpdatePredCountsInc(t', USeq.I(self.garbageQueue.value), changingRef, newSuccs, oldSuccs, idx)
      invariant UnchangedExceptTAndGarbageQueue(old_self, self)
      decreases |newSuccs| - idx as int
      {
        var ref := newSuccs[idx];

        ghost var graph := Graph(self.t);

        assert ref in graph;
        assert ref in self.t.contents;

        inout self.PredInc(ref);
        idx := idx + 1;

        assert RefcountUpdateInv(self.t, self.garbageQueue.value.I(), changingRef, newSuccs, oldSuccs, idx as int, 0);
      }

      var idx2: uint64 := 0;

      while idx2 < |oldSuccs| as uint64
      invariant self.t.Inv()
      invariant self.TrackingGarbage()
      invariant self.garbageQueue.value.Inv()
      invariant RefcountUpdateInv(self.t, self.garbageQueue.value.I(), changingRef, newSuccs, oldSuccs, |newSuccs|, idx2 as int)
      // invariant IndirectionTableModel.UpdatePredCountsInc(t, USeq.I(q), changingRef, newSuccs, oldSuccs, 0)
      //        == IndirectionTableModel.UpdatePredCountsDec(t', USeq.I(self.garbageQueue.value), changingRef, newSuccs, oldSuccs, idx2)
      invariant UnchangedExceptTAndGarbageQueue(old_self, self)
      decreases |oldSuccs| - idx2 as int
      {
        // PredDec model
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
        // end

        // TODO IndirectionTableModel.LemmaUpdatePredCountsDecStuff(t', USeq.I(self.garbageQueue.value), changingRef, newSuccs, oldSuccs, idx2 as int);
        assert oldSuccs[idx2] in self.t.contents;
        assert self.t.contents[oldSuccs[idx2]].predCount > 0;
        assert |self.garbageQueue.value.I()| <= 0x1_0000_0000;

        ghost var old_t := self.t;
        inout self.PredDec(oldSuccs[idx2]);

        //x
        if old_t.contents[ref].predCount == 1 {
          assert NoDupes([ref]) by { reveal_NoDupes(); }
          assume ref !in self.garbageQueue.value.I();
          DisjointConcatenation(self.garbageQueue.value.I(), [ref]);
        }
        assert Graph(old_t) == Graph(self.t);

        ghost var predCounts := PredCounts(old_t);
        ghost var predCounts' := PredCounts(self.t);
        forall r | r in predCounts'
        ensures predCounts'[r] == |PredecessorSet(graph, r)| + IsRoot(r)
            - SeqCount(newSuccs, r, |newSuccs| as nat)
            + SeqCount(oldSuccs, r, idx2 as nat + 1)
        {
          if r == ref {
          } else {
            SeqCountIncOther(oldSuccs, r, idx2 as nat);
            assert SeqCount(oldSuccs, r, idx2 as nat) == SeqCount(oldSuccs, r, idx2 as nat + 1);
          }
        }
        //x

        idx2 := idx2 + 1;
        assert RefcountUpdateInv(self.t, self.garbageQueue.value.I(), changingRef, newSuccs, oldSuccs, |newSuccs|, idx2 as int);
      }
    }

    // static method UpdateAndRemoveLoc(linear me: IndirectionTable, ref: BT.G.Reference, succs: seq<BT.G.Reference>)
    // returns (linear self: IndirectionTable, oldLoc : Option<Location>)
    // requires Inv(me)
    // requires IndirectionTableModel.TrackingGarbage(I(me))
    // requires |succs| <= MaxNumChildren()
    // requires |I(me).graph| < IndirectionTableModel.MaxSize()
    // requires IndirectionTableModel.SuccsValid(succs, I(me).graph)
    // ensures Inv(self)
    // ensures (I(self), oldLoc)  == IndirectionTableModel.UpdateAndRemoveLoc(I(me), ref, succs)
    // {
    //   IndirectionTableModel.reveal_UpdateAndRemoveLoc();

    //   IndirectionTableModel.lemma_count_eq_graph_size(I(me).t);
    //   IndirectionTableModel.LemmaUpdateAndRemoveLocStuff(I(me), ref, succs);

    //   linear var IndirectionTable(t, lSome(garbageQueue), refUpperBound, findLoclessIterator) := me;
    //   var oldEntry := LinearMutableMap.Get(t, ref);
    //   var predCount := if oldEntry.Some? then oldEntry.value.predCount else 0;
    //   if oldEntry.None? {
    //     garbageQueue := USeq.Add(garbageQueue, ref);
    //   }
    //   t := LinearMutableMap.Insert(t, ref, Entry(None, succs, predCount));

    //   IndirectionTableModel.lemma_count_eq_graph_size(me.t);

    //   t, garbageQueue := UpdatePredCounts(t, garbageQueue, ref, succs,
    //       if oldEntry.Some? then oldEntry.value.succs else []);

    //   IndirectionTableModel.lemma_count_eq_graph_size(me.t);

    //   //IndirectionTableModel.LemmaValidPredCountsOfValidPredCountsIntermediate(IndirectionTableModel.PredCounts(me.t), IndirectionTableModel.Graph(me.t), succs, if oldEntry.Some? then oldEntry.value.succs else []);

    //   if ref > refUpperBound {
    //     refUpperBound := ref;
    //   }

    //   oldLoc := if oldEntry.Some? && oldEntry.value.loc.Some? then oldEntry.value.loc else None;
    //   findLoclessIterator := None;

    //   ghost var _ := IndirectionTableModel.UpdateAndRemoveLoc(I(me), ref, succs);
    //   self := IndirectionTable(t, lSome(garbageQueue), refUpperBound, findLoclessIterator);
    // }

    // // Parsing and marshalling

    // static lemma lemma_valToHashMapNonePrefix(a: seq<V>, i: int)
    // requires IndirectionTableModel.valToHashMap.requires(a)
    // requires 0 <= i <= |a|
    // requires IndirectionTableModel.valToHashMap(a[..i]).None?
    // ensures IndirectionTableModel.valToHashMap(a).None?
    // decreases |a| - i
    // {
    //   if (i == |a|) {
    //     assert a[..i] == a;
    //   } else {
    //     assert IndirectionTableModel.valToHashMap(a[..i+1]).None? by {
    //       assert DropLast(a[..i+1]) == a[..i];
    //       assert Last(a[..i+1]) == a[i];
    //     }
    //     lemma_valToHashMapNonePrefix(a, i+1);
    //   }
    // }
  

    // static method {:fuel ValInGrammar,3} ValToHashMap(a: seq<V>) returns (linear s : lOption<HashMap>)
    // requires IndirectionTableModel.valToHashMap.requires(a)
    // ensures s.lNone? ==> IndirectionTableModel.valToHashMap(a).None?
    // ensures s.lSome? ==> s.value.Inv()
    // ensures s.lSome? ==> Some(s.value) == IndirectionTableModel.valToHashMap(a)
    // ensures s.lSome? ==> s.value.count as nat == |a|
    // ensures s.lSome? ==> s.value.count as nat < 0x1_0000_0000_0000_0000 / 8
    // {
    //   var i: uint64 := 0;
    //   var success := true;
    //   linear var mutMap := LinearMutableMap.Constructor<Entry>(1024); // TODO(alattuada) magic numbers

    //   while i < |a| as uint64
    //   invariant 0 <= i as int <= |a|
    //   invariant mutMap.Inv()
    //   invariant IndirectionTableModel.valToHashMap(a[..i]) == Some(mutMap)
    //   {
    //     var tuple := a[i];
    //     var ref := tuple.t[0 as uint64].u;
    //     var addr := tuple.t[1 as uint64].u;
    //     var len := tuple.t[2 as uint64].u;
    //     var succs := tuple.t[3 as uint64].ua;
    //     var graphRef := LinearMutableMap.Get(mutMap, ref);
    //     var loc := Location(addr, len);

    //     assert ValidVal(tuple);
    //     assert ValidVal(tuple.t[3]);
    //     assert |succs| < 0x1_0000_0000_0000_0000;

    //     assert DropLast(a[..i+1]) == a[..i];
    //     assert Last(a[..i+1]) == a[i];

    //     if graphRef.Some? || !ValidNodeLocation(loc)
    //         || |succs| as uint64 > MaxNumChildrenUint64() {
    //       lemma_valToHashMapNonePrefix(a, (i+1) as int);
    //       success := false;
    //       break;
    //     } else {
    //       mutMap := LinearMutableMap.Insert(mutMap, ref, Entry(Some(loc), succs, 0));
    //       i := i + 1;
    //     }
    //   }

    //   if success {
    //     assert a[..i] == a;
    //     s := lSome(mutMap);
    //   } else {
    //     LinearMutableMap.Destructor(mutMap);
    //     s := lNone;
    //   }
    // }

    // static method ComputeRefCounts(shared t: HashMap)
    //   returns (linear t' : lOption<HashMap>)
    //   requires t.Inv()
    //   requires forall ref | ref in t.contents :: t.contents[ref].predCount == 0
    //   requires forall ref | ref in t.contents :: |t.contents[ref].succs| <= MaxNumChildren()
    //   requires t.count as int <= IndirectionTableModel.MaxSize()
    //   requires BT.G.Root() in t.contents
    //   ensures match t' {
    //     case lNone => IndirectionTableModel.ComputeRefCounts(t) == None
    //     case lSome(t'') => t''.Inv() && IndirectionTableModel.ComputeRefCounts(t) == Some(t'')
    //   }
    // {
    //   IndirectionTableModel.LemmaComputeRefCountsIterateInvInit(t);

    //   shared var copy := t;
    //   linear var t1 := LinearMutableMap.Clone(t);

    //   var oldEntryOpt := LinearMutableMap.Get(t1, BT.G.Root());
    //   var oldEntry := oldEntryOpt.value;
    //   t1 := LinearMutableMap.Insert(t1, BT.G.Root(), oldEntry.(predCount := 1));

    //   var it := LinearMutableMap.IterStart(copy);
    //   var success := true;
    //   while it.next.Next?
    //   invariant t1.Inv()
    //   invariant copy.Inv()
    //   invariant IndirectionTableModel.ComputeRefCountsIterateInv(t1, copy, it)
    //   invariant BT.G.Root() in t1.contents
    //   invariant IndirectionTableModel.ComputeRefCounts(old(t))
    //          == IndirectionTableModel.ComputeRefCountsIterate(t1, copy, it)
    //   decreases it.decreaser
    //   {
    //     IndirectionTableModel.LemmaComputeRefCountsIterateStuff(t1, copy, it);
    //     IndirectionTableModel.LemmaComputeRefCountsIterateValidPredCounts(t1, copy, it);

    //     ghost var t0 := t1;

    //     var succs := it.next.value.succs;
    //     var i: uint64 := 0;
    //     while i < |succs| as uint64
    //     invariant t1.Inv()
    //     invariant copy.Inv()
    //     invariant BT.G.Root() in t1.contents
    //     invariant 0 <= i as int <= |succs|
    //     invariant |succs| <= MaxNumChildren()
    //     invariant t1.count as int <= IndirectionTableModel.MaxSize()
    //     invariant forall ref | ref in t1.contents :: t1.contents[ref].predCount as int <= 0x1_0000_0000_0000 + i as int
    //     invariant IndirectionTableModel.ComputeRefCounts(old(t))
    //            == IndirectionTableModel.ComputeRefCountsIterate(t0, copy, it)
    //     invariant IndirectionTableModel.ComputeRefCountsEntryIterate(t0, succs, 0)
    //            == IndirectionTableModel.ComputeRefCountsEntryIterate(t1, succs, i)
    //     decreases |succs| - i as int
    //     {
    //       var ref := succs[i];
    //       var oldEntry := LinearMutableMap.Get(t1, ref);
    //       if oldEntry.Some? {
    //         var newEntry := oldEntry.value.(predCount := oldEntry.value.predCount + 1);
    //         t1 := LinearMutableMap.Insert(t1, ref, newEntry);
    //         i := i + 1;
    //       } else {
    //         success := false;
    //         break break;
    //       }
    //     }

    //     it := LinearMutableMap.IterInc(copy, it);
    //   }

    //   if success {
    //     t' := lSome(t1);
    //   } else {
    //     LinearMutableMap.Destructor(t1);
    //     t' := lNone;
    //   }
    // }

    // static method MakeGarbageQueue(shared t: HashMap)
    // returns (linear q : USeq.USeq)
    // requires t.Inv()
    // requires |t.contents| <= 0x1_0000_0000
    // ensures USeq.Inv(q)
    // ensures USeq.I(q) == IndirectionTableModel.makeGarbageQueue(t)
    // {
    //   IndirectionTableModel.reveal_makeGarbageQueue();

    //   q := USeq.Alloc();
    //   var it := LinearMutableMap.IterStart(t);
    //   while it.next.Next?
    //   invariant USeq.Inv(q)
    //   invariant LinearMutableMap.Inv(t)
    //   invariant LinearMutableMap.WFIter(t, it)
    //   invariant IndirectionTableModel.makeGarbageQueue(t)
    //          == IndirectionTableModel.makeGarbageQueueIterate(t, USeq.I(q), it)
    //   invariant Set(USeq.I(q)) <= t.contents.Keys
    //   invariant |t.contents| <= 0x1_0000_0000
    //   decreases it.decreaser
    //   {
    //     if it.next.value.predCount == 0 {
    //       NoDupesSetCardinality(USeq.I(q));
    //       SetInclusionImpliesSmallerCardinality(
    //           Set(USeq.I(q)), t.contents.Keys);
    //       assert |t.contents.Keys| == |t.contents|;

    //       q := USeq.Add(q, it.next.key);
    //     }
    //     it := LinearMutableMap.IterInc(t, it);
    //   }
    // }

    // static method ComputeRefUpperBound(shared t: HashMap)
    // returns (r: uint64)
    // requires t.Inv()
    // ensures r == IndirectionTableModel.computeRefUpperBound(t)
    // {
    //   var it := LinearMutableMap.IterStart(t);
    //   var refUpperBound := 0;
    //   while it.next.Next?
    //   invariant LinearMutableMap.Inv(t)
    //   invariant LinearMutableMap.WFIter(t, it)
    //   invariant forall ref | ref in it.s :: ref <= refUpperBound
    //   invariant IndirectionTableModel.computeRefUpperBoundIterate(t, it, refUpperBound)
    //          == IndirectionTableModel.computeRefUpperBound(t)
    //   decreases it.decreaser
    //   {
    //     if it.next.key > refUpperBound {
    //       refUpperBound := it.next.key;
    //     }
    //     it := LinearMutableMap.IterInc(t, it);
    //   }
    //   r := refUpperBound;
    // }

    // static method ValToIndirectionTable(v: V)
    // returns (linear s : lOption<IndirectionTable>)
    // requires IndirectionTableModel.valToIndirectionTable.requires(v)
    // ensures s.lSome? ==> Inv(s.value)
    // ensures s.lNone? ==> IndirectionTableModel.valToIndirectionTable(v).None?
    // ensures s.lSome? ==> IndirectionTableModel.valToIndirectionTable(v) == Some(I(s.value))
    // {
    //   if |v.a| as uint64 <= IndirectionTableModel.MaxSizeUint64() {
    //     linear var res := ValToHashMap(v.a);
    //     linear match res {
    //       case lSome(t) => {
    //         var rootRef := LinearMutableMap.Get(t, BT.G.Root());
    //         if rootRef.Some? {
    //           linear var t1opt := ComputeRefCounts(t);
    //           LinearMutableMap.Destructor(t);
    //           linear match t1opt {
    //             case lSome(t1) => {
    //               IndirectionTableModel.lemmaMakeGarbageQueueCorrect(t1);
    //               IndirectionTableModel.lemma_count_eq_graph_size(t);
    //               IndirectionTableModel.lemma_count_eq_graph_size(t1);

    //               linear var q := MakeGarbageQueue(t1);
    //               var refUpperBound := ComputeRefUpperBound(t1);
    //               s := lSome(IndirectionTable(t1, lSome(q), refUpperBound, None));
    //             }
    //             case lNone => {
    //               s := lNone;
    //             }
    //           }
    //         } else {
    //           LinearMutableMap.Destructor(t);
    //           s := lNone;
    //         }
    //       }
    //       case lNone => {
    //         s := lNone;
    //       }
    //     }
    //   } else {
    //     s := lNone;
    //   }
    // }

    // static function MaxIndirectionTableByteSize() : int {
    //   8 + IndirectionTableModel.MaxSize() * (8 + 8 + 8 + (8 + MaxNumChildren() * 8))
    // }

    // static lemma lemma_SeqSum_prefix_array(a: array<V>, i: int)
    // requires 0 < i <= a.Length
    // ensures SeqSum(a[..i-1]) + SizeOfV(a[i-1]) == SeqSum(a[..i])
    // {
    //   lemma_SeqSum_prefix(a[..i-1], a[i-1]);
    //   assert a[..i-1] + [a[i-1]] == a[..i];
    // }

    // static lemma {:fuel SizeOfV,5} lemma_tuple_size(a: uint64, b: uint64, c: uint64, succs: seq<BT.G.Reference>)
    // requires|succs| <= MaxNumChildren()
    // ensures SizeOfV(VTuple([VUint64(a), VUint64(b), VUint64(c), VUint64Array(succs)]))
    //      == (8 + 8 + 8 + (8 + |succs| * 8))
    // {
    // }

    // static lemma lemma_SeqSum_empty()
    // ensures SeqSum([]) == 0;
    // {
    //   reveal_SeqSum();
    // }

    // // method marshallIndirectionTableRow(
    // //     data: array<byte>,
    // //     start: uint64,
    // //     next: MutableMapModel.IteratorOutput<Entry>)
    // // returns (end: uint64)
    // // modifies data
    // // requires 0 <= start as int <= data.Length
    // // requires data.Length < 0x1_0000_0000_0000_0000
    // // requires next.Next?
    // // requires next.value.loc.Some?
    // // requires |next.value.succs| <= MaxNumChildren()
    // // ensures end != 0 ==>
    // //   && start as int <= end as int <= data.Length
    // //   && parse_Val(data[start..end],
    // //     Marshalling.IndirectionTableRowGrammar()).0
    // //       == Some(VTuple([
    // //           VUint64(next.key),
    // //           VUint64(next.value.loc.value.addr),
    // //           VUint64(next.value.loc.value.len),
    // //           VUint64Array(next.value.succs)
    // //          ]))
    // // {
    // //   if 8 + 8 + 8 + 8 + 8*|next.value.succs| as uint64
    // //         > data.Length as uint64 - start
    // //   {
    // //     return 0;
    // //   }

    // //   var idx0 := start;
    // //   ghost var data0 := data[..];

    // //   Pack_LittleEndian_Uint64_into_Array(next.key, data, idx0);
    // //   var idx1 := idx0 + 8;

    // //   ghost var data1 := data[..];

    // //   Pack_LittleEndian_Uint64_into_Array(next.value.loc.value.addr, data, idx1);
    // //   var idx2 := idx1 + 8;

    // //   ghost var data2 := data[..];

    // //   Pack_LittleEndian_Uint64_into_Array(next.value.loc.value.len, data, idx2);
    // //   var idx3 := idx2 + 8;

    // //   ghost var data3 := data[..];

    // //   Pack_LittleEndian_Uint64_into_Array(
    // //       |next.value.succs| as uint64, data, idx3);
    // //   var idx4 := idx3 + 8;

    // //   ghost var data4 := data[..];

    // //   Pack_LittleEndian_Uint64_Seq_into_Array(
    // //       next.value.succs, data, idx4);
    // //   var idx5 := idx4 + 8 * |next.value.succs| as uint64;

    // //   ghost var data5 := data[..];

    // //   end := idx5;

    // //   calc {
    // //     parse_Val(data5[idx3..idx5], GUint64Array).0;
    // //     { reveal_parse_Val(); }
    // //     parse_Uint64Array(data5[idx3..idx5]).0;
    // //     {
    // //       assert unpack_LittleEndian_Uint64(data5[idx3..idx5][..8])
    // //          == |next.value.succs| as uint64 by {
    // //         assert data5[idx3..idx5][..8]
    // //             == data5[idx3..idx4]
    // //             == data4[idx3..idx4];
    // //       }
    // //       var len := |next.value.succs| as uint64;
    // //       assert unpack_LittleEndian_Uint64_Seq(data5[idx3..idx5][8..8 + 8*len], len as int)
    // //         == next.value.succs by {
    // //         assert data5[idx3..idx5][8..8+8*len] == data5[idx4..idx5];
    // //       }
    // //     }
    // //     Some(VUint64Array(next.value.succs));
    // //   }

    // //   calc {
    // //     parse_Val(data5[idx2..idx5], GUint64).0;
    // //     { reveal_parse_Val(); }
    // //     parse_Uint64(data5[idx2..idx5]).0;
    // //     {
    // //       calc {
    // //         data5[idx2..idx5][..8];
    // //         data4[idx2..idx3];
    // //         data3[idx2..idx3];
    // //       }
    // //     }
    // //     Some(VUint64(next.value.loc.value.len));
    // //   }

    // //   calc {
    // //     parse_Val(data5[idx1..idx5], GUint64).0;
    // //     { reveal_parse_Val(); }
    // //     parse_Uint64(data5[idx1..idx5]).0;
    // //     {
    // //       calc {
    // //         data5[idx1..idx5][..8];
    // //         { lemma_seq_slice_slice(data5, idx1 as int, idx5 as int, 0, 8); }
    // //         data5[idx1..idx2];
    // //         data4[idx1..idx2];
    // //         data3[idx1..idx2];
    // //         data2[idx1..idx2];
    // //       }
    // //     }
    // //     Some(VUint64(next.value.loc.value.addr));
    // //   }

    // //   calc {
    // //     parse_Val(data5[idx0..idx5], GUint64).0;
    // //     { reveal_parse_Val(); }
    // //     parse_Uint64(data5[idx0..idx5]).0;
    // //     {
    // //       calc {
    // //         data5[idx0..idx5][..8];
    // //         {
    // //           lemma_seq_slice_slice(data5, idx0 as int, idx5 as int, 0, 8);
    // //         }
    // //         data4[idx0..idx1];
    // //         data3[idx0..idx1];
    // //         data2[idx0..idx1];
    // //         data1[idx0..idx1];
    // //       }
    // //     }
    // //     Some(VUint64(next.key));
    // //   }

    // //   ghost var sl := data5[idx0..idx5];

    // //   calc {
    // //     [
    // //       VUint64(next.key),
    // //       VUint64(next.value.loc.value.addr),
    // //       VUint64(next.value.loc.value.len),
    // //       VUint64Array(next.value.succs)
    // //     ];
    // //     {
    // //       assert sl == data5[idx0..idx5];
    // //       assert sl[8..] == data5[idx1..idx5];
    // //       assert sl[16..] == data5[idx2..idx5];
    // //       assert sl[24..] == data5[idx3..idx5];
    // //       var x := [parse_Val(sl, GUint64).0.value] + [parse_Val(sl[8..], GUint64).0.value] + [parse_Val(sl[16..], GUint64).0.value] + [parse_Val(sl[24..], GUint64Array).0.value] + [];
    // //       assert VUint64(next.key) == parse_Val(sl, GUint64).0.value;
    // //       assert VUint64(next.value.loc.value.addr) == parse_Val(sl[8..], GUint64).0.value;
    // //       assert VUint64(next.value.loc.value.len) == parse_Val(sl[16..], GUint64).0.value;
    // //       assert VUint64Array(next.value.succs) == parse_Val(sl[24..], GUint64Array).0.value;
    // //     }
    // //     [parse_Val(sl, GUint64).0.value, parse_Val(sl[8..], GUint64).0.value, parse_Val(sl[16..], GUint64).0.value, parse_Val(sl[24..], GUint64Array).0.value];
    // //     [parse_Val(sl, GUint64).0.value] + [parse_Val(sl[8..], GUint64).0.value] + [parse_Val(sl[16..], GUint64).0.value] + [parse_Val(sl[24..], GUint64Array).0.value] + [];
    // //     {
    // //       reveal_parse_Tuple_contents();
    // //       assert parse_Tuple_contents(sl[idx5-idx0..], []).0.value == [];
    // //     }
    // //     [parse_Val(sl, GUint64).0.value] + [parse_Val(sl[8..], GUint64).0.value] + [parse_Val(sl[16..], GUint64).0.value] + [parse_Val(sl[24..], GUint64Array).0.value] + parse_Tuple_contents(sl[idx5-idx0..], []).0.value;
    // //     {
    // //       reveal_parse_Tuple_contents();
    // //       reveal_parse_Val();
    // //       assert sl[24..][idx5-idx3..] == sl[idx5-idx0..];
    // //     }
    // //     [parse_Val(sl, GUint64).0.value] + [parse_Val(sl[8..], GUint64).0.value] + [parse_Val(sl[16..], GUint64).0.value] + parse_Tuple_contents(sl[24..], [GUint64Array]).0.value;
    // //     {
    // //       reveal_parse_Tuple_contents();
    // //       reveal_parse_Val();
    // //       assert sl[16..][8..] == sl[24..];
    // //     }
    // //     [parse_Val(sl, GUint64).0.value] + [parse_Val(sl[8..], GUint64).0.value] + parse_Tuple_contents(sl[16..], [GUint64, GUint64Array]).0.value;
    // //     {
    // //       reveal_parse_Tuple_contents();
    // //       reveal_parse_Val();
    // //       assert sl[8..][8..] == sl[16..];
    // //     }
    // //     [parse_Val(sl, GUint64).0.value] + parse_Tuple_contents(sl[8..], [GUint64, GUint64, GUint64Array]).0.value;
    // //     {
    // //       reveal_parse_Tuple_contents();
    // //       reveal_parse_Val();
    // //     }
    // //     parse_Tuple_contents(sl, [GUint64, GUint64, GUint64, GUint64Array]).0.value;
    // //   }

    // //   calc {
    // //     Some(VTuple([
    // //       VUint64(next.key),
    // //       VUint64(next.value.loc.value.addr),
    // //       VUint64(next.value.loc.value.len),
    // //       VUint64Array(next.value.succs)
    // //     ]));
    // //     { reveal_parse_Val(); }
    // //     parse_Val(sl, Marshalling.IndirectionTableRowGrammar()).0;
    // //   }
    // // }

    // // method marshallIndirectionTableContents(data: array<byte>, start: uint64)
    // // returns (end: uint64)
    // // requires Inv(me)
    // // requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I(me)))

    // // requires 0 <= start as int <= data.Length
    // // requires data.Length < 0x1_0000_0000_0000_0000

    // // modifies data

    // // ensures end != 0 ==>
    // //   && start as int <= end as int <= data.Length
    // //   && Marshalling.valToIndirectionTableMaps(
    // //        parse_Array_contents(
    // //          data[start..end],
    // //          Marshalling.IndirectionTableRowGrammar(),
    // //          t.Count
    // //        )
    // //      ) == IndirectionTableModel.I(I(me))
    // // {
    // //   var idx := start;
    // //   var it := t.IterStart();
    // //   while it.next.Next?
    // //   {
    // //   }
    // // }

    // // method marshallIndirectionTable(data: array<byte>, start_idx: uint64)
    // // returns (end: uint64)
    // // requires Inv(me)
    // // requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I(me)))
    // // modifies data
    // // {
    // //   var idx := start_idx;

    // //   Pack_LittleEndian_Uint64_into_Array(t.Count, data, idx);
    // //   idx := idx + 8;

    // //   var it := t.IterStart();
    // //   while it.next.Next?
    // //   {
    // //     if idx + 8 + 8 + 8 + 8 + 8*|it.next.value.succs| as uint64
    // //         > data.Length as uint64
    // //     {
    // //       return 0;
    // //     }

    // //     Pack_LittleEndian_Uint64_into_Array(it.next.key, data, idx);
    // //     idx := idx + 8;

    // //     Pack_LittleEndian_Uint64_into_Array(it.next.value.loc.value.addr, data, idx);
    // //     idx := idx + 8;

    // //     Pack_LittleEndian_Uint64_into_Array(it.next.value.loc.value.len, data, idx);
    // //     idx := idx + 8;

    // //     Pack_LittleEndian_Uint64_into_Array(
    // //         |it.next.value.succs| as uint64, data, idx);
    // //     idx := idx + 8;

    // //     Pack_LittleEndian_Uint64_Seq_into_Array(
    // //         it.next.value.succs, data, idx);
    // //     idx := idx + 8 * |it.next.value.succs| as uint64;
    // //     
    // //     it := t.IterInc(it);
    // //   }
    // //   return idx;
    // // }

    // // NOTE(travis): I found that the above method which marshalls
    // // directly from indirection table to bytes is much faster
    // // than converting to a V and using the GenericMarshalling
    // // framework. I did some work on proving it (above),
    // // but it's kind of annoying. However, I think that it won't
    // // be a big deal as long as most syncs are journaling syncs?
    // // So I've moved back to this one which is slower but cleaner.
    // static method IndirectionTableToVal(shared me: IndirectionTable)
    // returns (v : V, size: uint64)
    // requires Inv(me)
    // requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I(me)))
    // ensures ValInGrammar(v, IndirectionTableModel.IndirectionTableGrammar())
    // ensures ValidVal(v)
    // ensures IndirectionTableModel.valToIndirectionTable(v).Some?
    // ensures
    //       IndirectionTableModel.I(IndirectionTableModel.valToIndirectionTable(v).value)
    //    == IndirectionTableModel.I(I(me))
    // ensures SizeOfV(v) <= MaxIndirectionTableByteSize()
    // ensures SizeOfV(v) == size as int
    // {
    //   assert me.t.count <= IndirectionTableModel.MaxSizeUint64();
    //   lemma_SeqSum_empty();
    //   var count := me.t.count as uint64;
    //   var a: array<V> := new V[count];
    //   var it := LinearMutableMap.IterStart(me.t);
    //   var i: uint64 := 0;
    //   size := 0;

    //   ghost var partial := map[];
    //   while it.next.Next?
    //   invariant Inv(me)
    //   invariant BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I(me)))
    //   invariant 0 <= i as int <= a.Length
    //   invariant LinearMutableMap.WFIter(me.t, it);
    //   invariant forall j | 0 <= j < i :: ValidVal(a[j])
    //   invariant forall j | 0 <= j < i :: ValInGrammar(a[j], GTuple([GUint64, GUint64, GUint64, GUint64Array]))
    //   // NOALIAS/CONST table doesn't need to be mutable, if we could say so we wouldn't need this
    //   invariant IndirectionTableModel.valToHashMap(a[..i]).Some?
    //   invariant IndirectionTableModel.valToHashMap(a[..i]).value.contents == partial
    //   invariant |partial.Keys| == i as nat
    //   invariant partial.Keys == it.s
    //   invariant partial.Keys <= me.t.contents.Keys
    //   invariant forall r | r in partial :: r in me.t.contents
    //       && partial[r].loc == me.t.contents[r].loc
    //       && partial[r].succs == me.t.contents[r].succs
    //   // NOALIAS/CONST t doesn't need to be mutable, if we could say so we wouldn't need this
    //   invariant me.t.contents == old(me.t.contents)
    //   invariant size as int <=
    //       |it.s| * (8 + 8 + 8 + (8 + MaxNumChildren() * 8))
    //   invariant SeqSum(a[..i]) == size as int;
    //   decreases it.decreaser
    //   {
    //     var (ref, locOptGraph: Entry) := (it.next.key, it.next.value);
    //     assert ref in I(me).locs;
    //     // NOTE: deconstructing in two steps to work around c# translation bug
    //     var locOpt := locOptGraph.loc;
    //     var succs := locOptGraph.succs;
    //     var loc := locOpt.value;
    //     //ghost var predCount := locOptGraph.predCount;
    //     var childrenVal := VUint64Array(succs);

    //     assert |succs| <= MaxNumChildren();

    //     //assert I(me).locs[ref] == loc;
    //     //assert I(me).graph[ref] == succs;

    //     //assert IndirectionTableModel.I(I(me)).locs[ref] == loc;
    //     //assert IndirectionTableModel.I(I(me)).graph[ref] == succs;

    //     assert ValidNodeLocation(loc);
    //     /*ghost var t0 := IndirectionTableModel.valToHashMap(a[..i]);
    //     assert ref !in t0.value.contents;
    //     assert loc.addr != 0;
    //     assert LBAType.ValidLocation(loc);*/

    //     LinearMutableMap.LemmaIterIndexLtCount(me.t, it);

    //     assert |succs| < 0x1_0000_0000_0000_0000;
    //     assert ValidVal(VTuple([VUint64(ref), VUint64(loc.addr), VUint64(loc.len), childrenVal]));

    //     assert |LinearMutableMap.IterInc(me.t, it).s| == |it.s| + 1;

    //     var vi := VTuple([VUint64(ref), VUint64(loc.addr), VUint64(loc.len), childrenVal]);

    //     //assert SizeOfV(vi) <= (8 + 8 + 8 + (8 + MaxNumChildren() * 8));

    //     // == mutation ==
    //     partial := partial[ref := Entry(locOpt, succs, 0)];
    //     a[i] := vi;
    //     i := i + 1;
    //     it := LinearMutableMap.IterInc(me.t, it);
    //     // ==============

    //     assert a[..i-1] == DropLast(a[..i]); // observe

    //     calc {
    //       SeqSum(a[..i]);
    //       {
    //         lemma_SeqSum_prefix_array(a, i as int);
    //       }
    //       SeqSum(a[..i-1]) + SizeOfV(a[i-1]);
    //       SeqSum(a[..i-1]) + SizeOfV(vi);
    //       {
    //         lemma_tuple_size(ref, loc.addr, loc.len, succs);
    //       }
    //       size as int + (8 + 8 + 8 + (8 + 8 * |succs|));
    //     }

    //     size := size + 32 + 8 * |succs| as uint64;
    //   }

    //   /* (doc) assert |partial.Keys| == |me.t.contents.Keys|; */
    //   SetInclusionAndEqualCardinalityImpliesSetEquality(partial.Keys, me.t.contents.Keys);

    //   assert a[..i] == a[..]; // observe
    //   v := VArray(a[..]);

    //   /*ghost var t0 := IndirectionTableModel.valToHashMap(v.value.a);
    //   assert t0.Some?;
    //   assert BT.G.Root() in t0.value.contents;
    //   assert t0.value.count <= MaxSizeUint64();
    //   ghost var t1 := IndirectionTableModel.ComputeRefCounts(t0.value);
    //   assert t1.Some?;*/

    //   assert |it.s| <= IndirectionTableModel.MaxSize();

    //   size := size + 8;
    // }

    // // To bitmap

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

    // static method BitmapInitUpTo(bm: BitmapImpl.Bitmap, upTo: uint64)
    // requires bm.Inv()
    // requires upTo as int <= BitmapModel.Len(bm.I())
    // modifies bm.Repr
    // ensures bm.Inv()
    // ensures bm.I() == IndirectionTableModel.BitmapInitUpTo(old(bm.I()), upTo)
    // ensures bm.Repr == old(bm.Repr)
    // {
    //   IndirectionTableModel.reveal_BitmapInitUpTo();
    //   BitmapInitUpToIterate(bm, 0, upTo);
    // }

    // static method InitLocBitmap(shared me: IndirectionTable)
    // returns (success: bool, bm: BitmapImpl.Bitmap)
    // requires Inv(me)
    // requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I(me)))
    // ensures bm.Inv()
    // ensures (success, bm.I()) == IndirectionTableModel.InitLocBitmap(old(I(me)))
    // ensures fresh(bm.Repr)
    // {
    //   IndirectionTableModel.reveal_InitLocBitmap();

    //   bm := new BitmapImpl.Bitmap(NumBlocksUint64());
    //   BitmapInitUpTo(bm, MinNodeBlockIndexUint64());
    //   var it := LinearMutableMap.IterStart(me.t);
    //   while it.next.Next?
    //   invariant me.t.Inv()
    //   invariant BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I(me)))
    //   invariant bm.Inv()
    //   invariant LinearMutableMap.WFIter(me.t, it)
    //   invariant BitmapModel.Len(bm.I()) == NumBlocks()
    //   invariant IndirectionTableModel.InitLocBitmapIterate(I(me), it, bm.I())
    //          == IndirectionTableModel.InitLocBitmap(I(me))
    //   invariant fresh(bm.Repr)
    //   decreases it.decreaser
    //   {
    //     assert it.next.key in IndirectionTableModel.I(I(me)).locs;

    //     var loc: uint64 := it.next.value.loc.value.addr;
    //     var locIndex: uint64 := loc / NodeBlockSizeUint64();
    //     if locIndex < NumBlocksUint64() {
    //       var isSet := bm.GetIsSet(locIndex);
    //       if !isSet {
    //         it := LinearMutableMap.IterInc(me.t, it);
    //         bm.Set(locIndex);
    //       } else {
    //         success := false;
    //         return;
    //       }
    //     } else {
    //       success := false;
    //       return;
    //     }
    //   }

    //   success := true;
    // }
    // 
    // ///// Dealloc stuff

    // static function method FindDeallocable(shared me: IndirectionTable) : (ref: Option<BT.G.Reference>)
    // requires Inv(me)
    // requires IndirectionTableModel.TrackingGarbage(I(me))
    // ensures ref == IndirectionTableModel.FindDeallocable(I(me))
    // {
    //   IndirectionTableModel.reveal_FindDeallocable();
    //   USeq.FirstOpt(me.garbageQueue.value)
    // }

    // static function method GetSize(shared me: IndirectionTable) : (size: uint64)
    // requires Inv(me)
    // ensures size as int == |I(me).graph|
    // {
    //   IndirectionTableModel.lemma_count_eq_graph_size(I(me).t);
    //   me.t.count
    // }

    // static method FindRefWithNoLoc(linear me: IndirectionTable) returns (linear self: IndirectionTable, ref: Option<BT.G.Reference>)
    // requires Inv(me)
    // ensures Inv(self)
    // ensures (I(self), ref) == IndirectionTableModel.FindRefWithNoLoc(I(me))
    // {
    //   IndirectionTableModel.reveal_FindRefWithNoLoc();

    //   linear var IndirectionTable(t, garbageQueue, refUpperBound, findLoclessIterator) := me;
    //   var it;
    //   if findLoclessIterator.Some? {
    //     it := findLoclessIterator.value;
    //   } else {
    //     it := LinearMutableMap.SimpleIterStart(t);
    //   }

    //   while true
    //   invariant Inv(me)
    //   invariant LinearMutableMap.WFSimpleIter(t, it)
    //   invariant forall r | r in it.s :: r in I(me).locs
    //   invariant IndirectionTableModel.FindRefWithNoLoc(I(me))
    //       == IndirectionTableModel.FindRefWithNoLocIterate(
    //           I(IndirectionTable(t, garbageQueue, refUpperBound, findLoclessIterator)), it)
    //   decreases it.decreaser
    //   {
    //     var next := LinearMutableMap.SimpleIterOutput(t, it);
    //     if next.Next? {
    //       if next.value.loc.None? {
    //         findLoclessIterator := Some(it);
    //         ref := Some(next.key);
    //         break;
    //       } else {
    //         it := LinearMutableMap.SimpleIterInc(t, it);
    //       }
    //     } else {
    //       findLoclessIterator := Some(it);
    //       ref := None;
    //       break;
    //     }
    //   }
    //   self := IndirectionTable(t, garbageQueue, refUpperBound, findLoclessIterator);
    // }

    // static function method GetRefUpperBound(shared me: IndirectionTable) : (r: uint64)
    // requires Inv(me)
    // ensures r == IndirectionTableModel.getRefUpperBound(I(me))
    // {
    //   IndirectionTableModel.reveal_getRefUpperBound();
    //   me.refUpperBound
    // }

    // ass IndirectionTable {
    // var box: BoxedLinear<IndirectionTable>;
    // ghost var Repr: set<object>;

    // function Read() : IndirectionTable
    //   requires box.Inv()
    //   reads this, box, box.Repr
    // {
    //   box.Read()
    // }

    // method DebugAccumulate() returns (acc:DebugAccumulator.DebugAccumulator)
    //   requires false
    // {
/*
    //   acc := DebugAccumulator.EmptyAccumulator();
    //   var a := new DebugAccumulator.AccRec(t.Count, "Entry");
    //   acc := DebugAccumulator.AccPut(acc, "t", a);
    //   var r := garbageQueue.DebugAccumulate();
    //   a := new DebugAccumulator.AccRec.Index(r);
    //   acc := DebugAccumulator.AccPut(acc, "garbageQueue", a);
*/
    // }

    // protected predicate Inv()
    //   reads this, Repr
    //   ensures Inv() ==> this in Repr
    // {
    //   && box in Repr
    //   && Repr == {this} + box.Repr
    //   && box.Inv()
    //   && box.Has()
    //   && It.Inv(Read())
    // }

    // protected function I() : IndirectionTableModel.IndirectionTable
    //   reads this, Repr
    //   requires Inv()
    //   ensures IndirectionTableModel.Inv(I())
    // {
    //   It.I(Read())
    // }

    // constructor Box(box: BoxedLinear<IndirectionTable>)
    //   ensures this.box == box
    //   ensures Repr == {this} + box.Repr
    // {
    //   this.box := box;
    //   new;
    //   Repr := {this} + box.Repr;
    // }

    // constructor Empty()
    //   ensures Inv()
    //   ensures fresh(Repr)
    // {
    //   box := new BoxedLinear(IndirectionTableEmptyConstructor());
    //   new;
    //   Repr := {this} + box.Repr;
    // }

    // constructor RootOnly(loc: Location)
    //   ensures Inv()
    //   ensures fresh(Repr)
    //   ensures I() == IndirectionTableModel.ConstructorRootOnly(loc)
    // {
    //   box := new BoxedLinear(IndirectionTableRootOnlyConstructor(loc));
    //   new;
    //   Repr := {this} + box.Repr;
    // }

//  //   constructor(t: HashMap)
//  //   {
//  //     box := new LinearBox(IndirectionTable(t, lNone, 0, None));
//  //     Repr := {this} + box.Repr;
//  //   }

    // // TODO: need to remember to call this; otherwise, memory will leak
    // method Destructor()
    //   requires Inv()
    //   modifies Repr
    // {
    //   linear var x := box.Take();
    //   It.Destructor(x);
    // }

    // method Clone() returns (table: IndirectionTable)
    //   requires Inv()
    //   ensures table.Inv()
    //   ensures fresh(table.Repr)
    //   ensures table.I() == IndirectionTableModel.clone(old(I()))
    // {
    //   linear var clone := It.Clone(box.Borrow());
    //   var boxed := new BoxedLinear(clone);
    //   table := new IndirectionTable.Box(boxed);
    // }

    // function method GetEntry(ref: BT.G.Reference) : (e : Option<Entry>)
    //   requires Inv()
    //   reads Repr
    //   ensures e == IndirectionTableModel.GetEntry(I(), ref)
    // {
    //   It.GetEntry(box.Borrow(), ref)
    // }

    // function method HasEmptyLoc(ref: BT.G.Reference) : (b: bool)
    //   requires Inv()
    //   reads Repr
    //   ensures b == IndirectionTableModel.HasEmptyLoc(I(), ref)
    // {
    //   It.HasEmptyLoc(box.Borrow(), ref)
    // }

    // method RemoveLoc(ref: BT.G.Reference) returns (oldLoc: Option<Location>)
    //   requires Inv()
    //   requires IndirectionTableModel.TrackingGarbage(I())
    //   requires ref in I().graph
    //   modifies Repr
    //   ensures Inv()
    //   ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
    //   ensures (I(), oldLoc) == IndirectionTableModel.RemoveLoc(old(I()), ref)
    // {
    //   linear var x := box.Take();
    //   x, oldLoc := It.RemoveLoc(x, ref);
    //   box.Give(x);
    // }

    // method AddLocIfPresent(ref: BT.G.Reference, loc: Location) returns (added: bool)
    //   requires Inv()
    //   modifies Repr
    //   ensures Inv()
    //   ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
    //   ensures (I(), added) == IndirectionTableModel.AddLocIfPresent(old(I()), ref, loc)
    // {
    //   linear var x := box.Take();
    //   x, added := It.AddLocIfPresent(x, ref, loc);
    //   box.Give(x);
    // }

    // method RemoveRef(ref: BT.G.Reference) returns (oldLoc: Option<Location>)
    //   requires Inv()
    //   requires IndirectionTableModel.TrackingGarbage(I())
    //   requires IndirectionTableModel.deallocable(I(), ref)
    //   modifies Repr
    //   ensures Inv()
    //   ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
    //   ensures (I(), oldLoc) == IndirectionTableModel.RemoveRef(old(I()), ref)
    // {
    //   linear var x := box.Take();
    //   x, oldLoc := It.RemoveRef(x, ref);
    //   box.Give(x);
    // }

    // method UpdateAndRemoveLoc(ref: BT.G.Reference, succs: seq<BT.G.Reference>) returns (oldLoc: Option<Location>)
    //   requires Inv()
    //   requires IndirectionTableModel.TrackingGarbage(I())
    //   requires |succs| <= MaxNumChildren()
    //   requires |I().graph| < IndirectionTableModel.MaxSize()
    //   requires IndirectionTableModel.SuccsValid(succs, I().graph)
    //   modifies Repr
    //   ensures Inv()
    //   ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
    //   ensures (I(), oldLoc) == IndirectionTableModel.UpdateAndRemoveLoc(old(I()), ref, succs)
    // {
    //   linear var x := box.Take();
    //   x, oldLoc := It.UpdateAndRemoveLoc(x, ref, succs);
    //   box.Give(x);
    // }

    // static method ValToIndirectionTable(v: V) returns (s: IndirectionTable?)
    //   requires IndirectionTableModel.valToIndirectionTable.requires(v)
    //   ensures s != null ==> s.Inv()
    //   ensures s != null ==> fresh(s.Repr)
    //   ensures s == null ==> IndirectionTableModel.valToIndirectionTable(v).None?
    //   ensures s != null ==> IndirectionTableModel.valToIndirectionTable(v) == Some(s.I())
    // {
    //   linear var opt := It.ValToIndirectionTable(v);
    //   linear match opt {
    //     case lNone => {s := null;}
    //     case lSome(it) => {
    //       var box := new BoxedLinear(it);
    //       s := new IndirectionTable.Box(box);
    //     }
    //   }
    // }

    // method IndirectionTableToVal() returns (v: V, size: uint64)
    //   requires Inv()
    //   requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I()))
    //   ensures ValInGrammar(v, IndirectionTableModel.IndirectionTableGrammar())
    //   ensures ValidVal(v)
    //   ensures IndirectionTableModel.valToIndirectionTable(v).Some?
    //   ensures
    //         IndirectionTableModel.I(IndirectionTableModel.valToIndirectionTable(v).value)
    //      == IndirectionTableModel.I(I())
    //   ensures SizeOfV(v) <= It.MaxIndirectionTableByteSize()
    //   ensures SizeOfV(v) == size as int
    // {
    //   v, size := It.IndirectionTableToVal(box.Borrow());
    // }

    // method InitLocBitmap() returns (success: bool, bm: BitmapImpl.Bitmap)
    //   requires Inv()
    //   requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I()))
    //   ensures bm.Inv()
    //   ensures (success, bm.I()) == IndirectionTableModel.InitLocBitmap(old(I()))
    //   ensures fresh(bm.Repr)
    // {
    //   success, bm := It.InitLocBitmap(box.Borrow());
    // }
    // 
    // function method FindDeallocable() : (ref: Option<BT.G.Reference>)
    //   requires Inv()
    //   requires IndirectionTableModel.TrackingGarbage(I())
    //   reads Repr
    //   ensures ref == IndirectionTableModel.FindDeallocable(I())
    // {
    //   It.FindDeallocable(box.Borrow())
    // }

    // function method GetSize() : (size: uint64)
    //   requires Inv()
    //   reads Repr
    //   ensures size as int == |I().graph|
    // {
    //   It.GetSize(box.Borrow())
    // }

    // method FindRefWithNoLoc() returns (ref: Option<BT.G.Reference>)
    //   requires Inv()
    //   modifies Repr
    //   ensures Inv()
    //   ensures Repr == old(Repr)
    //   ensures (I(), ref) == IndirectionTableModel.FindRefWithNoLoc(old(I()))
    // {
    //   linear var x := box.Take();
    //   x, ref := It.FindRefWithNoLoc(x);
    //   box.Give(x);
    // }

    // function method GetRefUpperBound() : (r: uint64)
    //   requires Inv()
    //   reads Repr
    //   ensures r == IndirectionTableModel.getRefUpperBound(this.I())
    // {
    //   It.GetRefUpperBound(box.Borrow())
    // }
  }
}
