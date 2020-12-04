include "../lib/Base/DebugAccumulator.i.dfy"
include "../lib/Base/Maps.i.dfy"
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

  function MapGraph(t: map<uint64, Entry>) : map<BT.G.Reference, seq<BT.G.Reference>>
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

    function I(): SectorType.IndirectionTable
    {
      SectorType.IndirectionTable(this.locs, this.graph)
    }

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

      assert r.Inv() by { reveal_PredCounts(); }
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
    ensures cloned.Inv()
    ensures cloned.graph == this.graph
    ensures cloned.locs == this.locs
    ensures cloned.I() == this.I()
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

      assert PredCounts(self.t) == PredCounts(old_self.t) by { reveal_PredCounts(); }
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
      assert self.Inv() by { reveal_PredCounts(); }
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
    {
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
      UpdatePredCounts(inout self, ref, [], oldEntry.value.succs);
      // ==============

      TCountEqGraphSize(self.t);

      oldLoc := if oldEntry.Some? then oldEntry.value.loc else None;

      // == mutation ==
      inout self.findLoclessIterator := None;
      inout self.UpdateGhost();
      // ==============

      assert self.graph == MapRemove1(old_self.graph, ref); // observe
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
      if this.garbageQueue.lSome? {
        NoDupesSetCardinality(this.garbageQueue.value.I());
        SetInclusionImpliesSmallerCardinality(Set(this.garbageQueue.value.I()), this.t.contents.Keys);
        assert |this.t.contents.Keys| == |this.t.contents|;
      }
    }

    linear inout method UpdateAndRemoveLoc(ref: BT.G.Reference, succs: seq<BT.G.Reference>)
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
    ensures (oldLoc.None? ==> ref !in old_self.locs)
    ensures (oldLoc.Some? ==> ref in old_self.locs && old_self.locs[ref] == oldLoc.value)
    {
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
      && (s.Some? ==> Marshalling.valToIndirectionTableMaps(a) == Some(IMapAsIndirectionTable(s.value)))
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

    static lemma RevealComputeRefCountsSharedDomainInv(t: HashMap, copy: HashMap)
    requires ComputeRefCountsSharedInv(t, copy)
    ensures forall ref | ref in copy.contents :: ref in t.contents
    ensures forall ref | ref in t.contents :: ref in copy.contents
    {
      reveal_ComputeRefCountsSharedInv();
    }

    static predicate {:opaque} ComputeRefCountsSharedInv(t: HashMap, copy: HashMap)
    ensures ComputeRefCountsSharedInv(t, copy) ==> t.count as int <= MaxSize()
    {
      && (t.count as int <= MaxSize())
      && (forall ref | ref in copy.contents :: ref in t.contents)
      && (forall ref | ref in t.contents :: ref in copy.contents)
      && (forall ref | ref in copy.contents :: t.contents[ref].loc == copy.contents[ref].loc)
      && (forall ref | ref in copy.contents :: t.contents[ref].succs == copy.contents[ref].succs)
      && (forall ref | ref in copy.contents :: |copy.contents[ref].succs| <= MaxNumChildren())
    }

    static predicate {:opaque} ComputeRefCountsOuterLoopInv0(t: HashMap, copy: HashMap, it: LinearMutableMap.Iterator<Entry>)
    requires (forall ref | ref in copy.contents :: ref in t.contents)
    {
      && (forall ref | ref in t.contents :: t.contents[ref].predCount as int <= 0x1_0000_0000_0000) // ???
      && (forall ref | ref in copy.contents :: t.contents[ref].predCount as int == |PredecessorSetRestricted(Graph(copy), ref, it.s)| + IsRoot(ref))
    }

    static predicate ComputeRefCountsOuterLoopInv(t: HashMap, copy: HashMap, it: LinearMutableMap.Iterator<Entry>)
    {
      && LinearMutableMap.Inv(t)
      && LinearMutableMap.Inv(copy)
      && LinearMutableMap.WFIter(copy, it)
      && BT.G.Root() in t.contents
      && ComputeRefCountsSharedInv(t, copy)
      && (RevealComputeRefCountsSharedDomainInv(t, copy);
          ComputeRefCountsOuterLoopInv0(t, copy, it))
      && GraphClosedRestricted(Graph(copy), it.s)
      && t.count as int <= MaxSize()
      && (t.count == copy.count)
    }

    static predicate {:opaque} ComputeRefCountsInnerLoopInv0(t: HashMap, copy: HashMap, it: LinearMutableMap.Iterator<Entry>, succs: seq<BT.G.Reference>, i: uint64)
    requires it.next.Next?
    requires ComputeRefCountsSharedInv(t, copy)
    {
      && (forall ref | ref in t.contents :: t.contents[ref].predCount as int <= 0x1_0000_0000_0000 + i as int)
      && (RevealComputeRefCountsSharedDomainInv(t, copy);
          forall ref | ref in t.contents :: t.contents[ref].loc == copy.contents[ref].loc)
      && (forall ref | ref in t.contents :: t.contents[ref].predCount as int == |PredecessorSetRestrictedPartial(Graph(copy), ref, it.s, it.next.key, i as int)| + IsRoot(ref))
    }

    static predicate ComputeRefCountsInnerLoopInv(t: HashMap, copy: HashMap, it: LinearMutableMap.Iterator<Entry>, succs: seq<BT.G.Reference>, i: uint64)
    requires it.next.Next?
    {
      && LinearMutableMap.Inv(t)
      && LinearMutableMap.Inv(copy)
      && LinearMutableMap.WFIter(copy, it)
      && 0 <= i as int <= |succs|
      && |succs| <= MaxNumChildren()
      && (t.count == copy.count)
      && BT.G.Root() in t.contents
      && ComputeRefCountsSharedInv(t, copy)
      && (RevealComputeRefCountsSharedDomainInv(t, copy);
          ComputeRefCountsInnerLoopInv0(t, copy, it, succs, i))
    }

    static lemma ComputeRefCountsOuterLoopInvImpliesInnerLoopInv(
      t: HashMap, copy: HashMap, it: LinearMutableMap.Iterator<Entry>, succs: seq<BT.G.Reference>)
    requires it.next.Next?
    requires succs == it.next.value.succs
    requires ComputeRefCountsOuterLoopInv(t, copy, it)
    ensures ComputeRefCountsInnerLoopInv(t, copy, it, succs, 0)
    {
      reveal_ComputeRefCountsSharedInv();
      reveal_ComputeRefCountsInnerLoopInv0();
      reveal_ComputeRefCountsOuterLoopInv0();

      forall ref | ref in t.contents
      ensures  t.contents[ref].predCount as int == |PredecessorSetRestrictedPartial(Graph(copy), ref, it.s, it.next.key, 0)| + IsRoot(ref) {
        assert PredecessorSetRestricted(Graph(copy), ref, it.s) == PredecessorSetRestrictedPartial(Graph(copy), ref, it.s, it.next.key, 0);
      }
    }

    static lemma ComputeRefCountsInnerLoopInvImpliesOuterLoopInv(
      t: HashMap,
      copy: HashMap,
      it: LinearMutableMap.Iterator<Entry>,
      it':  LinearMutableMap.Iterator<Entry>,
      succs: seq<BT.G.Reference>,
      i: uint64)
    requires it.next.Next?
    requires succs == it.next.value.succs
    requires LinearMutableMap.WFIter(copy, it')
    requires it'.s == it.s + {it.next.key}
    requires it'.decreaser < it.decreaser
    requires it'.next.Done? ==> it'.s == copy.contents.Keys
    requires i as int == |succs|
    requires ComputeRefCountsInnerLoopInv(t, copy, it, succs, i)
    requires BT.G.Root() in t.contents
    ensures ComputeRefCountsOuterLoopInv(t, copy, it')
    {
      assume GraphClosedRestricted(Graph(copy), it'.s);
      RevealComputeRefCountsSharedDomainInv(t, copy);
      assume (forall ref | ref in t.contents :: t.contents[ref].predCount as int <= 0x1_0000_0000_0000); // ???
      forall ref | ref in copy.contents
      ensures t.contents[ref].predCount as int == |PredecessorSetRestricted(Graph(copy), ref, it'.s)| + IsRoot(ref) {
        reveal_ComputeRefCountsInnerLoopInv0();
        assert PredecessorSetRestricted(Graph(copy), ref, it.s + {it.next.key}) == PredecessorSetRestrictedPartial(Graph(copy), ref, it.s, it.next.key, i as int);
      }
      assert ComputeRefCountsOuterLoopInv0(t, copy, it') by {
        reveal_ComputeRefCountsOuterLoopInv0();
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

    static lemma LemmaPredecessorSetRestrictedPartialAdd1Other(graph: map<BT.G.Reference, seq<BT.G.Reference>>, dest: BT.G.Reference, domain: set<BT.G.Reference>, next: BT.G.Reference, j: int)
    requires next in graph
    requires 0 <= j < |graph[next]|
    requires dest != graph[next][j]
    ensures |PredecessorSetRestrictedPartial(graph, dest, domain, next, j + 1)|
         == |PredecessorSetRestrictedPartial(graph, dest, domain, next, j)|
    {
      assert PredecessorSetRestrictedPartial(graph, dest, domain, next, j + 1)
          == PredecessorSetRestrictedPartial(graph, dest, domain, next, j);
    }

    static method ComputeRefCountsInnerLoop(linear inout t: HashMap, shared copy: HashMap, it: LinearMutableMap.Iterator<Entry>)
    returns (success: bool, it': LinearMutableMap.Iterator<Entry>)
    requires it.next.Next?
    requires ComputeRefCountsOuterLoopInv(old_t, copy, it)
    ensures LinearMutableMap.Inv(t)
    ensures success ==> (
      && ComputeRefCountsOuterLoopInv(t, copy, it')
      && BT.G.Root() in t.contents
    )
    ensures success ==> it'.decreaser < it.decreaser
    ensures LinearMutableMap.WFIter(copy, it')
    ensures !success ==> !BC.GraphClosed(Graph(copy))
    {
      var succs := it.next.value.succs;
      var i: uint64 := 0;

      assert |succs| <= MaxNumChildren() by {
        reveal_ComputeRefCountsSharedInv();
      }
      ComputeRefCountsOuterLoopInvImpliesInnerLoopInv(t, copy, it, succs);

      success := true;
      while i < |succs| as uint64
      invariant i as int <= |succs|
      invariant LinearMutableMap.Inv(copy)
      invariant LinearMutableMap.WFIter(copy, it)
      invariant BT.G.Root() in t.contents
      invariant ComputeRefCountsInnerLoopInv(t, copy, it, succs, i)
      decreases |succs| - i as int
      {
        var ref := succs[i];
        var oldEntry := LinearMutableMap.Get(t, ref);
        if oldEntry.Some? {
          reveal_ComputeRefCountsInnerLoopInv0();
          var newEntry := oldEntry.value.(predCount := oldEntry.value.predCount + 1);
          LinearMutableMap.Insert(inout t, ref, newEntry);

          forall r | r in t.contents
          ensures t.contents[r].predCount as int == |PredecessorSetRestrictedPartial(Graph(copy), r, it.s, it.next.key, (i+1) as int)| + IsRoot(r)
          {
            if r == ref {
              LemmaPredecessorSetRestrictedPartialAdd1Self(Graph(copy), r, it.s, it.next.key, i as int);
            } else {
              LemmaPredecessorSetRestrictedPartialAdd1Other(Graph(copy), r, it.s, it.next.key, i as int);
            }
          }

          i := i + 1;

          assert ComputeRefCountsInnerLoopInv(t, copy, it, succs, i) by {
            reveal_ComputeRefCountsSharedInv();
            assert ComputeRefCountsSharedInv(t, copy);
            assert ComputeRefCountsInnerLoopInv0(t, copy, it, succs, i);
          }
        } else {
          assert ref in Graph(copy)[it.next.key];
          success := false;
          break;
        }
      }

      it' := LinearMutableMap.IterInc(copy, it);
      
      if (success) {
        ComputeRefCountsInnerLoopInvImpliesOuterLoopInv(t, copy, it, it', succs, i);
      } else {
        assume !BC.GraphClosed(Graph(copy));
      }
    }

    static method ComputeRefCounts(shared t: HashMap)
      returns (linear t' : lOption<HashMap>)
      requires t.Inv()
      requires forall ref | ref in t.contents :: t.contents[ref].predCount == 0
      requires forall ref | ref in t.contents :: |t.contents[ref].succs| <= MaxNumChildren()
      requires t.count as int <= MaxSize()
      requires BT.G.Root() in t.contents

      ensures BC.GraphClosed(Graph(t)) <==> t'.lSome?
      ensures t'.lSome? ==> Graph(t) == Graph(t'.value)
      ensures t'.lSome? ==> Locs(t) == Locs(t'.value)
      ensures t'.lSome? ==> ValidPredCounts(PredCounts(t'.value), Graph(t'.value))
      ensures t'.lSome? ==> BT.G.Root() in t'.value.contents
    {
      shared var copy := t;
      linear var t1 := LinearMutableMap.Clone(t);

      var oldEntryOpt := LinearMutableMap.Get(t1, BT.G.Root());
      var oldEntry := oldEntryOpt.value;
      LinearMutableMap.Insert(inout t1, BT.G.Root(), oldEntry.(predCount := 1));

      var it := LinearMutableMap.IterStart(copy);

      assert ComputeRefCountsOuterLoopInv(t1, copy, it) by {
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
      invariant ComputeRefCountsOuterLoopInv(t1, copy, it)
      decreases it.decreaser
      {
        assert (forall ref | ref in t1.contents :: t1.contents[ref].predCount as int <= 0x1_0000_0000_0000 as int) by {
          forall ref | ref in t1.contents
          ensures t1.contents[ref].predCount as int <= 0x1_0000_0000_0000;
          {
            lemma_count_eq_graph_size(copy);
            PredecessorSetRestrictedSizeBound(Graph(copy), ref, it.s);
            reveal_ComputeRefCountsOuterLoopInv0();
          }
        }

        success, it := ComputeRefCountsInnerLoop(inout t1, copy, it);
        if (!success) {
          break;
        }

        assert ComputeRefCountsOuterLoopInv(t1, copy, it);
      }

      if success {
        t' := lSome(t1);

        assume Graph(t) == Graph(t'.value);
        assume Locs(t) == Locs(t'.value);
        assume ValidPredCounts(PredCounts(t'.value), Graph(t'.value));
        assume BC.GraphClosed(Graph(t));
      } else {
        LinearMutableMap.Destructor(t1);
        t' := lNone;

        assume !BC.GraphClosed(Graph(t));
      }
    }

    static method MakeGarbageQueue(shared t: HashMap)
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

    static method ValToIndirectionTable(v: V)
    returns (linear s : lOption<IndirectionTable>)
    requires ValidVal(v)
    requires ValInGrammar(v, IndirectionTableGrammar())
    ensures s.lSome? ==> s.value.Inv()
    // ensures s.lNone? ==> IndirectionTableModel.valToIndirectionTable(v).None?
    // ensures s.lSome? ==> IndirectionTableModel.valToIndirectionTable(v) == Some(I(s.value))
    ensures s.lSome? ==> Marshalling.valToIndirectionTable(v) == Some(s.value.I())
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
                  assume t1.Inv();
                  assume |t1.contents| <= 0x1_0000_0000;

                  linear var q := MakeGarbageQueue(t1);
                  var refUpperBound := ComputeRefUpperBound(t1);
                  s := lSome(IndirectionTable(
                    t1, lSome(q), refUpperBound, None,
                    /* r.locs */ Locs(t1),
                    /* r.graph */ Graph(t1),
                    /* r.predCounts */ PredCounts(t1)));

                  assert s.lSome? ==> s.value.Inv();
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

    static function MaxIndirectionTableByteSize() : int {
      8 + MaxSize() * (8 + 8 + 8 + (8 + MaxNumChildren() * 8))
    }

    static lemma lemma_SeqSum_prefix_array(a: array<V>, i: int)
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

    static function IMapAsIndirectionTable(m: map<uint64, Entry>) : SectorType.IndirectionTable
    {
      SectorType.IndirectionTable(MapLocs(m), MapGraph(m))
    }

    // TODO remove static function IHashMapAsIndirectionTable(m: HashMap) : SectorType.IndirectionTable
    // TODO remove {
    // TODO remove   SectorType.IndirectionTable(Locs(m), Graph(m))
    // TODO remove }

    static function method IndirectionTableGrammar() : G
    ensures ValidGrammar(IndirectionTableGrammar())
    {
      // (Reference, address, len, successor-list) triples
      GArray(GTuple([GUint64, GUint64, GUint64, GUint64Array]))
    }

    function IModel(self: IndirectionTable) : SectorType.IndirectionTable
    {
      SectorType.IndirectionTable(self.locs, self.graph)
    }

    // NOTE(travis): I found that the above method which marshalls
    // directly from indirection table to bytes is much faster
    // than converting to a V and using the GenericMarshalling
    // framework. I did some work on proving it (above),
    // but it's kind of annoying. However, I think that it won't
    // be a big deal as long as most syncs are journaling syncs?
    // So I've moved back to this one which is slower but cleaner.
    shared method IndirectionTableToVal()  // HashMapToVal
    returns (v : V, size: uint64)
    requires this.Inv()
    requires BC.WFCompleteIndirectionTable(this.I())
    ensures ValInGrammar(v, IndirectionTableGrammar())
    ensures ValidVal(v)
    ensures Marshalling.valToIndirectionTable(v).Some?
    ensures Marshalling.valToIndirectionTable(v) == Some(this.I())
    ensures SizeOfV(v) <= MaxIndirectionTableByteSize()
    ensures SizeOfV(v) == size as int
    {
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

        assume ValIsMap(a[..i], Some(partial));
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

      assert Marshalling.valToIndirectionTable(v).Some?;
      assume Marshalling.valToIndirectionTable(v) == Some(this.I());
    }

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

    static method BitmapInitUpTo(bm: BitmapImpl.Bitmap, upTo: uint64)
    requires bm.Inv()
    requires upTo as int <= BitmapModel.Len(bm.I())
    modifies bm.Repr
    ensures bm.Inv()
    // ensures bm.I() == IndirectionTableModel.BitmapInitUpTo(old(bm.I()), upTo)
    ensures bm.Repr == old(bm.Repr)
    {
      var i := 0;
      while i < upTo
      invariant i <= upTo
      invariant bm.Inv()
      invariant bm.Repr == old(bm.Repr)
      invariant upTo as int <= BitmapModel.Len(bm.I())
      {
        bm.Set(i);
        i := i + 1;
      }
    }

    shared method InitLocBitmap()
    returns (success: bool, bm: BitmapImpl.Bitmap)
    requires this.Inv()
    requires BC.WFCompleteIndirectionTable(this.I())
    ensures bm.Inv()
    // ensures (success, bm.I()) == IndirectionTableModel.InitLocBitmap(old(I(this)))
    ensures BitmapModel.Len(bm.I()) == NumBlocks()
    ensures fresh(bm.Repr)
    {
      bm := new BitmapImpl.Bitmap(NumBlocksUint64());
      BitmapInitUpTo(bm, MinNodeBlockIndexUint64());
      var it := LinearMutableMap.IterStart(this.t);

      assume BitmapModel.Len(bm.I()) == NumBlocks();

      while it.next.Next?
      invariant this.t.Inv()
      invariant BC.WFCompleteIndirectionTable(this.I())
      invariant bm.Inv()
      invariant LinearMutableMap.WFIter(this.t, it)
      invariant BitmapModel.Len(bm.I()) == NumBlocks()
      // invariant IndirectionTableModel.InitLocBitmapIterate(I(this), it, bm.I())
      //        == IndirectionTableModel.InitLocBitmap(I(this))
      invariant fresh(bm.Repr)
      decreases it.decreaser
      {
        assert it.next.key in this.I().locs;

        var loc: uint64 := it.next.value.loc.value.addr;
        var locIndex: uint64 := loc / NodeBlockSizeUint64();
        if locIndex < NumBlocksUint64() {
          var isSet := bm.GetIsSet(locIndex);
          if !isSet {
            it := LinearMutableMap.IterInc(this.t, it);
            bm.Set(locIndex);
          } else {
            success := false;
            return;
          }
        } else {
          success := false;
          return;
        }
      }

      success := true;
    }
    // 
    // ///// Dealloc stuff

    predicate deallocable(ref: BT.G.Reference)
    {
      && ref in this.I().graph
      && ref != BT.G.Root()
      && (forall r | r in this.I().graph :: ref !in this.I().graph[r])
    }

    shared method FindDeallocable() returns (ref: Option<BT.G.Reference>)
    requires this.Inv()
    requires this.TrackingGarbage()
    ensures ref.Some? ==> ref.value in this.I().graph
    ensures ref.Some? ==> this.deallocable(ref.value)
    ensures ref.None? ==> forall r | r in this.I().graph :: !this.deallocable(r)
    {
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
  }

  class BoxedIndirectionTable {
    var box: BoxedLinear<IndirectionTable>;
    ghost var Repr: set<object>;

    function Read() : IndirectionTable
      requires box.Inv()
      reads this, box, box.Repr
    {
      box.Read()
    }

//     method DebugAccumulate() returns (acc:DebugAccumulator.DebugAccumulator)
//       requires false
//     {
// /*
//       acc := DebugAccumulator.EmptyAccumulator();
//       var a := new DebugAccumulator.AccRec(t.Count, "Entry");
//       acc := DebugAccumulator.AccPut(acc, "t", a);
//       var r := garbageQueue.DebugAccumulate();
//       a := new DebugAccumulator.AccRec.Index(r);
//       acc := DebugAccumulator.AccPut(acc, "garbageQueue", a);
// */
//     }

    protected predicate Inv()
      reads this, Repr
      ensures Inv() ==> this in Repr
    {
      && box in Repr
      && Repr == {this} + box.Repr
      && box.Inv()
      && box.Has()
      && Read().Inv()
    }

    protected function I() : SectorType.IndirectionTable
      reads this, Repr
      requires Inv()
    {
      this.Read().I()
    }

    protected predicate TrackingGarbage()
      reads this, Repr
      requires Inv()
    {
      this.Read().TrackingGarbage()
    }

    predicate DeallocableRef(ref: BT.G.Reference)
    reads this, Repr
    requires this.Inv()
    ensures DeallocableRef(ref) ==> this.Read().DeallocableRef(ref)
    {
      && ref in this.I().graph
      && ref != BT.G.Root()
      && (forall r | r in this.I().graph :: ref !in this.I().graph[r])
    }

    constructor Box(box: BoxedLinear<IndirectionTable>)
      ensures this.box == box
      ensures Repr == {this} + box.Repr
    {
      this.box := box;
      new;
      Repr := {this} + box.Repr;
    }

    // TODO constructor Empty()
    // TODO   ensures Inv()
    // TODO   ensures fresh(Repr)
    // TODO {
    // TODO   box := new BoxedLinear(IndirectionTableEmptyConstructor());
    // TODO   new;
    // TODO   Repr := {this} + box.Repr;
    // TODO }

    constructor (loc: Location)
      ensures Inv()
      ensures fresh(Repr)
      ensures Read().Inv()
      ensures Read().graph == map[BT.G.Root() := []]
      ensures Read().locs == map[BT.G.Root() := loc]
    {
      linear var allocd := IndirectionTable.Alloc(loc);
      box := new BoxedLinear(allocd);
      new;
      Repr := {this} + box.Repr;
    }

    // TODO: need to remember to call this; otherwise, memory will leak
    method Destructor()
      requires Inv()
      modifies Repr
    {
      linear var x := box.Take();
      x.Free();
    }

    method Clone() returns (table: BoxedIndirectionTable)
      requires Inv()
      ensures table.Inv()
      ensures fresh(table.Repr)
      ensures table.I() == this.I()
    {
      linear var clone := box.Borrow().Clone();
      assert clone.I() == this.I();
      var boxed := new BoxedLinear(clone);
      table := new BoxedIndirectionTable.Box(boxed);
    }

    method GetEntry(ref: BT.G.Reference) returns (e : Option<Entry>)
      requires Inv()
      ensures e.None? ==> ref !in this.Read().graph
      ensures e.Some? ==> ref in this.Read().graph
      ensures e.Some? ==> this.Read().graph[ref] == e.value.succs
      ensures e.Some? && e.value.loc.Some? ==>
          ref in this.Read().locs && this.Read().locs[ref] == e.value.loc.value
      ensures ref in this.Read().locs ==> e.Some? && e.value.loc.Some?
    {
      e := box.Borrow().GetEntry(ref);
    }

    method HasEmptyLoc(ref: BT.G.Reference) returns (b: bool)
      requires Inv()
      ensures b == (ref in this.I().graph && ref !in this.I().locs)
    {
      b := box.Borrow().HasEmptyLoc(ref);
    }

    method RemoveLoc(ref: BT.G.Reference) returns (oldLoc: Option<Location>)
      requires Inv()
      requires TrackingGarbage()
      requires ref in I().graph
      modifies Repr
      ensures Inv()
      ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
      ensures TrackingGarbage()
      ensures this.I().locs == MapRemove1(old(this.I()).locs, ref)
      ensures this.I().graph == old(this.I()).graph
      ensures oldLoc.None? ==> ref !in old(this.I()).locs
      ensures oldLoc.Some? ==> ref in old(this.I()).locs && old(this.I()).locs[ref] == oldLoc.value
    {
      linear var x := box.Take();
      oldLoc := inout x.RemoveLoc(ref);
      box.Give(x);
    }

    method AddLocIfPresent(ref: BT.G.Reference, loc: Location) returns (added: bool)
      requires Inv()
      modifies Repr
      ensures Inv()
      ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
      ensures added == (ref in old(this.I()).graph && ref !in old(this.I()).locs)
      ensures this.I().graph == old(this.I()).graph
      ensures added ==> this.I().locs == old(this.I()).locs[ref := loc]
      ensures !added ==> this.I().locs == old(this.I()).locs
      ensures old(this.TrackingGarbage()) ==> this.TrackingGarbage()
    {
      linear var x := box.Take();
      added := inout x.AddLocIfPresent(ref, loc);
      box.Give(x);
    }

    method RemoveRef(ref: BT.G.Reference) returns (oldLoc: Option<Location>)
      requires Inv()
      requires this.TrackingGarbage()
      requires this.DeallocableRef(ref)
      modifies Repr
      ensures Inv()
      ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
      ensures this.TrackingGarbage()
      ensures this.I().graph == MapRemove1(old(this.I()).graph, ref)
      ensures this.I().locs == MapRemove1(old(this.I()).locs, ref)
      ensures (ref in old(this.I()).locs ==> oldLoc == Some(old(this.I()).locs[ref]))
      ensures (ref !in old(this.I()).locs ==> oldLoc == None)
    {
      linear var x := box.Take();
      oldLoc := inout x.RemoveRef(ref);
      box.Give(x);
    }

    method UpdateAndRemoveLoc(ref: BT.G.Reference, succs: seq<BT.G.Reference>) returns (oldLoc: Option<Location>)
      requires Inv()
      requires this.TrackingGarbage()
      requires |succs| <= MaxNumChildren()
      requires |I().graph| < MaxSize()
      requires IndirectionTable.SuccsValid(succs, I().graph)
      modifies Repr
      ensures Inv()
      ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
      ensures this.TrackingGarbage()
      ensures this.I().locs == MapRemove1(old(this.I()).locs, ref)
      ensures this.I().graph == old(this.I()).graph[ref := succs]
      ensures (oldLoc.None? ==> ref !in old(this.I()).locs)
      ensures (oldLoc.Some? ==> ref in old(this.I()).locs && old(this.I()).locs[ref] == oldLoc.value)
    {
      linear var x := box.Take();
      oldLoc := inout x.UpdateAndRemoveLoc(ref, succs);
      box.Give(x);
    }

    static method ValToIndirectionTable(v: V) returns (s: BoxedIndirectionTable?)
      requires ValidVal(v)
      requires ValInGrammar(v, IndirectionTable.IndirectionTableGrammar())
      ensures s != null ==> s.Inv()
      ensures s != null ==> fresh(s.Repr)
      ensures s != null ==> Marshalling.valToIndirectionTable(v) == Some(s.I())
      ensures s == null ==> Marshalling.valToIndirectionTable(v).None?
      // TODO maybe these are needed at call sites?  ensures s.Some? ==> TrackingGarbage(s.value)
      // TODO maybe these are needed at call sites?  ensures s.Some? ==> BC.WFCompleteIndirectionTable(I(s.value))
    {
      linear var opt := IndirectionTable.ValToIndirectionTable(v);
      linear match opt {
        case lNone => {s := null;}
        case lSome(it) => {
          var box := new BoxedLinear(it);
          s := new BoxedIndirectionTable.Box(box);
        }
      }
    }

    method IndirectionTableToVal() returns (v: V, size: uint64)
      requires Inv()
      requires BC.WFCompleteIndirectionTable(this.I())
      ensures ValInGrammar(v, IndirectionTable.IndirectionTableGrammar())
      ensures ValidVal(v)
      ensures Marshalling.valToIndirectionTable(v).Some?
      ensures Marshalling.valToIndirectionTable(v) == Some(this.I())

      ensures SizeOfV(v) <= IndirectionTable.MaxIndirectionTableByteSize()
      ensures SizeOfV(v) == size as int
    {
      v, size := box.Borrow().IndirectionTableToVal();
    }

    method InitLocBitmap() returns (success: bool, bm: BitmapImpl.Bitmap)
      requires Inv()
      requires BC.WFCompleteIndirectionTable(this.I())
      ensures bm.Inv()
      // ensures (success, bm.I()) == IndirectionTableModel.InitLocBitmap(old(I()))
      ensures fresh(bm.Repr)
    {
      success, bm := box.Borrow().InitLocBitmap();
    }
    
    method FindDeallocable() returns (ref: Option<BT.G.Reference>)
      requires this.Inv()
      requires this.Read().TrackingGarbage()
      ensures ref.Some? ==> ref.value in this.Read().I().graph
      ensures ref.Some? ==> this.Read().deallocable(ref.value)
      ensures ref.None? ==> forall r | r in this.I().graph :: !this.Read().deallocable(r)
    {
      ref := box.Borrow().FindDeallocable();
    }

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
