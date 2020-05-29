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
include "IndirectionTableModel.i.dfy"
//
// The heap-y implementation of IndirectionTableModel.
//

module IndirectionTableImpl {
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
  import IndirectionTableModel
  import opened NativePackedInts
  import USeq
  import Marshalling

  type HashMap = LinearMutableMap.LinearHashMap<IndirectionTableModel.Entry>
  type GarbageQueue = USeq.USeq

  // Dummy constructor only used when ImplVariables is in a state with no indirection
  // table. We could use a null indirection table instead, it's just slightly more
  // annoying to do that because we'd need additional invariants.
  function method IndirectionTableEmptyConstructor() : linear indirectionTable
  ensures It.Inv(IndirectionTableEmptyConstructor())
  {
    linear var t0 := LinearMutableMap.Constructor<IndirectionTableModel.Entry>(128);
    // This is not important, but needed to satisfy the Inv:
    linear var t1 := LinearMutableMap.Insert(t0, BT.G.Root(), IndirectionTableModel.Entry(None, [], 1));

    indirectionTable(
      t1,
      lNone,
      /* refUpperBound = */ 0,
      None)
  }

  function method IndirectionTableRootOnlyConstructor(loc: Location) : linear indirectionTable
  ensures It.Inv(IndirectionTableRootOnlyConstructor(loc))
  ensures It.I(IndirectionTableRootOnlyConstructor(loc)) == IndirectionTableModel.ConstructorRootOnly(loc)
  {
    linear var t0 := LinearMutableMap.Constructor<IndirectionTableModel.Entry>(128);
    linear var t1 := LinearMutableMap.Insert(t0, BT.G.Root(), IndirectionTableModel.Entry(Some(loc), [], 1));

    IndirectionTableModel.reveal_ConstructorRootOnly();

    linear var r := indirectionTable(
      t1,
      lNone,
      /* refUpperBound = */ BT.G.Root(),
      None);

    assert It.I(r) == IndirectionTableModel.ConstructorRootOnly(loc); // observe (surprisingly)

    r
  }



  // TODO move bitmap in here?
  linear datatype indirectionTable = indirectionTable(
    linear t: HashMap,
    linear garbageQueue: lOption<GarbageQueue>,
    refUpperBound: uint64,
    findLoclessIterator: Option<LinearMutableMap.SimpleIterator>)
  class It
  {

    // method DebugAccumulate()
    // returns (acc:DebugAccumulator.DebugAccumulator)
    // requires false
    // {
    //   acc := DebugAccumulator.EmptyAccumulator();
    //   var a := new DebugAccumulator.AccRec(t.Count, "IndirectionTableModel.Entry");
    //   acc := DebugAccumulator.AccPut(acc, "t", a);
    //   var r := garbageQueue.DebugAccumulate();
    //   a := new DebugAccumulator.AccRec.Index(r);
    //   acc := DebugAccumulator.AccPut(acc, "garbageQueue", a);
    // }

    static protected predicate Inv(me: indirectionTable)
    {
      && LinearMutableMap.Inv(me.t)
      && (me.garbageQueue.lSome? ==> USeq.Inv(me.garbageQueue.value))

      && var predCounts := IndirectionTableModel.PredCounts(me.t);
      && var graph := IndirectionTableModel.Graph(me.t);
      && var locs := IndirectionTableModel.Locs(me.t);
      && IndirectionTableModel.ValidPredCounts(predCounts, graph)
      && BC.GraphClosed(graph)
      && (forall ref | ref in graph :: |graph[ref]| <= MaxNumChildren())
      && (me.garbageQueue.lSome? ==> (
        && (forall ref | ref in me.t.contents && me.t.contents[ref].predCount == 0 :: ref in USeq.I(me.garbageQueue.value))
        && (forall ref | ref in USeq.I(me.garbageQueue.value) :: ref in me.t.contents && me.t.contents[ref].predCount == 0)
      ))
      && BT.G.Root() in me.t.contents
      && me.t.count as int <= IndirectionTableModel.MaxSize()
      && (forall ref | ref in graph :: ref <= me.refUpperBound)
      && (me.findLoclessIterator.Some? ==>
        && LinearMutableMap.WFSimpleIter(me.t, me.findLoclessIterator.value)
        && (forall r | r in me.findLoclessIterator.value.s ::
            r in locs)
      )
    }

    static protected function I(me: indirectionTable) : (res:IndirectionTableModel.IndirectionTable)
    requires Inv(me)
    ensures IndirectionTableModel.Inv(res)
    {
      var res := IndirectionTableModel.FromHashMap(me.t, MapOption(me.garbageQueue.Option(), x => USeq.I(x)), me.refUpperBound, me.findLoclessIterator);
      IndirectionTableModel.reveal_Inv(res);
      res
    }

    // constructor RootOnly(loc: Location)
    // ensures Inv(me)
    // ensures fresh(Repr)
    // ensures I(me) == IndirectionTableModel.ConstructorRootOnly(loc)
    // {
    //   me.t := new LinearMutableMap.LinearHashMap(128);
    //   me.findLoclessIterator := None;
    //   new;
    //   me.t.Insert(BT.G.Root(), IndirectionTableModel.Entry(Some(loc), [], 1));
    //   me.garbageQueue := null;
    //   me.refUpperBound := BT.G.Root();
    //   Repr := {this} + me.t.Repr;
    //   IndirectionTableModel.reveal_ConstructorRootOnly();
    // }

    // constructor(t: HashMap)
    // ensures me.t == t
    // ensures me.garbageQueue == null
    // {
    //   me.t := t;
    //   me.garbageQueue := null;
    // }

    static method Destructor(linear me: indirectionTable)
    {
      linear var indirectionTable(t, garbageQueue, refUpperBound, findLoclessIterator) := me;
      LinearMutableMap.Destructor(t);
      linear match garbageQueue {
        case lNone => {}
        case lSome(gq) => {USeq.Free(gq);}
      }
    }

    static method Clone(shared me: indirectionTable)
    returns (linear table : indirectionTable)
    requires Inv(me)
    ensures Inv(table)
    ensures I(table) == IndirectionTableModel.clone(I(me))
    {
      IndirectionTableModel.reveal_clone();
      shared var indirectionTable(t, garbageQueue, refUpperBound, findLoclessIterator) := me;
      linear var t' := LinearMutableMap.Clone(t);
      table := indirectionTable(t', lNone, refUpperBound, None);
    }

    static function method GetEntry(shared me: indirectionTable, ref: BT.G.Reference) : (e : Option<IndirectionTableModel.Entry>)
    requires Inv(me)
    ensures e == IndirectionTableModel.GetEntry(I(me), ref)
    {
      IndirectionTableModel.reveal_GetEntry();
      LinearMutableMap.Get(me.t, ref)
    }

    static function method HasEmptyLoc(shared me: indirectionTable, ref: BT.G.Reference) : (b: bool)
    requires Inv(me)
    ensures b == IndirectionTableModel.HasEmptyLoc(I(me), ref)
    {
      var entry := LinearMutableMap.Get(me.t, ref);
      entry.Some? && entry.value.loc.None?
    }

    static method RemoveLoc(linear me: indirectionTable, ref: BT.G.Reference)
    returns (linear self: indirectionTable, oldLoc: Option<Location>)
    requires Inv(me)
    requires IndirectionTableModel.TrackingGarbage(I(me))
    requires ref in I(me).graph
    ensures Inv(self)
    ensures (I(self), oldLoc) == IndirectionTableModel.RemoveLoc(I(me), ref)
    {
      IndirectionTableModel.reveal_RemoveLoc();

      linear var indirectionTable(t, garbageQueue, refUpperBound, findLoclessIterator) := me;
      var it := LinearMutableMap.FindSimpleIter(t, ref);
      var oldEntry := LinearMutableMap.SimpleIterOutput(t, it);
      var predCount := oldEntry.value.predCount;
      var succs := oldEntry.value.succs;
      t := LinearMutableMap.UpdateByIter(t, it, IndirectionTableModel.Entry(None, succs, predCount));
      findLoclessIterator := None;

      oldLoc := oldEntry.value.loc;

      ghost var _ := IndirectionTableModel.RemoveLoc(old(I(me)), ref);
      self := indirectionTable(t, garbageQueue, refUpperBound, findLoclessIterator);
      assert (I(self), oldLoc) == IndirectionTableModel.RemoveLoc(I(me), ref);
    }

    static method AddLocIfPresent(linear me: indirectionTable, ref: BT.G.Reference, loc: Location)
    returns (linear self: indirectionTable, added: bool)
    requires Inv(me)
    ensures Inv(self)
    ensures (I(self), added) == IndirectionTableModel.AddLocIfPresent(I(me), ref, loc)
    {
      IndirectionTableModel.reveal_AddLocIfPresent();

      linear var indirectionTable(t, garbageQueue, refUpperBound, findLoclessIterator) := me;
      var it := LinearMutableMap.FindSimpleIter(t, ref);
      var oldEntry := LinearMutableMap.SimpleIterOutput(t, it);
      added := oldEntry.Next? && oldEntry.value.loc.None?;

      if added {
        ghost var ghosty := true;
        if ghosty {
          if I(me).findLoclessIterator.Some? {
            LinearMutableMap.UpdatePreservesSimpleIter(I(me).t, it, IndirectionTableModel.Entry(Some(loc), oldEntry.value.succs, oldEntry.value.predCount), I(me).findLoclessIterator.value);
          }
        }

        t := LinearMutableMap.UpdateByIter(t, it, IndirectionTableModel.Entry(Some(loc), oldEntry.value.succs, oldEntry.value.predCount));
      }

      ghost var _ := IndirectionTableModel.AddLocIfPresent(I(me), ref, loc);
      self := indirectionTable(t, garbageQueue, refUpperBound, findLoclessIterator);
      assert (I(self), added) == IndirectionTableModel.AddLocIfPresent(I(me), ref, loc);
    }

    static method RemoveRef(linear me: indirectionTable, ref: BT.G.Reference)
    returns (linear self: indirectionTable, oldLoc : Option<Location>)
    requires Inv(me)
    requires IndirectionTableModel.TrackingGarbage(I(me))
    requires IndirectionTableModel.deallocable(I(me), ref)
    ensures Inv(self)
    ensures (I(self), oldLoc) == IndirectionTableModel.RemoveRef(I(me), ref)
    {
      IndirectionTableModel.reveal_RemoveRef();

      IndirectionTableModel.lemma_count_eq_graph_size(I(me).t);
      IndirectionTableModel.LemmaRemoveRefStuff(I(me), ref);

      linear var indirectionTable(t, lSome(garbageQueue), refUpperBound, findLoclessIterator) := me;
      linear var RemoveResult(t', oldEntry) := LinearMutableMap.RemoveAndGet(t, ref);
      t := t';

      IndirectionTableModel.lemma_count_eq_graph_size(t);

      garbageQueue := USeq.Remove(garbageQueue, ref);
      t, garbageQueue := UpdatePredCounts(t, garbageQueue, ref, [], oldEntry.value.succs);

      IndirectionTableModel.lemma_count_eq_graph_size(t);

      oldLoc := if oldEntry.Some? then oldEntry.value.loc else None;
      findLoclessIterator := None;

      ghost var _ := IndirectionTableModel.RemoveRef(I(me), ref);
      self := indirectionTable(t, lSome(garbageQueue), refUpperBound, findLoclessIterator);
    }

    static method PredInc(linear t: HashMap, linear q: USeq.USeq, ref: BT.G.Reference)
    returns(linear t': HashMap, linear q': USeq.USeq)
    requires t.Inv()
    requires USeq.Inv(q)
    requires t.count as nat < 0x1_0000_0000_0000_0000 / 8
    requires ref in t.contents
    requires t.contents[ref].predCount < 0xffff_ffff_ffff_ffff
    ensures t'.Inv()
    ensures USeq.Inv(q')
    ensures (t', USeq.I(q')) == IndirectionTableModel.PredInc(t, USeq.I(q), ref)
    {
      var oldEntryOpt := LinearMutableMap.Get(t, ref);
      var oldEntry := oldEntryOpt.value;
      var newEntry := oldEntry.(predCount := oldEntry.predCount + 1);
      t' := LinearMutableMap.Insert(t, ref, newEntry);
      q' := q;
      if oldEntry.predCount == 0 {
        q' := USeq.Remove(q', ref);
      }
    }

    static method PredDec(linear t: HashMap, linear q: USeq.USeq, ref: BT.G.Reference)
    returns(linear t': HashMap, linear q': USeq.USeq)
    requires t.Inv()
    requires USeq.Inv(q)
    requires t.count as nat < 0x1_0000_0000_0000_0000 / 8
    requires ref in t.contents
    requires t.contents[ref].predCount > 0
    requires |USeq.I(q)| <= 0x1_0000_0000;
    ensures t'.Inv()
    ensures USeq.Inv(q')
    ensures (t', USeq.I(q')) == IndirectionTableModel.PredDec(t, USeq.I(q), ref)
    {
      var oldEntryOpt := LinearMutableMap.Get(t, ref);
      var oldEntry := oldEntryOpt.value;
      var newEntry := oldEntry.(predCount := oldEntry.predCount - 1);
      t' := LinearMutableMap.Insert(t, ref, newEntry);
      q' := q;
      if oldEntry.predCount == 1 {
        q' := USeq.Add(q', ref);
      }
    }

    static method UpdatePredCounts(linear t: HashMap, linear q: USeq.USeq, ghost changingRef: BT.G.Reference,
        newSuccs: seq<BT.G.Reference>, oldSuccs: seq<BT.G.Reference>)
    returns(linear t': HashMap, linear q': USeq.USeq)
    requires t.Inv()
    requires USeq.Inv(q)
    requires IndirectionTableModel.RefcountUpdateInv(t, USeq.I(q), changingRef, newSuccs, oldSuccs, 0, 0)
    ensures t'.Inv()
    ensures USeq.Inv(q')
    ensures (t', USeq.I(q')) == IndirectionTableModel.UpdatePredCountsInc(t, USeq.I(q), changingRef, newSuccs, oldSuccs, 0)
    {
      var idx: uint64 := 0;
      t' := t;
      q' := q;

      while idx < |newSuccs| as uint64
      invariant t'.Inv()
      invariant USeq.Inv(q')
      invariant IndirectionTableModel.RefcountUpdateInv(t', USeq.I(q'), changingRef, newSuccs, oldSuccs, idx as int, 0)
      invariant IndirectionTableModel.UpdatePredCountsInc(t, USeq.I(q), changingRef, newSuccs, oldSuccs, 0)
             == IndirectionTableModel.UpdatePredCountsInc(t', USeq.I(q'), changingRef, newSuccs, oldSuccs, idx)
      decreases |newSuccs| - idx as int
      {
        IndirectionTableModel.LemmaUpdatePredCountsIncStuff(t', USeq.I(q'), changingRef, newSuccs, oldSuccs, idx as int);

        t', q' := PredInc(t', q', newSuccs[idx]);
        idx := idx + 1;
      }

      var idx2: uint64 := 0;

      while idx2 < |oldSuccs| as uint64
      invariant t'.Inv()
      invariant USeq.Inv(q')
      invariant IndirectionTableModel.RefcountUpdateInv(t', USeq.I(q'), changingRef, newSuccs, oldSuccs, |newSuccs|, idx2 as int)
      invariant IndirectionTableModel.UpdatePredCountsInc(t, USeq.I(q), changingRef, newSuccs, oldSuccs, 0)
             == IndirectionTableModel.UpdatePredCountsDec(t', USeq.I(q'), changingRef, newSuccs, oldSuccs, idx2)
      decreases |oldSuccs| - idx2 as int
      {
        IndirectionTableModel.LemmaUpdatePredCountsDecStuff(t', USeq.I(q'), changingRef, newSuccs, oldSuccs, idx2 as int);

        t', q' := PredDec(t', q', oldSuccs[idx2]);
        idx2 := idx2 + 1;
      }
    }

    static method UpdateAndRemoveLoc(linear me: indirectionTable, ref: BT.G.Reference, succs: seq<BT.G.Reference>)
    returns (linear self: indirectionTable, oldLoc : Option<Location>)
    requires Inv(me)
    requires IndirectionTableModel.TrackingGarbage(I(me))
    requires |succs| <= MaxNumChildren()
    requires |I(me).graph| < IndirectionTableModel.MaxSize()
    requires IndirectionTableModel.SuccsValid(succs, I(me).graph)
    ensures Inv(self)
    ensures (I(self), oldLoc)  == IndirectionTableModel.UpdateAndRemoveLoc(I(me), ref, succs)
    {
      IndirectionTableModel.reveal_UpdateAndRemoveLoc();

      IndirectionTableModel.lemma_count_eq_graph_size(I(me).t);
      IndirectionTableModel.LemmaUpdateAndRemoveLocStuff(I(me), ref, succs);

      linear var indirectionTable(t, lSome(garbageQueue), refUpperBound, findLoclessIterator) := me;
      var oldEntry := LinearMutableMap.Get(t, ref);
      var predCount := if oldEntry.Some? then oldEntry.value.predCount else 0;
      if oldEntry.None? {
        garbageQueue := USeq.Add(garbageQueue, ref);
      }
      t := LinearMutableMap.Insert(t, ref, IndirectionTableModel.Entry(None, succs, predCount));

      IndirectionTableModel.lemma_count_eq_graph_size(me.t);

      t, garbageQueue := UpdatePredCounts(t, garbageQueue, ref, succs,
          if oldEntry.Some? then oldEntry.value.succs else []);

      IndirectionTableModel.lemma_count_eq_graph_size(me.t);

      //IndirectionTableModel.LemmaValidPredCountsOfValidPredCountsIntermediate(IndirectionTableModel.PredCounts(me.t), IndirectionTableModel.Graph(me.t), succs, if oldEntry.Some? then oldEntry.value.succs else []);

      if ref > refUpperBound {
        refUpperBound := ref;
      }

      oldLoc := if oldEntry.Some? && oldEntry.value.loc.Some? then oldEntry.value.loc else None;
      findLoclessIterator := None;

      ghost var _ := IndirectionTableModel.UpdateAndRemoveLoc(I(me), ref, succs);
      self := indirectionTable(t, lSome(garbageQueue), refUpperBound, findLoclessIterator);
    }

    // Parsing and marshalling

    static lemma lemma_valToHashMapNonePrefix(a: seq<V>, i: int)
    requires IndirectionTableModel.valToHashMap.requires(a)
    requires 0 <= i <= |a|
    requires IndirectionTableModel.valToHashMap(a[..i]).None?
    ensures IndirectionTableModel.valToHashMap(a).None?
    decreases |a| - i
    {
      if (i == |a|) {
        assert a[..i] == a;
      } else {
        assert IndirectionTableModel.valToHashMap(a[..i+1]).None? by {
          assert DropLast(a[..i+1]) == a[..i];
          assert Last(a[..i+1]) == a[i];
        }
        lemma_valToHashMapNonePrefix(a, i+1);
      }
    }
  

    static method {:fuel ValInGrammar,3} ValToHashMap(a: seq<V>) returns (linear s : lOption<HashMap>)
    requires IndirectionTableModel.valToHashMap.requires(a)
    ensures s.lNone? ==> IndirectionTableModel.valToHashMap(a).None?
    ensures s.lSome? ==> s.value.Inv()
    ensures s.lSome? ==> Some(s.value) == IndirectionTableModel.valToHashMap(a)
    ensures s.lSome? ==> s.value.count as nat == |a|
    ensures s.lSome? ==> s.value.count as nat < 0x1_0000_0000_0000_0000 / 8
    {
      var i: uint64 := 0;
      var success := true;
      linear var mutMap := LinearMutableMap.Constructor<IndirectionTableModel.Entry>(1024); // TODO(alattuada) magic numbers

      while i < |a| as uint64
      invariant 0 <= i as int <= |a|
      invariant mutMap.Inv()
      invariant IndirectionTableModel.valToHashMap(a[..i]) == Some(mutMap)
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
          mutMap := LinearMutableMap.Insert(mutMap, ref, IndirectionTableModel.Entry(Some(loc), succs, 0));
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

    static method ComputeRefCounts(shared t: HashMap)
      returns (linear t' : lOption<HashMap>)
      requires t.Inv()
      requires forall ref | ref in t.contents :: t.contents[ref].predCount == 0
      requires forall ref | ref in t.contents :: |t.contents[ref].succs| <= MaxNumChildren()
      requires t.count as int <= IndirectionTableModel.MaxSize()
      requires BT.G.Root() in t.contents
      ensures match t' {
        case lNone => IndirectionTableModel.ComputeRefCounts(t) == None
        case lSome(t'') => t''.Inv() && IndirectionTableModel.ComputeRefCounts(t) == Some(t'')
      }
    {
      IndirectionTableModel.LemmaComputeRefCountsIterateInvInit(t);

      shared var copy := t;
      linear var t1 := LinearMutableMap.Clone(t);

      var oldEntryOpt := LinearMutableMap.Get(t1, BT.G.Root());
      var oldEntry := oldEntryOpt.value;
      t1 := LinearMutableMap.Insert(t1, BT.G.Root(), oldEntry.(predCount := 1));

      var it := LinearMutableMap.IterStart(copy);
      var success := true;
      while it.next.Next?
      invariant t1.Inv()
      invariant copy.Inv()
      invariant IndirectionTableModel.ComputeRefCountsIterateInv(t1, copy, it)
      invariant BT.G.Root() in t1.contents
      invariant IndirectionTableModel.ComputeRefCounts(old(t))
             == IndirectionTableModel.ComputeRefCountsIterate(t1, copy, it)
      decreases it.decreaser
      {
        IndirectionTableModel.LemmaComputeRefCountsIterateStuff(t1, copy, it);
        IndirectionTableModel.LemmaComputeRefCountsIterateValidPredCounts(t1, copy, it);

        ghost var t0 := t1;

        var succs := it.next.value.succs;
        var i: uint64 := 0;
        while i < |succs| as uint64
        invariant t1.Inv()
        invariant copy.Inv()
        invariant BT.G.Root() in t1.contents
        invariant 0 <= i as int <= |succs|
        invariant |succs| <= MaxNumChildren()
        invariant t1.count as int <= IndirectionTableModel.MaxSize()
        invariant forall ref | ref in t1.contents :: t1.contents[ref].predCount as int <= 0x1_0000_0000_0000 + i as int
        invariant IndirectionTableModel.ComputeRefCounts(old(t))
               == IndirectionTableModel.ComputeRefCountsIterate(t0, copy, it)
        invariant IndirectionTableModel.ComputeRefCountsEntryIterate(t0, succs, 0)
               == IndirectionTableModel.ComputeRefCountsEntryIterate(t1, succs, i)
        decreases |succs| - i as int
        {
          var ref := succs[i];
          var oldEntry := LinearMutableMap.Get(t1, ref);
          if oldEntry.Some? {
            var newEntry := oldEntry.value.(predCount := oldEntry.value.predCount + 1);
            t1 := LinearMutableMap.Insert(t1, ref, newEntry);
            i := i + 1;
          } else {
            success := false;
            break break;
          }
        }

        it := LinearMutableMap.IterInc(copy, it);
      }

      if success {
        t' := lSome(t1);
      } else {
        LinearMutableMap.Destructor(t1);
        t' := lNone;
      }
    }

    static method MakeGarbageQueue(shared t: HashMap)
    returns (linear q : USeq.USeq)
    requires t.Inv()
    requires |t.contents| <= 0x1_0000_0000
    ensures USeq.Inv(q)
    ensures USeq.I(q) == IndirectionTableModel.makeGarbageQueue(t)
    {
      IndirectionTableModel.reveal_makeGarbageQueue();

      q := USeq.Alloc();
      var it := LinearMutableMap.IterStart(t);
      while it.next.Next?
      invariant USeq.Inv(q)
      invariant LinearMutableMap.Inv(t)
      invariant LinearMutableMap.WFIter(t, it)
      invariant IndirectionTableModel.makeGarbageQueue(t)
             == IndirectionTableModel.makeGarbageQueueIterate(t, USeq.I(q), it)
      invariant Set(USeq.I(q)) <= t.contents.Keys
      invariant |t.contents| <= 0x1_0000_0000
      decreases it.decreaser
      {
        if it.next.value.predCount == 0 {
          NoDupesSetCardinality(USeq.I(q));
          SetInclusionImpliesSmallerCardinality(
              Set(USeq.I(q)), t.contents.Keys);
          assert |t.contents.Keys| == |t.contents|;

          q := USeq.Add(q, it.next.key);
        }
        it := LinearMutableMap.IterInc(t, it);
      }
    }

    static method ComputeRefUpperBound(shared t: HashMap)
    returns (r: uint64)
    requires t.Inv()
    ensures r == IndirectionTableModel.computeRefUpperBound(t)
    {
      var it := LinearMutableMap.IterStart(t);
      var refUpperBound := 0;
      while it.next.Next?
      invariant LinearMutableMap.Inv(t)
      invariant LinearMutableMap.WFIter(t, it)
      invariant forall ref | ref in it.s :: ref <= refUpperBound
      invariant IndirectionTableModel.computeRefUpperBoundIterate(t, it, refUpperBound)
             == IndirectionTableModel.computeRefUpperBound(t)
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
    returns (linear s : lOption<indirectionTable>)
    requires IndirectionTableModel.valToIndirectionTable.requires(v)
    ensures s.lSome? ==> Inv(s.value)
    ensures s.lNone? ==> IndirectionTableModel.valToIndirectionTable(v).None?
    ensures s.lSome? ==> IndirectionTableModel.valToIndirectionTable(v) == Some(I(s.value))
    {
      if |v.a| as uint64 <= IndirectionTableModel.MaxSizeUint64() {
        linear var res := ValToHashMap(v.a);
        linear match res {
          case lSome(t) => {
            var rootRef := LinearMutableMap.Get(t, BT.G.Root());
            if rootRef.Some? {
              linear var t1opt := ComputeRefCounts(t);
              LinearMutableMap.Destructor(t);
              linear match t1opt {
                case lSome(t1) => {
                  IndirectionTableModel.lemmaMakeGarbageQueueCorrect(t1);
                  IndirectionTableModel.lemma_count_eq_graph_size(t);
                  IndirectionTableModel.lemma_count_eq_graph_size(t1);

                  linear var q := MakeGarbageQueue(t1);
                  var refUpperBound := ComputeRefUpperBound(t1);
                  s := lSome(indirectionTable(t1, lSome(q), refUpperBound, None));
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
      8 + IndirectionTableModel.MaxSize() * (8 + 8 + 8 + (8 + MaxNumChildren() * 8))
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

    // method marshallIndirectionTableRow(
    //     data: array<byte>,
    //     start: uint64,
    //     next: MutableMapModel.IteratorOutput<IndirectionTableModel.Entry>)
    // returns (end: uint64)
    // modifies data
    // requires 0 <= start as int <= data.Length
    // requires data.Length < 0x1_0000_0000_0000_0000
    // requires next.Next?
    // requires next.value.loc.Some?
    // requires |next.value.succs| <= MaxNumChildren()
    // ensures end != 0 ==>
    //   && start as int <= end as int <= data.Length
    //   && parse_Val(data[start..end],
    //     Marshalling.IndirectionTableRowGrammar()).0
    //       == Some(VTuple([
    //           VUint64(next.key),
    //           VUint64(next.value.loc.value.addr),
    //           VUint64(next.value.loc.value.len),
    //           VUint64Array(next.value.succs)
    //          ]))
    // {
    //   if 8 + 8 + 8 + 8 + 8*|next.value.succs| as uint64
    //         > data.Length as uint64 - start
    //   {
    //     return 0;
    //   }

    //   var idx0 := start;
    //   ghost var data0 := data[..];

    //   Pack_LittleEndian_Uint64_into_Array(next.key, data, idx0);
    //   var idx1 := idx0 + 8;

    //   ghost var data1 := data[..];

    //   Pack_LittleEndian_Uint64_into_Array(next.value.loc.value.addr, data, idx1);
    //   var idx2 := idx1 + 8;

    //   ghost var data2 := data[..];

    //   Pack_LittleEndian_Uint64_into_Array(next.value.loc.value.len, data, idx2);
    //   var idx3 := idx2 + 8;

    //   ghost var data3 := data[..];

    //   Pack_LittleEndian_Uint64_into_Array(
    //       |next.value.succs| as uint64, data, idx3);
    //   var idx4 := idx3 + 8;

    //   ghost var data4 := data[..];

    //   Pack_LittleEndian_Uint64_Seq_into_Array(
    //       next.value.succs, data, idx4);
    //   var idx5 := idx4 + 8 * |next.value.succs| as uint64;

    //   ghost var data5 := data[..];

    //   end := idx5;

    //   calc {
    //     parse_Val(data5[idx3..idx5], GUint64Array).0;
    //     { reveal_parse_Val(); }
    //     parse_Uint64Array(data5[idx3..idx5]).0;
    //     {
    //       assert unpack_LittleEndian_Uint64(data5[idx3..idx5][..8])
    //          == |next.value.succs| as uint64 by {
    //         assert data5[idx3..idx5][..8]
    //             == data5[idx3..idx4]
    //             == data4[idx3..idx4];
    //       }
    //       var len := |next.value.succs| as uint64;
    //       assert unpack_LittleEndian_Uint64_Seq(data5[idx3..idx5][8..8 + 8*len], len as int)
    //         == next.value.succs by {
    //         assert data5[idx3..idx5][8..8+8*len] == data5[idx4..idx5];
    //       }
    //     }
    //     Some(VUint64Array(next.value.succs));
    //   }

    //   calc {
    //     parse_Val(data5[idx2..idx5], GUint64).0;
    //     { reveal_parse_Val(); }
    //     parse_Uint64(data5[idx2..idx5]).0;
    //     {
    //       calc {
    //         data5[idx2..idx5][..8];
    //         data4[idx2..idx3];
    //         data3[idx2..idx3];
    //       }
    //     }
    //     Some(VUint64(next.value.loc.value.len));
    //   }

    //   calc {
    //     parse_Val(data5[idx1..idx5], GUint64).0;
    //     { reveal_parse_Val(); }
    //     parse_Uint64(data5[idx1..idx5]).0;
    //     {
    //       calc {
    //         data5[idx1..idx5][..8];
    //         { lemma_seq_slice_slice(data5, idx1 as int, idx5 as int, 0, 8); }
    //         data5[idx1..idx2];
    //         data4[idx1..idx2];
    //         data3[idx1..idx2];
    //         data2[idx1..idx2];
    //       }
    //     }
    //     Some(VUint64(next.value.loc.value.addr));
    //   }

    //   calc {
    //     parse_Val(data5[idx0..idx5], GUint64).0;
    //     { reveal_parse_Val(); }
    //     parse_Uint64(data5[idx0..idx5]).0;
    //     {
    //       calc {
    //         data5[idx0..idx5][..8];
    //         {
    //           lemma_seq_slice_slice(data5, idx0 as int, idx5 as int, 0, 8);
    //         }
    //         data4[idx0..idx1];
    //         data3[idx0..idx1];
    //         data2[idx0..idx1];
    //         data1[idx0..idx1];
    //       }
    //     }
    //     Some(VUint64(next.key));
    //   }

    //   ghost var sl := data5[idx0..idx5];

    //   calc {
    //     [
    //       VUint64(next.key),
    //       VUint64(next.value.loc.value.addr),
    //       VUint64(next.value.loc.value.len),
    //       VUint64Array(next.value.succs)
    //     ];
    //     {
    //       assert sl == data5[idx0..idx5];
    //       assert sl[8..] == data5[idx1..idx5];
    //       assert sl[16..] == data5[idx2..idx5];
    //       assert sl[24..] == data5[idx3..idx5];
    //       var x := [parse_Val(sl, GUint64).0.value] + [parse_Val(sl[8..], GUint64).0.value] + [parse_Val(sl[16..], GUint64).0.value] + [parse_Val(sl[24..], GUint64Array).0.value] + [];
    //       assert VUint64(next.key) == parse_Val(sl, GUint64).0.value;
    //       assert VUint64(next.value.loc.value.addr) == parse_Val(sl[8..], GUint64).0.value;
    //       assert VUint64(next.value.loc.value.len) == parse_Val(sl[16..], GUint64).0.value;
    //       assert VUint64Array(next.value.succs) == parse_Val(sl[24..], GUint64Array).0.value;
    //     }
    //     [parse_Val(sl, GUint64).0.value, parse_Val(sl[8..], GUint64).0.value, parse_Val(sl[16..], GUint64).0.value, parse_Val(sl[24..], GUint64Array).0.value];
    //     [parse_Val(sl, GUint64).0.value] + [parse_Val(sl[8..], GUint64).0.value] + [parse_Val(sl[16..], GUint64).0.value] + [parse_Val(sl[24..], GUint64Array).0.value] + [];
    //     {
    //       reveal_parse_Tuple_contents();
    //       assert parse_Tuple_contents(sl[idx5-idx0..], []).0.value == [];
    //     }
    //     [parse_Val(sl, GUint64).0.value] + [parse_Val(sl[8..], GUint64).0.value] + [parse_Val(sl[16..], GUint64).0.value] + [parse_Val(sl[24..], GUint64Array).0.value] + parse_Tuple_contents(sl[idx5-idx0..], []).0.value;
    //     {
    //       reveal_parse_Tuple_contents();
    //       reveal_parse_Val();
    //       assert sl[24..][idx5-idx3..] == sl[idx5-idx0..];
    //     }
    //     [parse_Val(sl, GUint64).0.value] + [parse_Val(sl[8..], GUint64).0.value] + [parse_Val(sl[16..], GUint64).0.value] + parse_Tuple_contents(sl[24..], [GUint64Array]).0.value;
    //     {
    //       reveal_parse_Tuple_contents();
    //       reveal_parse_Val();
    //       assert sl[16..][8..] == sl[24..];
    //     }
    //     [parse_Val(sl, GUint64).0.value] + [parse_Val(sl[8..], GUint64).0.value] + parse_Tuple_contents(sl[16..], [GUint64, GUint64Array]).0.value;
    //     {
    //       reveal_parse_Tuple_contents();
    //       reveal_parse_Val();
    //       assert sl[8..][8..] == sl[16..];
    //     }
    //     [parse_Val(sl, GUint64).0.value] + parse_Tuple_contents(sl[8..], [GUint64, GUint64, GUint64Array]).0.value;
    //     {
    //       reveal_parse_Tuple_contents();
    //       reveal_parse_Val();
    //     }
    //     parse_Tuple_contents(sl, [GUint64, GUint64, GUint64, GUint64Array]).0.value;
    //   }

    //   calc {
    //     Some(VTuple([
    //       VUint64(next.key),
    //       VUint64(next.value.loc.value.addr),
    //       VUint64(next.value.loc.value.len),
    //       VUint64Array(next.value.succs)
    //     ]));
    //     { reveal_parse_Val(); }
    //     parse_Val(sl, Marshalling.IndirectionTableRowGrammar()).0;
    //   }
    // }

    // method marshallIndirectionTableContents(data: array<byte>, start: uint64)
    // returns (end: uint64)
    // requires Inv(me)
    // requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I(me)))

    // requires 0 <= start as int <= data.Length
    // requires data.Length < 0x1_0000_0000_0000_0000

    // modifies data

    // ensures end != 0 ==>
    //   && start as int <= end as int <= data.Length
    //   && Marshalling.valToIndirectionTableMaps(
    //        parse_Array_contents(
    //          data[start..end],
    //          Marshalling.IndirectionTableRowGrammar(),
    //          t.Count
    //        )
    //      ) == IndirectionTableModel.I(I(me))
    // {
    //   var idx := start;
    //   var it := t.IterStart();
    //   while it.next.Next?
    //   {
    //   }
    // }

    // method marshallIndirectionTable(data: array<byte>, start_idx: uint64)
    // returns (end: uint64)
    // requires Inv(me)
    // requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I(me)))
    // modifies data
    // {
    //   var idx := start_idx;

    //   Pack_LittleEndian_Uint64_into_Array(t.Count, data, idx);
    //   idx := idx + 8;

    //   var it := t.IterStart();
    //   while it.next.Next?
    //   {
    //     if idx + 8 + 8 + 8 + 8 + 8*|it.next.value.succs| as uint64
    //         > data.Length as uint64
    //     {
    //       return 0;
    //     }

    //     Pack_LittleEndian_Uint64_into_Array(it.next.key, data, idx);
    //     idx := idx + 8;

    //     Pack_LittleEndian_Uint64_into_Array(it.next.value.loc.value.addr, data, idx);
    //     idx := idx + 8;

    //     Pack_LittleEndian_Uint64_into_Array(it.next.value.loc.value.len, data, idx);
    //     idx := idx + 8;

    //     Pack_LittleEndian_Uint64_into_Array(
    //         |it.next.value.succs| as uint64, data, idx);
    //     idx := idx + 8;

    //     Pack_LittleEndian_Uint64_Seq_into_Array(
    //         it.next.value.succs, data, idx);
    //     idx := idx + 8 * |it.next.value.succs| as uint64;
    //     
    //     it := t.IterInc(it);
    //   }
    //   return idx;
    // }

    // NOTE(travis): I found that the above method which marshalls
    // directly from indirection table to bytes is much faster
    // than converting to a V and using the GenericMarshalling
    // framework. I did some work on proving it (above),
    // but it's kind of annoying. However, I think that it won't
    // be a big deal as long as most syncs are journaling syncs?
    // So I've moved back to this one which is slower but cleaner.
    static method indirectionTableToVal(shared me: indirectionTable)
    returns (v : V, size: uint64)
    requires Inv(me)
    requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I(me)))
    ensures ValInGrammar(v, IndirectionTableModel.IndirectionTableGrammar())
    ensures ValidVal(v)
    ensures IndirectionTableModel.valToIndirectionTable(v).Some?
    ensures
          IndirectionTableModel.I(IndirectionTableModel.valToIndirectionTable(v).value)
       == IndirectionTableModel.I(I(me))
    ensures SizeOfV(v) <= MaxIndirectionTableByteSize()
    ensures SizeOfV(v) == size as int
    {
      assert me.t.count <= IndirectionTableModel.MaxSizeUint64();
      lemma_SeqSum_empty();
      var count := me.t.count as uint64;
      var a: array<V> := new V[count];
      var it := LinearMutableMap.IterStart(me.t);
      var i: uint64 := 0;
      size := 0;

      ghost var partial := map[];
      while it.next.Next?
      invariant Inv(me)
      invariant BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I(me)))
      invariant 0 <= i as int <= a.Length
      invariant LinearMutableMap.WFIter(me.t, it);
      invariant forall j | 0 <= j < i :: ValidVal(a[j])
      invariant forall j | 0 <= j < i :: ValInGrammar(a[j], GTuple([GUint64, GUint64, GUint64, GUint64Array]))
      // NOALIAS/CONST table doesn't need to be mutable, if we could say so we wouldn't need this
      invariant IndirectionTableModel.valToHashMap(a[..i]).Some?
      invariant IndirectionTableModel.valToHashMap(a[..i]).value.contents == partial
      invariant |partial.Keys| == i as nat
      invariant partial.Keys == it.s
      invariant partial.Keys <= me.t.contents.Keys
      invariant forall r | r in partial :: r in me.t.contents
          && partial[r].loc == me.t.contents[r].loc
          && partial[r].succs == me.t.contents[r].succs
      // NOALIAS/CONST t doesn't need to be mutable, if we could say so we wouldn't need this
      invariant me.t.contents == old(me.t.contents)
      invariant size as int <=
          |it.s| * (8 + 8 + 8 + (8 + MaxNumChildren() * 8))
      invariant SeqSum(a[..i]) == size as int;
      decreases it.decreaser
      {
        var (ref, locOptGraph: IndirectionTableModel.Entry) := (it.next.key, it.next.value);
        assert ref in I(me).locs;
        // NOTE: deconstructing in two steps to work around c# translation bug
        var locOpt := locOptGraph.loc;
        var succs := locOptGraph.succs;
        var loc := locOpt.value;
        //ghost var predCount := locOptGraph.predCount;
        var childrenVal := VUint64Array(succs);

        assert |succs| <= MaxNumChildren();

        //assert I(me).locs[ref] == loc;
        //assert I(me).graph[ref] == succs;

        //assert IndirectionTableModel.I(I(me)).locs[ref] == loc;
        //assert IndirectionTableModel.I(I(me)).graph[ref] == succs;

        assert ValidNodeLocation(loc);
        /*ghost var t0 := IndirectionTableModel.valToHashMap(a[..i]);
        assert ref !in t0.value.contents;
        assert loc.addr != 0;
        assert LBAType.ValidLocation(loc);*/

        LinearMutableMap.LemmaIterIndexLtCount(me.t, it);

        assert |succs| < 0x1_0000_0000_0000_0000;
        assert ValidVal(VTuple([VUint64(ref), VUint64(loc.addr), VUint64(loc.len), childrenVal]));

        assert |LinearMutableMap.IterInc(me.t, it).s| == |it.s| + 1;

        var vi := VTuple([VUint64(ref), VUint64(loc.addr), VUint64(loc.len), childrenVal]);

        //assert SizeOfV(vi) <= (8 + 8 + 8 + (8 + MaxNumChildren() * 8));

        // == mutation ==
        partial := partial[ref := IndirectionTableModel.Entry(locOpt, succs, 0)];
        a[i] := vi;
        i := i + 1;
        it := LinearMutableMap.IterInc(me.t, it);
        // ==============

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
      }

      /* (doc) assert |partial.Keys| == |me.t.contents.Keys|; */
      SetInclusionAndEqualCardinalityImpliesSetEquality(partial.Keys, me.t.contents.Keys);

      assert a[..i] == a[..]; // observe
      v := VArray(a[..]);

      /*ghost var t0 := IndirectionTableModel.valToHashMap(v.value.a);
      assert t0.Some?;
      assert BT.G.Root() in t0.value.contents;
      assert t0.value.count <= MaxSizeUint64();
      ghost var t1 := IndirectionTableModel.ComputeRefCounts(t0.value);
      assert t1.Some?;*/

      assert |it.s| <= IndirectionTableModel.MaxSize();

      size := size + 8;
    }

    // To bitmap

    static method BitmapInitUpToIterate(bm: BitmapImpl.Bitmap, i: uint64, upTo: uint64)
    requires bm.Inv()
    requires 0 <= i as int <= upTo as int <= BitmapModel.Len(bm.I())
    modifies bm.Repr
    ensures bm.Inv()
    ensures bm.I() == IndirectionTableModel.BitmapInitUpToIterate(old(bm.I()), i, upTo)
    ensures bm.Repr == old(bm.Repr)
    decreases upTo - i
    {
      if i == upTo {
      } else {
        bm.Set(i);
        BitmapInitUpToIterate(bm, i+1, upTo);
      }
    }

    static method BitmapInitUpTo(bm: BitmapImpl.Bitmap, upTo: uint64)
    requires bm.Inv()
    requires upTo as int <= BitmapModel.Len(bm.I())
    modifies bm.Repr
    ensures bm.Inv()
    ensures bm.I() == IndirectionTableModel.BitmapInitUpTo(old(bm.I()), upTo)
    ensures bm.Repr == old(bm.Repr)
    {
      IndirectionTableModel.reveal_BitmapInitUpTo();
      BitmapInitUpToIterate(bm, 0, upTo);
    }

    static method InitLocBitmap(shared me: indirectionTable)
    returns (success: bool, bm: BitmapImpl.Bitmap)
    requires Inv(me)
    requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I(me)))
    ensures bm.Inv()
    ensures (success, bm.I()) == IndirectionTableModel.InitLocBitmap(old(I(me)))
    ensures fresh(bm.Repr)
    {
      IndirectionTableModel.reveal_InitLocBitmap();

      bm := new BitmapImpl.Bitmap(NumBlocksUint64());
      BitmapInitUpTo(bm, MinNodeBlockIndexUint64());
      var it := LinearMutableMap.IterStart(me.t);
      while it.next.Next?
      invariant me.t.Inv()
      invariant BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I(me)))
      invariant bm.Inv()
      invariant LinearMutableMap.WFIter(me.t, it)
      invariant BitmapModel.Len(bm.I()) == NumBlocks()
      invariant IndirectionTableModel.InitLocBitmapIterate(I(me), it, bm.I())
             == IndirectionTableModel.InitLocBitmap(I(me))
      invariant fresh(bm.Repr)
      decreases it.decreaser
      {
        assert it.next.key in IndirectionTableModel.I(I(me)).locs;

        var loc: uint64 := it.next.value.loc.value.addr;
        var locIndex: uint64 := loc / NodeBlockSizeUint64();
        if locIndex < NumBlocksUint64() {
          var isSet := bm.GetIsSet(locIndex);
          if !isSet {
            it := LinearMutableMap.IterInc(me.t, it);
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
    
    ///// Dealloc stuff

    static function method FindDeallocable(shared me: indirectionTable) : (ref: Option<BT.G.Reference>)
    requires Inv(me)
    requires IndirectionTableModel.TrackingGarbage(I(me))
    ensures ref == IndirectionTableModel.FindDeallocable(I(me))
    {
      IndirectionTableModel.reveal_FindDeallocable();
      USeq.FirstOpt(me.garbageQueue.value)
    }

    static function method GetSize(shared me: indirectionTable) : (size: uint64)
    requires Inv(me)
    ensures size as int == |I(me).graph|
    {
      IndirectionTableModel.lemma_count_eq_graph_size(I(me).t);
      me.t.count
    }

    static method FindRefWithNoLoc(linear me: indirectionTable) returns (linear self: indirectionTable, ref: Option<BT.G.Reference>)
    requires Inv(me)
    ensures Inv(self)
    ensures (I(self), ref) == IndirectionTableModel.FindRefWithNoLoc(I(me))
    {
      IndirectionTableModel.reveal_FindRefWithNoLoc();

      linear var indirectionTable(t, garbageQueue, refUpperBound, findLoclessIterator) := me;
      var it;
      if findLoclessIterator.Some? {
        it := findLoclessIterator.value;
      } else {
        it := LinearMutableMap.SimpleIterStart(t);
      }

      while true
      invariant Inv(me)
      invariant LinearMutableMap.WFSimpleIter(t, it)
      invariant forall r | r in it.s :: r in I(me).locs
      invariant IndirectionTableModel.FindRefWithNoLoc(I(me))
          == IndirectionTableModel.FindRefWithNoLocIterate(
              I(indirectionTable(t, garbageQueue, refUpperBound, findLoclessIterator)), it)
      decreases it.decreaser
      {
        var next := LinearMutableMap.SimpleIterOutput(t, it);
        if next.Next? {
          if next.value.loc.None? {
            findLoclessIterator := Some(it);
            ref := Some(next.key);
            break;
          } else {
            it := LinearMutableMap.SimpleIterInc(t, it);
          }
        } else {
          findLoclessIterator := Some(it);
          ref := None;
          break;
        }
      }
      self := indirectionTable(t, garbageQueue, refUpperBound, findLoclessIterator);
    }

    static function method GetRefUpperBound(shared me: indirectionTable) : (r: uint64)
    requires Inv(me)
    ensures r == IndirectionTableModel.getRefUpperBound(I(me))
    {
      IndirectionTableModel.reveal_getRefUpperBound();
      me.refUpperBound
    }
  }

  class IndirectionTable {
    var box: BoxedLinear<indirectionTable>;
    ghost var Repr: set<object>;

    function Read() : indirectionTable
      requires box.Inv()
      reads this, box, box.Repr
    {
      box.Read()
    }

    method DebugAccumulate() returns (acc:DebugAccumulator.DebugAccumulator)
      requires false
    {
/*
      acc := DebugAccumulator.EmptyAccumulator();
      var a := new DebugAccumulator.AccRec(t.Count, "IndirectionTableModel.Entry");
      acc := DebugAccumulator.AccPut(acc, "t", a);
      var r := garbageQueue.DebugAccumulate();
      a := new DebugAccumulator.AccRec.Index(r);
      acc := DebugAccumulator.AccPut(acc, "garbageQueue", a);
*/
    }

    protected predicate Inv()
      reads this, Repr
      ensures Inv() ==> this in Repr
    {
      && box in Repr
      && Repr == {this} + box.Repr
      && box.Inv()
      && box.Has()
      && It.Inv(Read())
    }

    protected function I() : IndirectionTableModel.IndirectionTable
      reads this, Repr
      requires Inv()
      ensures IndirectionTableModel.Inv(I())
    {
      It.I(Read())
    }

    constructor Box(box: BoxedLinear<indirectionTable>)
      ensures this.box == box
      ensures Repr == {this} + box.Repr
    {
      this.box := box;
      new;
      Repr := {this} + box.Repr;
    }

    constructor Empty()
      ensures Inv()
      ensures fresh(Repr)
    {
      box := new BoxedLinear(IndirectionTableEmptyConstructor());
      new;
      Repr := {this} + box.Repr;
    }

    constructor RootOnly(loc: Location)
      ensures Inv()
      ensures fresh(Repr)
      ensures I() == IndirectionTableModel.ConstructorRootOnly(loc)
    {
      box := new BoxedLinear(IndirectionTableRootOnlyConstructor(loc));
      new;
      Repr := {this} + box.Repr;
    }

//    constructor(t: HashMap)
//    {
//      box := new LinearBox(indirectionTable(t, lNone, 0, None));
//      Repr := {this} + box.Repr;
//    }

    // TODO: need to remember to call this; otherwise, memory will leak
    method Destructor()
      requires Inv()
      modifies Repr
    {
      linear var x := box.Take();
      It.Destructor(x);
    }

    method Clone() returns (table: IndirectionTable)
      requires Inv()
      ensures table.Inv()
      ensures fresh(table.Repr)
      ensures table.I() == IndirectionTableModel.clone(old(I()))
    {
      linear var clone := It.Clone(box.Borrow());
      var boxed := new BoxedLinear(clone);
      table := new IndirectionTable.Box(boxed);
    }

    function method GetEntry(ref: BT.G.Reference) : (e : Option<IndirectionTableModel.Entry>)
      requires Inv()
      reads Repr
      ensures e == IndirectionTableModel.GetEntry(I(), ref)
    {
      It.GetEntry(box.Borrow(), ref)
    }

    function method HasEmptyLoc(ref: BT.G.Reference) : (b: bool)
      requires Inv()
      reads Repr
      ensures b == IndirectionTableModel.HasEmptyLoc(I(), ref)
    {
      It.HasEmptyLoc(box.Borrow(), ref)
    }

    method RemoveLoc(ref: BT.G.Reference) returns (oldLoc: Option<Location>)
      requires Inv()
      requires IndirectionTableModel.TrackingGarbage(I())
      requires ref in I().graph
      modifies Repr
      ensures Inv()
      ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
      ensures (I(), oldLoc) == IndirectionTableModel.RemoveLoc(old(I()), ref)
    {
      linear var x := box.Take();
      x, oldLoc := It.RemoveLoc(x, ref);
      box.Give(x);
    }

    method AddLocIfPresent(ref: BT.G.Reference, loc: Location) returns (added: bool)
      requires Inv()
      modifies Repr
      ensures Inv()
      ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
      ensures (I(), added) == IndirectionTableModel.AddLocIfPresent(old(I()), ref, loc)
    {
      linear var x := box.Take();
      x, added := It.AddLocIfPresent(x, ref, loc);
      box.Give(x);
    }

    method RemoveRef(ref: BT.G.Reference) returns (oldLoc: Option<Location>)
      requires Inv()
      requires IndirectionTableModel.TrackingGarbage(I())
      requires IndirectionTableModel.deallocable(I(), ref)
      modifies Repr
      ensures Inv()
      ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
      ensures (I(), oldLoc) == IndirectionTableModel.RemoveRef(old(I()), ref)
    {
      linear var x := box.Take();
      x, oldLoc := It.RemoveRef(x, ref);
      box.Give(x);
    }

    method UpdateAndRemoveLoc(ref: BT.G.Reference, succs: seq<BT.G.Reference>) returns (oldLoc: Option<Location>)
      requires Inv()
      requires IndirectionTableModel.TrackingGarbage(I())
      requires |succs| <= MaxNumChildren()
      requires |I().graph| < IndirectionTableModel.MaxSize()
      requires IndirectionTableModel.SuccsValid(succs, I().graph)
      modifies Repr
      ensures Inv()
      ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
      ensures (I(), oldLoc) == IndirectionTableModel.UpdateAndRemoveLoc(old(I()), ref, succs)
    {
      linear var x := box.Take();
      x, oldLoc := It.UpdateAndRemoveLoc(x, ref, succs);
      box.Give(x);
    }

    static method ValToIndirectionTable(v: V) returns (s: IndirectionTable?)
      requires IndirectionTableModel.valToIndirectionTable.requires(v)
      ensures s != null ==> s.Inv()
      ensures s != null ==> fresh(s.Repr)
      ensures s == null ==> IndirectionTableModel.valToIndirectionTable(v).None?
      ensures s != null ==> IndirectionTableModel.valToIndirectionTable(v) == Some(s.I())
    {
      linear var opt := It.ValToIndirectionTable(v);
      linear match opt {
        case lNone => {s := null;}
        case lSome(it) => {
          var box := new BoxedLinear(it);
          s := new IndirectionTable.Box(box);
        }
      }
    }

    method indirectionTableToVal() returns (v: V, size: uint64)
      requires Inv()
      requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I()))
      ensures ValInGrammar(v, IndirectionTableModel.IndirectionTableGrammar())
      ensures ValidVal(v)
      ensures IndirectionTableModel.valToIndirectionTable(v).Some?
      ensures
            IndirectionTableModel.I(IndirectionTableModel.valToIndirectionTable(v).value)
         == IndirectionTableModel.I(I())
      ensures SizeOfV(v) <= It.MaxIndirectionTableByteSize()
      ensures SizeOfV(v) == size as int
    {
      v, size := It.indirectionTableToVal(box.Borrow());
    }

    method InitLocBitmap() returns (success: bool, bm: BitmapImpl.Bitmap)
      requires Inv()
      requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I()))
      ensures bm.Inv()
      ensures (success, bm.I()) == IndirectionTableModel.InitLocBitmap(old(I()))
      ensures fresh(bm.Repr)
    {
      success, bm := It.InitLocBitmap(box.Borrow());
    }
    
    function method FindDeallocable() : (ref: Option<BT.G.Reference>)
      requires Inv()
      requires IndirectionTableModel.TrackingGarbage(I())
      reads Repr
      ensures ref == IndirectionTableModel.FindDeallocable(I())
    {
      It.FindDeallocable(box.Borrow())
    }

    function method GetSize() : (size: uint64)
      requires Inv()
      reads Repr
      ensures size as int == |I().graph|
    {
      It.GetSize(box.Borrow())
    }

    method FindRefWithNoLoc() returns (ref: Option<BT.G.Reference>)
      requires Inv()
      modifies Repr
      ensures Inv()
      ensures Repr == old(Repr)
      ensures (I(), ref) == IndirectionTableModel.FindRefWithNoLoc(old(I()))
    {
      linear var x := box.Take();
      x, ref := It.FindRefWithNoLoc(x);
      box.Give(x);
    }

    function method GetRefUpperBound() : (r: uint64)
      requires Inv()
      reads Repr
      ensures r == IndirectionTableModel.getRefUpperBound(this.I())
    {
      It.GetRefUpperBound(box.Borrow())
    }
  }
}
