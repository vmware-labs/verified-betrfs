include "../lib/Base/DebugAccumulator.i.dfy"
include "../lib/Base/Maps.s.dfy"
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/NativeTypes.s.dfy"
include "../lib/DataStructures/LruModel.i.dfy"
include "../lib/DataStructures/MutableMapModel.i.dfy"
include "../lib/DataStructures/MutableMapImpl.i.dfy"
include "../PivotBetree/PivotBetreeSpec.i.dfy"
include "../lib/Marshalling/GenericMarshalling.i.dfy"
include "../lib/DataStructures/BitmapImpl.i.dfy"
include "../lib/DataStructures/LruImpl.i.dfy"
include "IndirectionTableModel.i.dfy"
//
// The heap-y implementation of IndirectionTableModel.
//

module IndirectionTableImpl {
  import DebugAccumulator
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
  import MutableMap
  import opened DiskLayout
  import opened GenericMarshalling
  import BitmapModel
  import BitmapImpl
  import opened Bounds
  import IndirectionTableModel
  import LruImpl
  import opened NativePackedInts
  import Marshalling

  type HashMap = MutableMap.ResizingHashMap<IndirectionTableModel.Entry>

  // TODO move bitmap in here?
  class IndirectionTable {
    var t: HashMap;
    var garbageQueue: LruImpl.LruImplQueue?;
    var refUpperBound: uint64;
    var findLoclessIterator: Option<MutableMapModel.SimpleIterator>;
    ghost var Repr: set<object>;

    method DebugAccumulate()
    returns (acc:DebugAccumulator.DebugAccumulator)
    requires false
    {
      acc := DebugAccumulator.EmptyAccumulator();
      var a := new DebugAccumulator.AccRec(t.Count, "IndirectionTableModel.Entry");
      acc := DebugAccumulator.AccPut(acc, "t", a);
      var r := garbageQueue.DebugAccumulate();
      a := new DebugAccumulator.AccRec.Index(r);
      acc := DebugAccumulator.AccPut(acc, "garbageQueue", a);
    }

    protected predicate Inv()
    reads this, Repr
    ensures Inv() ==> this in Repr
    {
      && this in Repr
      && this.t in Repr
      && (this.garbageQueue != null ==> this.garbageQueue in Repr)
      && this.Repr == {this} + this.t.Repr + (if this.garbageQueue != null then this.garbageQueue.Repr else {})
      && this !in this.t.Repr
      && this.t.Inv()
      && (this.garbageQueue != null ==> this.garbageQueue.Inv())
      && (this.garbageQueue != null ==> this.garbageQueue.Repr !! this.t.Repr)
      && (this.garbageQueue != null ==> this !in this.garbageQueue.Repr)

      && var predCounts := IndirectionTableModel.PredCounts(this.t.I());
      && var graph := IndirectionTableModel.Graph(this.t.I());
      && var locs := IndirectionTableModel.Locs(this.t.I());
      && IndirectionTableModel.ValidPredCounts(predCounts, graph)
      && BC.GraphClosed(graph)
      && (forall ref | ref in graph :: |graph[ref]| <= MaxNumChildren())
      && (this.garbageQueue != null ==> (
        && (forall ref | ref in this.t.I().contents && t.I().contents[ref].predCount == 0 :: ref in LruModel.I(garbageQueue.Queue))
        && (forall ref | ref in LruModel.I(garbageQueue.Queue) :: ref in t.I().contents && t.I().contents[ref].predCount == 0)
      ))
      && BT.G.Root() in t.I().contents
      && this.t.Count as int <= IndirectionTableModel.MaxSize()
      && (forall ref | ref in graph :: ref <= this.refUpperBound)
      && (findLoclessIterator.Some? ==>
        && MutableMapModel.WFSimpleIter(t.I(),
            findLoclessIterator.value)
        && (forall r | r in findLoclessIterator.value.s ::
            r in locs)
      )
    }

    protected function I() : IndirectionTableModel.IndirectionTable
    reads this, Repr
    requires Inv()
    ensures IndirectionTableModel.Inv(I())
    {
      var res := IndirectionTableModel.FromHashMap(t.I(), if garbageQueue != null then Some(garbageQueue.Queue) else None, refUpperBound, findLoclessIterator);
      IndirectionTableModel.reveal_Inv(res);
      res
    }

    // Dummy constructor only used when ImplVariables is in a state with no indirection
    // table. We could use a null indirection table instead, it's just slightly more
    // annoying to do that because we'd need additional invariants.
    constructor Empty()
    ensures Inv()
    ensures fresh(Repr)
    {
      this.t := new MutableMap.ResizingHashMap(128);
      this.findLoclessIterator := None;
      new;
      // This is not important, but needed to satisfy the Inv:
      this.t.Insert(BT.G.Root(), IndirectionTableModel.Entry(None, [], 1));
      this.garbageQueue := null;
      Repr := {this} + this.t.Repr;
    }

    constructor RootOnly(loc: Location)
    ensures Inv()
    ensures fresh(Repr)
    ensures I() == IndirectionTableModel.ConstructorRootOnly(loc)
    {
      this.t := new MutableMap.ResizingHashMap(128);
      this.findLoclessIterator := None;
      new;
      this.t.Insert(BT.G.Root(), IndirectionTableModel.Entry(Some(loc), [], 1));
      this.garbageQueue := null;
      this.refUpperBound := BT.G.Root();
      Repr := {this} + this.t.Repr;
      IndirectionTableModel.reveal_ConstructorRootOnly();
    }

    constructor(t: HashMap)
    ensures this.t == t
    ensures this.garbageQueue == null
    {
      this.t := t;
      this.garbageQueue := null;
    }

    method Clone()
    returns (table : IndirectionTable)
    requires Inv()
    ensures table.Inv()
    ensures fresh(table.Repr)
    ensures table.I() == IndirectionTableModel.clone(old(I()))
    {
      var t0 := this.t.Clone();
      table := new IndirectionTable(t0);
      table.refUpperBound := this.refUpperBound;
      table.findLoclessIterator := None;

      table.Repr := {table} + table.t.Repr + (if table.garbageQueue != null then table.garbageQueue.Repr else {});
      IndirectionTableModel.reveal_clone();
    }

    method GetEntry(ref: BT.G.Reference) returns (e : Option<IndirectionTableModel.Entry>)
    requires Inv()
    ensures e == IndirectionTableModel.GetEntry(I(), ref)
    {
      IndirectionTableModel.reveal_GetEntry();
      e := this.t.Get(ref);
    }

    method HasEmptyLoc(ref: BT.G.Reference) returns (b: bool)
    requires Inv()
    ensures b == IndirectionTableModel.HasEmptyLoc(I(), ref)
    {
      var entry := this.t.Get(ref);
      b := entry.Some? && entry.value.loc.None?;
    }

    method RemoveLoc(ref: BT.G.Reference)
    returns (oldLoc: Option<Location>)
    requires Inv()
    requires IndirectionTableModel.TrackingGarbage(I())
    requires ref in I().graph
    modifies Repr
    ensures Inv()
    ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
    ensures (I(), oldLoc) == IndirectionTableModel.RemoveLoc(old(I()), ref)
    {
      IndirectionTableModel.reveal_RemoveLoc();

      var it := t.FindSimpleIter(ref);
      var oldEntry := t.SimpleIterOutput(it);
      var predCount := oldEntry.value.predCount;
      var succs := oldEntry.value.succs;
      t.UpdateByIter(it, IndirectionTableModel.Entry(None, succs, predCount));
      this.findLoclessIterator := None;

      oldLoc := oldEntry.value.loc;

      Repr := {this} + this.t.Repr + (if this.garbageQueue != null then this.garbageQueue.Repr else {});
      ghost var _ := IndirectionTableModel.RemoveLoc(old(I()), ref);
    }

    method AddLocIfPresent(ref: BT.G.Reference, loc: Location)
    returns (added : bool)
    requires Inv()
    modifies Repr
    ensures Inv()
    ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
    ensures (I(), added) == IndirectionTableModel.AddLocIfPresent(old(I()), ref, loc)
    {
      IndirectionTableModel.reveal_AddLocIfPresent();

      var it := this.t.FindSimpleIter(ref);
      var oldEntry := this.t.SimpleIterOutput(it);
      added := oldEntry.Next? && oldEntry.value.loc.None?;

      if added {
        ghost var ghosty := true;
        if ghosty {
          if I().findLoclessIterator.Some? {
            MutableMapModel.UpdatePreservesSimpleIter(I().t, it, IndirectionTableModel.Entry(Some(loc), oldEntry.value.succs, oldEntry.value.predCount), I().findLoclessIterator.value);
          }
        }

        this.t.UpdateByIter(it, IndirectionTableModel.Entry(Some(loc), oldEntry.value.succs, oldEntry.value.predCount));
      }

      Repr := {this} + this.t.Repr + (if this.garbageQueue != null then this.garbageQueue.Repr else {});
      ghost var _ := IndirectionTableModel.AddLocIfPresent(old(I()), ref, loc);
    }

    method RemoveRef(ref: BT.G.Reference)
    returns (oldLoc : Option<Location>)
    requires Inv()
    requires IndirectionTableModel.TrackingGarbage(I())
    requires IndirectionTableModel.deallocable(I(), ref)
    modifies Repr
    ensures Inv()
    ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
    ensures (I(), oldLoc) == IndirectionTableModel.RemoveRef(old(I()), ref)
    {
      IndirectionTableModel.reveal_RemoveRef();

      IndirectionTableModel.lemma_count_eq_graph_size(I().t);
      IndirectionTableModel.LemmaRemoveRefStuff(I(), ref);

      var oldEntry := this.t.RemoveAndGet(ref);

      IndirectionTableModel.lemma_count_eq_graph_size(this.t.I());

      this.garbageQueue.Remove(ref);
      UpdatePredCounts(this.t, this.garbageQueue, ref, [], oldEntry.value.succs);

      IndirectionTableModel.lemma_count_eq_graph_size(this.t.I());

      oldLoc := if oldEntry.Some? then oldEntry.value.loc else None;
      this.findLoclessIterator := None;

      Repr := {this} + this.t.Repr + (if this.garbageQueue != null then this.garbageQueue.Repr else {});
      ghost var _ := IndirectionTableModel.RemoveRef(old(I()), ref);
    }

    static method PredInc(t: HashMap, q: LruImpl.LruImplQueue, ref: BT.G.Reference)
    requires t.Inv()
    requires q.Inv()
    requires t.Count as nat < 0x1_0000_0000_0000_0000 / 8
    requires ref in t.I().contents
    requires t.I().contents[ref].predCount < 0xffff_ffff_ffff_ffff
    requires t.Repr !! q.Repr
    modifies t.Repr
    modifies q.Repr
    ensures forall o | o in t.Repr :: o in old(t.Repr) || fresh(o)
    ensures forall o | o in q.Repr :: o in old(q.Repr) || fresh(o)
    ensures t.Repr !! q.Repr
    ensures t.Inv()
    ensures q.Inv()
    ensures (t.I(), q.Queue) == IndirectionTableModel.PredInc(old(t.I()), old(q.Queue), ref)
    {
      var oldEntryOpt := t.Get(ref);
      var oldEntry := oldEntryOpt.value;
      var newEntry := oldEntry.(predCount := oldEntry.predCount + 1);
      t.Insert(ref, newEntry);
      if oldEntry.predCount == 0 {
        q.Remove(ref);
      }
    }

    static method PredDec(t: HashMap, q: LruImpl.LruImplQueue, ref: BT.G.Reference)
    requires t.Inv()
    requires q.Inv()
    requires t.Count as nat < 0x1_0000_0000_0000_0000 / 8
    requires ref in t.I().contents
    requires t.I().contents[ref].predCount > 0
    requires t.Repr !! q.Repr
    requires |LruModel.I(q.Queue)| <= 0x1_0000_0000;
    modifies t.Repr
    modifies q.Repr
    ensures forall o | o in t.Repr :: o in old(t.Repr) || fresh(o)
    ensures forall o | o in q.Repr :: o in old(q.Repr) || fresh(o)
    ensures t.Repr !! q.Repr
    ensures t.Inv()
    ensures q.Inv()
    ensures (t.I(), q.Queue) == IndirectionTableModel.PredDec(old(t.I()), old(q.Queue), ref)
    {
      var oldEntryOpt := t.Get(ref);
      var oldEntry := oldEntryOpt.value;
      var newEntry := oldEntry.(predCount := oldEntry.predCount - 1);
      t.Insert(ref, newEntry);
      if oldEntry.predCount == 1 {
        q.Use(ref);
      }
    }

    static method UpdatePredCounts(t: HashMap, q: LruImpl.LruImplQueue, ghost changingRef: BT.G.Reference,
        newSuccs: seq<BT.G.Reference>, oldSuccs: seq<BT.G.Reference>)
    requires t.Inv()
    requires q.Inv()
    requires t.Repr !! q.Repr
    requires IndirectionTableModel.RefcountUpdateInv(t.I(), q.Queue, changingRef, newSuccs, oldSuccs, 0, 0)
    modifies t.Repr
    modifies q.Repr
    ensures forall o | o in t.Repr :: o in old(t.Repr) || fresh(o)
    ensures forall o | o in q.Repr :: o in old(q.Repr) || fresh(o)
    ensures t.Repr !! q.Repr
    ensures t.Inv()
    ensures q.Inv()
    ensures (t.I(), q.Queue) == IndirectionTableModel.UpdatePredCountsInc(old(t.I()), old(q.Queue), changingRef, newSuccs, oldSuccs, 0)
    {
      var idx: uint64 := 0;

      while idx < |newSuccs| as uint64
      invariant forall o | o in t.Repr :: o in old(t.Repr) || fresh(o)
      invariant forall o | o in q.Repr :: o in old(q.Repr) || fresh(o)
      invariant t.Repr !! q.Repr
      invariant t.Inv()
      invariant q.Inv()
      invariant IndirectionTableModel.RefcountUpdateInv(t.I(), q.Queue, changingRef, newSuccs, oldSuccs, idx as int, 0)
      invariant IndirectionTableModel.UpdatePredCountsInc(old(t.I()), old(q.Queue), changingRef, newSuccs, oldSuccs, 0)
             == IndirectionTableModel.UpdatePredCountsInc(t.I(), q.Queue, changingRef, newSuccs, oldSuccs, idx)
      decreases |newSuccs| - idx as int
      {
        IndirectionTableModel.LemmaUpdatePredCountsIncStuff(t.I(), q.Queue, changingRef, newSuccs, oldSuccs, idx as int);

        PredInc(t, q, newSuccs[idx]);
        idx := idx + 1;
      }

      var idx2: uint64 := 0;

      while idx2 < |oldSuccs| as uint64
      invariant forall o | o in t.Repr :: o in old(t.Repr) || fresh(o)
      invariant forall o | o in q.Repr :: o in old(q.Repr) || fresh(o)
      invariant t.Repr !! q.Repr
      invariant t.Inv()
      invariant q.Inv()
      invariant IndirectionTableModel.RefcountUpdateInv(t.I(), q.Queue, changingRef, newSuccs, oldSuccs, |newSuccs|, idx2 as int)
      invariant IndirectionTableModel.UpdatePredCountsInc(old(t.I()), old(q.Queue), changingRef, newSuccs, oldSuccs, 0)
             == IndirectionTableModel.UpdatePredCountsDec(t.I(), q.Queue, changingRef, newSuccs, oldSuccs, idx2)
      decreases |oldSuccs| - idx2 as int
      {
        IndirectionTableModel.LemmaUpdatePredCountsDecStuff(t.I(), q.Queue, changingRef, newSuccs, oldSuccs, idx2 as int);

        PredDec(t, q, oldSuccs[idx2]);
        idx2 := idx2 + 1;
      }
    }

    method UpdateAndRemoveLoc(ref: BT.G.Reference, succs: seq<BT.G.Reference>)
    returns (oldLoc : Option<Location>)
    requires Inv()
    requires IndirectionTableModel.TrackingGarbage(I())
    requires |succs| <= MaxNumChildren()
    requires |I().graph| < IndirectionTableModel.MaxSize()
    requires IndirectionTableModel.SuccsValid(succs, I().graph)
    modifies Repr
    ensures Inv()
    ensures forall o | o in Repr :: fresh(o) || o in old(Repr)
    ensures (I(), oldLoc)  == IndirectionTableModel.UpdateAndRemoveLoc(old(I()), ref, succs)
    {
      IndirectionTableModel.reveal_UpdateAndRemoveLoc();

      IndirectionTableModel.lemma_count_eq_graph_size(I().t);
      IndirectionTableModel.LemmaUpdateAndRemoveLocStuff(I(), ref, succs);

      var oldEntry := this.t.Get(ref);
      var predCount := if oldEntry.Some? then oldEntry.value.predCount else 0;
      if oldEntry.None? {
        this.garbageQueue.Use(ref);
      }
      this.t.Insert(ref, IndirectionTableModel.Entry(None, succs, predCount));

      IndirectionTableModel.lemma_count_eq_graph_size(this.t.I());

      UpdatePredCounts(this.t, this.garbageQueue, ref, succs,
          if oldEntry.Some? then oldEntry.value.succs else []);

      IndirectionTableModel.lemma_count_eq_graph_size(this.t.I());

      //IndirectionTableModel.LemmaValidPredCountsOfValidPredCountsIntermediate(IndirectionTableModel.PredCounts(this.t.I()), IndirectionTableModel.Graph(this.t.I()), succs, if oldEntry.Some? then oldEntry.value.succs else []);

      if ref > this.refUpperBound {
        this.refUpperBound := ref;
      }

      oldLoc := if oldEntry.Some? && oldEntry.value.loc.Some? then oldEntry.value.loc else None;
      this.findLoclessIterator := None;

      Repr := {this} + this.t.Repr + (if this.garbageQueue != null then this.garbageQueue.Repr else {});
      ghost var _ := IndirectionTableModel.UpdateAndRemoveLoc(old(I()), ref, succs);
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

    static method {:fuel ValInGrammar,3} ValToHashMap(a: seq<V>) returns (s : Option<HashMap>)
    requires IndirectionTableModel.valToHashMap.requires(a)
    ensures s.None? ==> IndirectionTableModel.valToHashMap(a).None?
    ensures s.Some? ==> s.value.Inv()
    ensures s.Some? ==> Some(s.value.I()) == IndirectionTableModel.valToHashMap(a)
    ensures s.Some? ==> s.value.Count as nat == |a|
    ensures s.Some? ==> s.value.Count as nat < 0x1_0000_0000_0000_0000 / 8
    ensures s.Some? ==> fresh(s.value) && fresh(s.value.Repr)
    {
      var i: uint64 := 0;
      var mutMap := new MutableMap.ResizingHashMap<IndirectionTableModel.Entry>(1024); // TODO(alattuada) magic numbers

      while i < |a| as uint64
      invariant 0 <= i as int <= |a|
      invariant mutMap.Inv()
      invariant fresh(mutMap.Repr)
      invariant IndirectionTableModel.valToHashMap(a[..i]) == Some(mutMap.I())
      {
        var tuple := a[i];
        var ref := tuple.t[0 as uint64].u;
        var addr := tuple.t[1 as uint64].u;
        var len := tuple.t[2 as uint64].u;
        var succs := tuple.t[3 as uint64].ua;
        var graphRef := mutMap.Get(ref);
        var loc := Location(addr, len);

        assert ValidVal(tuple);
        assert ValidVal(tuple.t[3]);
        assert |succs| < 0x1_0000_0000_0000_0000;

        assert DropLast(a[..i+1]) == a[..i];
        assert Last(a[..i+1]) == a[i];

        if graphRef.Some? || !ValidNodeLocation(loc)
            || |succs| as uint64 > MaxNumChildrenUint64() {
          lemma_valToHashMapNonePrefix(a, (i+1) as int);
          return None;
        } else {
          mutMap.Insert(ref, IndirectionTableModel.Entry(Some(loc), succs, 0));
          i := i + 1;
        }
      }

      assert a[..i] == a;
      return Some(mutMap);
    }

    static method ComputeRefCounts(t: HashMap)
    returns (t' : MutableMap.ResizingHashMap?<IndirectionTableModel.Entry>)
    requires t.Inv()
    requires forall ref | ref in t.I().contents :: t.I().contents[ref].predCount == 0
    requires forall ref | ref in t.I().contents :: |t.I().contents[ref].succs| <= MaxNumChildren()
    requires t.I().count as int <= IndirectionTableModel.MaxSize()
    requires BT.G.Root() in t.I().contents
    ensures t' == null ==> IndirectionTableModel.ComputeRefCounts(old(t.I())) == None
    ensures t' != null ==> t'.Inv()
    ensures t' != null ==> IndirectionTableModel.ComputeRefCounts(old(t.I())) == Some(t'.I())
    ensures t' != null ==> fresh(t'.Repr)
    {
      IndirectionTableModel.LemmaComputeRefCountsIterateInvInit(t.I());

      var copy := t;
      var t1 := t.Clone();

      var oldEntryOpt := t1.Get(BT.G.Root());
      var oldEntry := oldEntryOpt.value;
      t1.Insert(BT.G.Root(), oldEntry.(predCount := 1));

      var it := copy.IterStart();
      while it.next.Next?
      invariant t1.Inv()
      invariant copy.Inv()
      invariant copy.Repr !! t1.Repr
      invariant fresh(t1.Repr)

      invariant IndirectionTableModel.ComputeRefCountsIterateInv(t1.I(), copy.I(), it)
      invariant BT.G.Root() in t1.I().contents
      invariant IndirectionTableModel.ComputeRefCounts(old(t.I()))
             == IndirectionTableModel.ComputeRefCountsIterate(t1.I(), copy.I(), it)
      decreases it.decreaser
      {
        IndirectionTableModel.LemmaComputeRefCountsIterateStuff(t1.I(), copy.I(), it);
        IndirectionTableModel.LemmaComputeRefCountsIterateValidPredCounts(t1.I(), copy.I(), it);

        ghost var t0 := t1.I();

        var succs := it.next.value.succs;
        var i: uint64 := 0;
        while i < |succs| as uint64
        invariant t1.Inv()
        invariant copy.Inv()
        invariant copy.Repr !! t1.Repr
        invariant fresh(t1.Repr)

        invariant BT.G.Root() in t1.I().contents
        invariant 0 <= i as int <= |succs|
        invariant |succs| <= MaxNumChildren()
        invariant t1.I().count as int <= IndirectionTableModel.MaxSize()
        invariant forall ref | ref in t1.I().contents :: t1.I().contents[ref].predCount as int <= 0x1_0000_0000_0000 + i as int
        invariant IndirectionTableModel.ComputeRefCounts(old(t.I()))
               == IndirectionTableModel.ComputeRefCountsIterate(t0, copy.I(), it)
        invariant IndirectionTableModel.ComputeRefCountsEntryIterate(t0, succs, 0)
               == IndirectionTableModel.ComputeRefCountsEntryIterate(t1.I(), succs, i)
        decreases |succs| - i as int
        {
          var ref := succs[i];
          var oldEntry := t1.Get(ref);
          if oldEntry.Some? {
            var newEntry := oldEntry.value.(predCount := oldEntry.value.predCount + 1);
            t1.Insert(ref, newEntry);
            i := i + 1;
          } else {
            return null;
          }
        }

        it := copy.IterInc(it);
      }

      return t1;
    }

    static method MakeGarbageQueue(t: HashMap)
    returns (q : LruImpl.LruImplQueue)
    requires t.Inv()
    requires |t.I().contents| <= 0x1_0000_0000
    ensures q.Inv()
    ensures fresh(q.Repr)
    ensures q.Queue == IndirectionTableModel.makeGarbageQueue(t.I())
    {
      IndirectionTableModel.reveal_makeGarbageQueue();

      q := new LruImpl.LruImplQueue();
      var it := t.IterStart();
      while it.next.Next?
      invariant q.Inv()
      invariant fresh(q.Repr)
      invariant MutableMapModel.Inv(t.I())
      invariant MutableMapModel.WFIter(t.I(), it)
      invariant IndirectionTableModel.makeGarbageQueue(t.I())
             == IndirectionTableModel.makeGarbageQueueIterate(t.I(), q.Queue, it)
      invariant LruModel.I(q.Queue) <= t.I().contents.Keys
      invariant |t.I().contents| <= 0x1_0000_0000
      decreases it.decreaser
      {
        if it.next.value.predCount == 0 {
          LruModel.LruUse(q.Queue, it.next.key);

          SetInclusionImpliesSmallerCardinality(
              LruModel.I(q.Queue), t.I().contents.Keys);
          assert |t.I().contents.Keys| == |t.I().contents|;

          q.Use(it.next.key);
        }
        it := t.IterInc(it);
      }
    }

    static method ComputeRefUpperBound(t: HashMap)
    returns (r: uint64)
    requires t.Inv()
    ensures r == IndirectionTableModel.computeRefUpperBound(t.I())
    {
      var it := t.IterStart();
      var refUpperBound := 0;
      while it.next.Next?
      invariant MutableMapModel.Inv(t.I())
      invariant MutableMapModel.WFIter(t.I(), it)
      invariant forall ref | ref in it.s :: ref <= refUpperBound
      invariant IndirectionTableModel.computeRefUpperBoundIterate(t.I(), it, refUpperBound)
             == IndirectionTableModel.computeRefUpperBound(t.I())
      decreases it.decreaser
      {
        if it.next.key > refUpperBound {
          refUpperBound := it.next.key;
        }
        it := t.IterInc(it);
      }
      r := refUpperBound;
    }

    static method ValToIndirectionTable(v: V)
    returns (s : IndirectionTable?)
    requires IndirectionTableModel.valToIndirectionTable.requires(v)
    ensures s != null ==> s.Inv()
    ensures s != null ==> fresh(s.Repr)
    ensures s == null ==> IndirectionTableModel.valToIndirectionTable(v).None?
    ensures s != null ==> IndirectionTableModel.valToIndirectionTable(v) == Some(s.I())
    {
      if |v.a| as uint64 <= IndirectionTableModel.MaxSizeUint64() {
        var res := ValToHashMap(v.a);
        match res {
          case Some(t) => {
            var rootRef := t.Get(BT.G.Root());
            if rootRef.Some? {
              var t1 := ComputeRefCounts(t);
              if t1 != null {
                IndirectionTableModel.lemmaMakeGarbageQueueCorrect(t1.I());
                IndirectionTableModel.lemma_count_eq_graph_size(t.I());
                IndirectionTableModel.lemma_count_eq_graph_size(t1.I());

                var q := MakeGarbageQueue(t1);
                s := new IndirectionTable(t1);
                s.garbageQueue := q;
                s.refUpperBound := ComputeRefUpperBound(t1);
                s.findLoclessIterator := None;
                s.Repr := {s} + s.t.Repr + s.garbageQueue.Repr;
              } else {
                s := null;
              }
            } else {
              s := null;
            }
          }
          case None => {
            s := null;
          }
        }
      } else {
        s := null;
      }
    }

    function MaxIndirectionTableByteSize() : int {
      8 + IndirectionTableModel.MaxSize() * (8 + 8 + 8 + (8 + MaxNumChildren() * 8))
    }

    lemma lemma_SeqSum_prefix_array(a: array<V>, i: int)
    requires 0 < i <= a.Length
    ensures SeqSum(a[..i-1]) + SizeOfV(a[i-1]) == SeqSum(a[..i])
    {
      lemma_SeqSum_prefix(a[..i-1], a[i-1]);
      assert a[..i-1] + [a[i-1]] == a[..i];
    }

    lemma {:fuel SizeOfV,5} lemma_tuple_size(a: uint64, b: uint64, c: uint64, succs: seq<BT.G.Reference>)
    requires|succs| <= MaxNumChildren()
    ensures SizeOfV(VTuple([VUint64(a), VUint64(b), VUint64(c), VUint64Array(succs)]))
         == (8 + 8 + 8 + (8 + |succs| * 8))
    {
    }

    lemma lemma_SeqSum_empty()
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
    // requires Inv()
    // requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I()))

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
    //      ) == IndirectionTableModel.I(I())
    // {
    //   var idx := start;
    //   var it := t.IterStart();
    //   while it.next.Next?
    //   {
    //   }
    // }

    // method marshallIndirectionTable(data: array<byte>, start_idx: uint64)
    // returns (end: uint64)
    // requires Inv()
    // requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I()))
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
    method indirectionTableToVal()
    returns (v : V, size: uint64)
    requires Inv()
    requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I()))
    ensures ValInGrammar(v, IndirectionTableModel.IndirectionTableGrammar())
    ensures ValidVal(v)
    ensures IndirectionTableModel.valToIndirectionTable(v).Some?
    ensures
          IndirectionTableModel.I(IndirectionTableModel.valToIndirectionTable(v).value)
       == IndirectionTableModel.I(I())
    ensures SizeOfV(v) <= MaxIndirectionTableByteSize()
    ensures SizeOfV(v) == size as int
    {
      assert t.Count <= IndirectionTableModel.MaxSizeUint64();
      lemma_SeqSum_empty();
      var a: array<V> := new V[t.Count as uint64];
      var it := t.IterStart();
      var i: uint64 := 0;
      size := 0;

      ghost var partial := map[];
      while it.next.Next?
      invariant Inv()
      invariant BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I()))
      invariant 0 <= i as int <= a.Length
      invariant MutableMapModel.WFIter(t.I(), it);
      invariant forall j | 0 <= j < i :: ValidVal(a[j])
      invariant forall j | 0 <= j < i :: ValInGrammar(a[j], GTuple([GUint64, GUint64, GUint64, GUint64Array]))
      // NOALIAS/CONST table doesn't need to be mutable, if we could say so we wouldn't need this
      invariant IndirectionTableModel.valToHashMap(a[..i]).Some?
      invariant IndirectionTableModel.valToHashMap(a[..i]).value.contents == partial
      invariant |partial.Keys| == i as nat
      invariant partial.Keys == it.s
      invariant partial.Keys <= t.I().contents.Keys
      invariant forall r | r in partial :: r in t.I().contents
          && partial[r].loc == t.I().contents[r].loc
          && partial[r].succs == t.I().contents[r].succs
      // NOALIAS/CONST t doesn't need to be mutable, if we could say so we wouldn't need this
      invariant t.I().contents == old(t.I().contents)
      invariant size as int <=
          |it.s| * (8 + 8 + 8 + (8 + MaxNumChildren() * 8))
      invariant SeqSum(a[..i]) == size as int;
      decreases it.decreaser
      {
        var (ref, locOptGraph: IndirectionTableModel.Entry) := (it.next.key, it.next.value);
        assert ref in I().locs;
        // NOTE: deconstructing in two steps to work around c# translation bug
        var locOpt := locOptGraph.loc;
        var succs := locOptGraph.succs;
        var loc := locOpt.value;
        //ghost var predCount := locOptGraph.predCount;
        var childrenVal := VUint64Array(succs);

        assert |succs| <= MaxNumChildren();

        //assert I().locs[ref] == loc;
        //assert I().graph[ref] == succs;

        //assert IndirectionTableModel.I(I()).locs[ref] == loc;
        //assert IndirectionTableModel.I(I()).graph[ref] == succs;

        assert ValidNodeLocation(loc);
        /*ghost var t0 := IndirectionTableModel.valToHashMap(a[..i]);
        assert ref !in t0.value.contents;
        assert loc.addr != 0;
        assert LBAType.ValidLocation(loc);*/

        MutableMapModel.LemmaIterIndexLtCount(t.I(), it);

        assert |succs| < 0x1_0000_0000_0000_0000;
        assert ValidVal(VTuple([VUint64(ref), VUint64(loc.addr), VUint64(loc.len), childrenVal]));

        assert |MutableMapModel.IterInc(t.I(), it).s| == |it.s| + 1;

        var vi := VTuple([VUint64(ref), VUint64(loc.addr), VUint64(loc.len), childrenVal]);

        //assert SizeOfV(vi) <= (8 + 8 + 8 + (8 + MaxNumChildren() * 8));

        // == mutation ==
        partial := partial[ref := IndirectionTableModel.Entry(locOpt, succs, 0)];
        a[i] := vi;
        i := i + 1;
        it := t.IterInc(it);
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

      /* (doc) assert |partial.Keys| == |t.I().contents.Keys|; */
      SetInclusionAndEqualCardinalityImpliesSetEquality(partial.Keys, t.I().contents.Keys);

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

    method InitLocBitmap()
    returns (success: bool, bm: BitmapImpl.Bitmap)
    requires Inv()
    requires BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I()))
    ensures bm.Inv()
    ensures (success, bm.I()) == IndirectionTableModel.InitLocBitmap(old(I()))
    ensures fresh(bm.Repr)
    {
      IndirectionTableModel.reveal_InitLocBitmap();

      bm := new BitmapImpl.Bitmap(NumBlocksUint64());
      BitmapInitUpTo(bm, MinNodeBlockIndexUint64());
      var it := t.IterStart();
      while it.next.Next?
      invariant t.Inv()
      invariant BC.WFCompleteIndirectionTable(IndirectionTableModel.I(I()))
      invariant bm.Inv()
      invariant MutableMapModel.WFIter(t.I(), it)
      invariant BitmapModel.Len(bm.I()) == NumBlocks()
      invariant IndirectionTableModel.InitLocBitmapIterate(I(), it, bm.I())
             == IndirectionTableModel.InitLocBitmap(I())
      invariant fresh(bm.Repr)
      decreases it.decreaser
      {
        assert it.next.key in IndirectionTableModel.I(I()).locs;

        var loc: uint64 := it.next.value.loc.value.addr;
        var locIndex: uint64 := loc / NodeBlockSizeUint64();
        if locIndex < NumBlocksUint64() {
          var isSet := bm.GetIsSet(locIndex);
          if !isSet {
            it := t.IterInc(it);
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

    method FindDeallocable() returns (ref: Option<BT.G.Reference>)
    requires Inv()
    requires IndirectionTableModel.TrackingGarbage(I())
    ensures ref == IndirectionTableModel.FindDeallocable(I())
    {
      IndirectionTableModel.reveal_FindDeallocable();
      ref := garbageQueue.NextOpt();
    }

    method GetSize()
    returns (size: uint64)
    requires Inv()
    ensures size as int == |I().graph|
    {
      IndirectionTableModel.lemma_count_eq_graph_size(I().t);
      return this.t.Count;
    }

    method FindRefWithNoLoc() returns (ref: Option<BT.G.Reference>)
    requires Inv()
    modifies Repr
    ensures Inv()
    ensures Repr == old(Repr)
    ensures (I(), ref) == IndirectionTableModel.FindRefWithNoLoc(old(I()))
    {
      IndirectionTableModel.reveal_FindRefWithNoLoc();

      var it;
      if this.findLoclessIterator.Some? {
        it := this.findLoclessIterator.value;
      } else {
        it := this.t.SimpleIterStart();
      }

      while true
      invariant Inv()
      invariant MutableMapModel.WFSimpleIter(this.t.I(), it)
      invariant forall r | r in it.s :: r in I().locs
      invariant IndirectionTableModel.FindRefWithNoLoc(old(I()))
          == IndirectionTableModel.FindRefWithNoLocIterate(I(), it)
      invariant Repr == old(Repr)
      decreases it.decreaser
      {
        var next := this.t.SimpleIterOutput(it);
        if next.Next? {
          if next.value.loc.None? {
            this.findLoclessIterator := Some(it);
            return Some(next.key);
          } else {
            it := this.t.SimpleIterInc(it);
          }
        } else {
          this.findLoclessIterator := Some(it);
          return None;
        }
      }
    }

    method GetRefUpperBound() returns (r: uint64)
    requires Inv()
    ensures r == IndirectionTableModel.getRefUpperBound(this.I())
    {
      IndirectionTableModel.reveal_getRefUpperBound();
      return this.refUpperBound;
    }
  }
}
