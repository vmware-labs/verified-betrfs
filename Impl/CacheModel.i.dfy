include "ModelState.i.dfy"
include "IOModel.i.dfy"
include "../lib/Base/Sets.i.dfy"

module ImplModelCache { 
  import opened ImplModel
  import opened ImplModelIO

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketWeights
  import opened Bounds
  import LruModel

  import opened NativeTypes

  predicate RefAvailable(s: Variables, ref: Reference)
  {
    && s.Ready?
    && ref !in s.ephemeralIndirectionTable.graph
    && ref !in s.cache 
    && ref != BT.G.Root()
  }

  function getFreeRefIterate(s: Variables, i: uint64) 
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
  requires i >= 1
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  decreases 0x1_0000_0000_0000_0000 - i as int
  {
    if i !in s.ephemeralIndirectionTable.graph && i !in s.cache then (
      Some(i)
    ) else if i == 0xffff_ffff_ffff_ffff then (
      None
    ) else (
      getFreeRefIterate(s, i+1) 
    )
  }

  function {:opaque} getFreeRef(s: Variables)
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  {
    getFreeRefIterate(s, 1)
  }

  function getFreeRef2Iterate(s: Variables, avoid: BT.G.Reference, i: uint64) 
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
  requires i >= 1
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  ensures ref.Some? ==> ref.value != avoid
  decreases 0x1_0000_0000_0000_0000 - i as int
  {
    if i != avoid && i !in s.ephemeralIndirectionTable.graph && i !in s.cache then (
      Some(i)
    ) else if i == 0xffff_ffff_ffff_ffff then (
      None
    ) else (
      getFreeRef2Iterate(s, avoid, i+1) 
    )
  }

  function {:opaque} getFreeRef2(s: Variables, avoid: BT.G.Reference)
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  ensures ref.Some? ==> ref.value != avoid
  {
    getFreeRef2Iterate(s, avoid, 1)
  }

  // Conditions that will hold intermediately between writes and allocs
  predicate WriteAllocConditions(k: Constants, s: Variables)
  {
    && s.Ready?
    && IndirectionTableModel.Inv(s.ephemeralIndirectionTable)
    && IndirectionTableModel.TrackingGarbage(s.ephemeralIndirectionTable)
    && (forall loc |
        loc in IIndirectionTable(s.ephemeralIndirectionTable).locs.Values :: 
          BC.ValidLocationForNode(loc))
    && ConsistentBitmap(s.ephemeralIndirectionTable, s.frozenIndirectionTable,
        s.persistentIndirectionTable, s.outstandingBlockWrites, s.blockAllocator)
    && BlockAllocatorModel.Inv(s.blockAllocator)
    && BC.AllLocationsForDifferentRefsDontOverlap(
        IIndirectionTable(s.ephemeralIndirectionTable))
  }

  predicate ChildrenConditions(k: Constants, s: Variables, succs: Option<seq<BT.G.Reference>>)
  requires s.Ready?
  {
    succs.Some? ==> (
      && |succs.value| <= MaxNumChildren()
      && IndirectionTableModel.SuccsValid(succs.value, s.ephemeralIndirectionTable.graph)
    )
  }

  lemma lemmaIndirectionTableLocIndexValid(k: Constants, s: Variables, ref: BT.G.Reference)
  requires WriteAllocConditions(k, s)
  ensures ref in s.ephemeralIndirectionTable.locs ==>
    (
      && 0 <= s.ephemeralIndirectionTable.locs[ref].addr as int / BlockSize() < NumBlocks()
      && (s.ephemeralIndirectionTable.locs[ref].addr as int / BlockSize()) * BlockSize() == s.ephemeralIndirectionTable.locs[ref].addr as int
    )
  {
    if ref in s.ephemeralIndirectionTable.locs {
      reveal_ConsistentBitmap();
      var loc := s.ephemeralIndirectionTable.locs[ref];
      var i := loc.addr as int / BlockSize();
      assert IIndirectionTable(s.ephemeralIndirectionTable).locs[ref] == loc;
      assert loc in IIndirectionTable(s.ephemeralIndirectionTable).locs.Values;
      assert BC.ValidLocationForNode(loc);
      LBAType.reveal_ValidAddr();
      assert i * BlockSize() == loc.addr as int;
      assert IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
    }
  }

  // Bookkeeping only - we update the cache with the Node separately.
  // This turns out to be easier to do.

  function {:opaque} writeBookkeeping(k: Constants, s: Variables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  : (s': Variables)
  requires WriteAllocConditions(k, s)
  requires ChildrenConditions(k, s, children)
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  ensures s'.Ready?
  ensures s'.cache == s.cache
  ensures WriteAllocConditions(k, s')
  ensures |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
    lemmaIndirectionTableLocIndexValid(k, s, ref);
    var (eph, oldLoc) := IndirectionTableModel.UpdateAndRemoveLoc(s.ephemeralIndirectionTable, ref,
        (if children.Some? then children.value else []));
    var blockAllocator' := if oldLoc.Some?
      then BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / BlockSize())
      else s.blockAllocator;
    var s' := s.(ephemeralIndirectionTable := eph)
     .(lru := LruModel.Use(s.lru, ref))
     .(blockAllocator := blockAllocator');

    freeIndirectionTableLocCorrect(k, s, s', ref,
      if oldLoc.Some?
      then Some(oldLoc.value.addr as int / BlockSize())
      else None);
    reveal_ConsistentBitmap();

    s'
  }

  function {:opaque} writeBookkeepingNoSuccsUpdate(k: Constants, s: Variables, ref: BT.G.Reference)
  : (s': Variables)
  requires WriteAllocConditions(k, s)
  requires ref in s.ephemeralIndirectionTable.graph
  ensures s'.Ready?
  ensures s'.cache == s.cache
  ensures WriteAllocConditions(k, s')
  ensures |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
    lemmaIndirectionTableLocIndexValid(k, s, ref);
    var (eph, oldLoc) := IndirectionTableModel.RemoveLoc(s.ephemeralIndirectionTable, ref);
    var blockAllocator' := if oldLoc.Some?
      then BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / BlockSize())
      else s.blockAllocator;
    var s' := s.(ephemeralIndirectionTable := eph)
     .(lru := LruModel.Use(s.lru, ref))
     .(blockAllocator := blockAllocator');

    freeIndirectionTableLocCorrect(k, s, s', ref,
      if oldLoc.Some?
      then Some(oldLoc.value.addr as int / BlockSize())
      else None);
    reveal_ConsistentBitmap();

    s'
  }


  function {:opaque} allocBookkeeping(k: Constants, s: Variables, children: Option<seq<BT.G.Reference>>)
  : (p: (Variables, Option<Reference>))
  requires WriteAllocConditions(k, s)
  requires ChildrenConditions(k, s, children)
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()

  ensures var (s', id) := p;
    && s'.Ready?
    && WriteAllocConditions(k, s')
    && |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
    var ref := getFreeRef(s);
    if ref.Some? then (
      (writeBookkeeping(k, s, ref.value, children), ref)
    ) else (
      (s, None)
    )
  }

  // fullWrite and fullAlloc are like writeBookkeeping/allocBookkeeping, except that fullWrite and fullAlloc update
  // the cache with the node. In the implementation of betree operations we use the above,
  // because it turns out to be easier to do the cache updates separately. However, for the proofs
  // it is easier to use the below.

  function writeWithNode(k: Constants, s: Variables, ref: BT.G.Reference, node: Node)
  : (s': Variables)
  requires WriteAllocConditions(k, s)
  requires ChildrenConditions(k, s, node.children)
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  ensures WriteAllocConditions(k, s')
  ensures |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
    lemmaIndirectionTableLocIndexValid(k, s, ref);
    var (eph, oldLoc) := IndirectionTableModel.UpdateAndRemoveLoc(s.ephemeralIndirectionTable, ref,
        (if node.children.Some? then node.children.value else []));
    var blockAllocator' := if oldLoc.Some?
      then BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / BlockSize())
      else s.blockAllocator;
    var s' := s.(ephemeralIndirectionTable := eph).(cache := s.cache[ref := node])
        .(lru := LruModel.Use(s.lru, ref))
        .(blockAllocator := blockAllocator');

    freeIndirectionTableLocCorrect(k, s, s', ref,
      if oldLoc.Some?
      then Some(oldLoc.value.addr as int / BlockSize())
      else None);
    reveal_ConsistentBitmap();

    s'
  }

  function allocWithNode(k: Constants, s: Variables, node: Node)
  : (p: (Variables, Option<Reference>))
  requires WriteAllocConditions(k, s)
  requires ChildrenConditions(k, s, node.children)
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  ensures var (s', id) := p;
      && WriteAllocConditions(k, s')
      && |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
    var ref := getFreeRef(s);
    if ref.Some? then (
      (writeWithNode(k, s, ref.value, node), ref)
    ) else (
      (s, None)
    )
  }

  lemma freeIndirectionTableLocCorrect(
      k: Constants, s: Variables, s': Variables, ref: BT.G.Reference, j: Option<int>)
  requires WriteAllocConditions(k, s)
  requires s'.Ready?
  requires forall r | r != ref ::
      MapsAgreeOnKey(
          IIndirectionTable(s.ephemeralIndirectionTable).locs,
          IIndirectionTable(s'.ephemeralIndirectionTable).locs,
          r)
  requires ref !in IIndirectionTable(s'.ephemeralIndirectionTable).locs
  requires j.Some? ==> 0 <= j.value < NumBlocks()
  requires j.Some? ==> ref in IIndirectionTable(s.ephemeralIndirectionTable).locs
  requires j.Some? ==> IIndirectionTable(s.ephemeralIndirectionTable).locs[ref].addr as int == j.value * BlockSize()
  requires j.Some? ==> s'.blockAllocator == BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, j.value)
  requires j.None? ==> s'.blockAllocator == s.blockAllocator
  requires j.None? ==> ref !in IIndirectionTable(s.ephemeralIndirectionTable).locs
  ensures (forall i: int :: IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable, i)
      <==> IsLocAllocBitmap(s'.blockAllocator.ephemeral, i))
  ensures BlockAllocatorModel.Inv(s'.blockAllocator)
  ensures BC.AllLocationsForDifferentRefsDontOverlap(
        IIndirectionTable(s'.ephemeralIndirectionTable))
  ensures (forall loc |
        loc in IIndirectionTable(s'.ephemeralIndirectionTable).locs.Values :: 
          BC.ValidLocationForNode(loc))
  {
    reveal_ConsistentBitmap();
    Bitmap.reveal_IsSet();
    Bitmap.reveal_BitUnset();
    lemmaIndirectionTableLocIndexValid(k, s, ref);

    forall r1, r2 | r1 in IIndirectionTable(s'.ephemeralIndirectionTable).locs && r2 in IIndirectionTable(s'.ephemeralIndirectionTable).locs
    ensures BC.LocationsForDifferentRefsDontOverlap(IIndirectionTable(s'.ephemeralIndirectionTable), r1, r2)
    {
      assert MapsAgreeOnKey( IIndirectionTable(s.ephemeralIndirectionTable).locs, IIndirectionTable(s'.ephemeralIndirectionTable).locs, r1);
      assert MapsAgreeOnKey( IIndirectionTable(s.ephemeralIndirectionTable).locs, IIndirectionTable(s'.ephemeralIndirectionTable).locs, r2);
    }

    forall loc | loc in IIndirectionTable(s'.ephemeralIndirectionTable).locs.Values
    ensures BC.ValidLocationForNode(loc)
    {
      var r :| r in IIndirectionTable(s'.ephemeralIndirectionTable).locs && IIndirectionTable(s'.ephemeralIndirectionTable).locs[r] == loc;
      assert MapsAgreeOnKey(IIndirectionTable(s.ephemeralIndirectionTable).locs, IIndirectionTable(s'.ephemeralIndirectionTable).locs, r);
    }

    if j.Some? {
      assert BC.ValidLocationForNode(IIndirectionTable(s.ephemeralIndirectionTable).locs[ref]);
    }

    forall i: int
    | IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable, i)
    ensures IsLocAllocBitmap(s'.blockAllocator.ephemeral, i)
    {
      if j.Some? && i == j.value {
        if i == 0 {
          assert false;
        } else {
          var r :| r in s'.ephemeralIndirectionTable.locs &&
              s'.ephemeralIndirectionTable.locs[r].addr as int == i * BlockSize() as int;
          assert MapsAgreeOnKey(
            IIndirectionTable(s.ephemeralIndirectionTable).locs,
            IIndirectionTable(s'.ephemeralIndirectionTable).locs, r);

          assert BC.LocationsForDifferentRefsDontOverlap(IIndirectionTable(s.ephemeralIndirectionTable), ref, r);

          assert ref !in IIndirectionTable(s'.ephemeralIndirectionTable).locs;
          assert r in IIndirectionTable(s'.ephemeralIndirectionTable).locs;
          assert IIndirectionTable(s.ephemeralIndirectionTable).locs[r]
              == IIndirectionTable(s.ephemeralIndirectionTable).locs[ref];
          assert r == ref;

          assert false;
        }
      } else {
        if i == 0 {
          assert IsLocAllocIndirectionTable(s.ephemeralIndirectionTable, i);
          assert IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
          assert IsLocAllocBitmap(s'.blockAllocator.ephemeral, i);
        } else {
          var r :| r in s'.ephemeralIndirectionTable.locs &&
              s'.ephemeralIndirectionTable.locs[r].addr as int == i * BlockSize() as int;
          //assert r != ref;
          assert MapsAgreeOnKey(
            IIndirectionTable(s.ephemeralIndirectionTable).locs,
            IIndirectionTable(s'.ephemeralIndirectionTable).locs, r);
          //assert r in IIndirectionTable(s'.ephemeralIndirectionTable).locs;
          //assert r in IIndirectionTable(s.ephemeralIndirectionTable).locs;
          //assert r in s.ephemeralIndirectionTable.contents;
          //assert s.ephemeralIndirectionTable.contents[r].0.Some?;
          //assert s.ephemeralIndirectionTable.contents[r].0.value.addr as int == i * BlockSize() as int;
          assert IsLocAllocIndirectionTable(s.ephemeralIndirectionTable, i);
          assert IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
          assert IsLocAllocBitmap(s'.blockAllocator.ephemeral, i);
        }
      }
    }

    forall i: int
    | IsLocAllocBitmap(s'.blockAllocator.ephemeral, i)
    ensures IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable, i)
    {
      if j.Some? && i == j.value {
        assert IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable, i);
      } else {
        assert IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
        assert IsLocAllocIndirectionTable(s.ephemeralIndirectionTable, i);
        if i == 0 {
          assert IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable, i);
        } else {
          var r :| r in s.ephemeralIndirectionTable.locs &&
            s.ephemeralIndirectionTable.locs[r].addr as int == i * BlockSize() as int;
          assert MapsAgreeOnKey(
            IIndirectionTable(s.ephemeralIndirectionTable).locs,
            IIndirectionTable(s'.ephemeralIndirectionTable).locs, r);
          assert r in s'.ephemeralIndirectionTable.locs &&
            s'.ephemeralIndirectionTable.locs[r].addr as int == i * BlockSize() as int;
          assert IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable, i);
        }
      }
    }

    if j.Some? {
      forall i | 0 <= i < NumBlocks()
      ensures Bitmap.IsSet(s'.blockAllocator.full, i) == (
        || Bitmap.IsSet(s'.blockAllocator.ephemeral, i)
        || (s'.blockAllocator.frozen.Some? && Bitmap.IsSet(s'.blockAllocator.frozen.value, i))
        || Bitmap.IsSet(s'.blockAllocator.persistent, i)
        || Bitmap.IsSet(s'.blockAllocator.full, i)
      )
      {
        if i == j.value {
        } else {
          assert Bitmap.IsSet(s'.blockAllocator.full, i) == Bitmap.IsSet(s.blockAllocator.full, i);
          assert Bitmap.IsSet(s'.blockAllocator.ephemeral, i) == Bitmap.IsSet(s.blockAllocator.ephemeral, i);
          assert s'.blockAllocator.frozen.Some? ==> Bitmap.IsSet(s'.blockAllocator.frozen.value, i) == Bitmap.IsSet(s.blockAllocator.frozen.value, i);
          assert Bitmap.IsSet(s'.blockAllocator.persistent, i) == Bitmap.IsSet(s.blockAllocator.persistent, i);
          assert Bitmap.IsSet(s'.blockAllocator.outstanding, i) == Bitmap.IsSet(s.blockAllocator.outstanding, i);
        }
      }
    } else {
    }
  }

  lemma writeBookkeepingBitmapCorrect(k: Constants, s: Variables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  requires WriteAllocConditions(k, s)
  requires ChildrenConditions(k, s, children)
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  ensures var s' := writeBookkeeping(k, s, ref, children);
    && WriteAllocConditions(k, s')
  {
    /*reveal_writeBookkeeping();
    var s' := writeBookkeeping(k, s, ref, children);

    lemmaIndirectionTableLocIndexValid(k, s, ref);
    assume s.ephemeralIndirectionTable.count as nat < 0x10000000000000000 / 8;
    var (eph, oldEntry) := MutableMapModel.InsertAndGetOld(s.ephemeralIndirectionTable, ref,
        (None, if children.Some? then children.value else []));

    var j := if oldEntry.Some? && oldEntry.value.0.Some? then
      Some(oldEntry.value.0.value.addr as int / BlockSize())
    else
      None;
    freeIndirectionTableLocCorrect(k, s, s', ref, j);
    reveal_ConsistentBitmap();*/
  }

  lemma allocCorrect(k: Constants, s: Variables, node: Node)
  requires WFVars(s)
  requires WriteAllocConditions(k, s)
  requires BC.BlockPointsToValidReferences(INode(node), IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires TotalCacheSize(s) <= MaxCacheSize() - 1
  requires WFNode(node)
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  ensures var (s', ref) := allocWithNode(k, s, node);
    && WFVars(s')
    && (ref.Some? ==> BC.Alloc(Ik(k), IVars(s), IVars(s'), ref.value, INode(node)))
    && (ref.None? ==> s' == s)
    && (ref.Some? ==> TotalCacheSize(s') == TotalCacheSize(s) + 1)
    && WriteAllocConditions(k, s')
  {
    var ref := getFreeRef(s);
    if ref.Some? {
      lemmaIndirectionTableLocIndexValid(k, s, ref.value);
      LruModel.LruUse(s.lru, ref.value);
      writeBookkeepingBitmapCorrect(k, s, ref.value, node.children);
      reveal_writeBookkeeping();

      var (s', ref0) := allocWithNode(k, s, node);
    }
  }
  
  lemma writeCorrect(k: Constants, s: Variables, ref: BT.G.Reference, node: Node)
  requires s.Ready?
  requires WFVars(s)
  requires WriteAllocConditions(k, s)
  requires ref in IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in s.cache
  requires WFNode(node)
  requires BC.BlockPointsToValidReferences(INode(node), IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value.graph ==> ref in s.frozenIndirectionTable.value.locs
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  ensures var s' := writeWithNode(k, s, ref, node);
    && WFVars(s')
    && BC.Dirty(Ik(k), IVars(s), IVars(s'), ref, INode(node))
    && TotalCacheSize(s') == TotalCacheSize(s)
    && WriteAllocConditions(k, s')
  {
    lemmaIndirectionTableLocIndexValid(k, s, ref);
    WeightBucketEmpty();

    LruModel.LruUse(s.lru, ref);

    writeBookkeepingBitmapCorrect(k, s, ref, node.children);
    reveal_writeBookkeeping();

    var s' := writeWithNode(k, s, ref, node);
    assert WFVars(s');
  }
 
  lemma writeNewRefIsAlloc(k: Constants, s: Variables, ref: BT.G.Reference, node: Node)
  requires s.Ready?
  requires WFVars(s)
  requires WriteAllocConditions(k, s)
  requires RefAvailable(s, ref)
  requires WFNode(node)
  requires TotalCacheSize(s) <= MaxCacheSize() - 1
  requires BC.BlockPointsToValidReferences(INode(node), IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  ensures var s' := writeWithNode(k, s, ref, node);
    && WFVars(s')
    && BC.Alloc(Ik(k), IVars(s), IVars(s'), ref, INode(node))
    && TotalCacheSize(s') == TotalCacheSize(s) + 1
    && WriteAllocConditions(k, s')
  {
    LruModel.LruUse(s.lru, ref);

    writeBookkeepingBitmapCorrect(k, s, ref, node.children);
    reveal_writeBookkeeping();
  }

  lemma lemmaChildInGraph(k: Constants, s: Variables, ref: BT.G.Reference, childref: BT.G.Reference)
  requires s.Ready?
  requires Inv(k, s)
  requires ref in s.cache
  requires ref in s.ephemeralIndirectionTable.graph
  requires childref in BT.G.Successors(INode(s.cache[ref]))
  ensures childref in s.ephemeralIndirectionTable.graph
  {
    assert childref in IIndirectionTable(s.ephemeralIndirectionTable).graph[ref];
  }

  lemma lemmaGraphChildInGraph(k: Constants, s: Variables, ref: BT.G.Reference, childref: BT.G.Reference)
  requires s.Ready?
  requires Inv(k, s)
  requires ref in s.ephemeralIndirectionTable.graph
  requires childref in s.ephemeralIndirectionTable.graph[ref]
  ensures childref in s.ephemeralIndirectionTable.graph

  lemma lemmaBlockPointsToValidReferences(k: Constants, s: Variables, ref: BT.G.Reference)
  requires Inv(k, s)
  requires s.Ready?
  requires ref in s.cache
  requires ref in s.ephemeralIndirectionTable.graph
  ensures BC.BlockPointsToValidReferences(INode(s.cache[ref]), IIndirectionTable(s.ephemeralIndirectionTable).graph);
  {
    var node := INode(s.cache[ref]);
    var graph := IIndirectionTable(s.ephemeralIndirectionTable).graph;
    forall r | r in BT.G.Successors(node) ensures r in graph
    {
      lemmaChildInGraph(k, s, ref, r);
    }
  }

  lemma getFreeRefDoesntEqual(s: Variables, ref: BT.G.Reference)
  requires s.Ready?
  requires ref in s.cache
  ensures getFreeRef(s) != Some(ref)

  lemma getFreeRef2DoesntEqual(s: Variables, avoid: BT.G.Reference, ref: BT.G.Reference)
  requires s.Ready?
  requires ref in s.cache
  ensures getFreeRef2(s, avoid) != Some(ref)

  lemma lemmaChildrenConditionsOfNode(
      k: Constants, s: Variables, ref: BT.G.Reference)
  requires s.Ready?
  requires Inv(k, s)
  requires ref in s.cache
  requires ref in s.ephemeralIndirectionTable.graph
  ensures ChildrenConditions(k, s, s.cache[ref].children)
  {
    if s.cache[ref].children.Some? {
      forall r | r in s.cache[ref].children.value
      ensures r in s.ephemeralIndirectionTable.graph
      {
        // Trigger the forall in CacheConsistentWithSuccessors
        assert r in BT.G.Successors(INode(s.cache[ref]));
        assert r in s.ephemeralIndirectionTable.graph[ref];
      }
    }
  }

  lemma lemmaChildrenConditionsSingleOfAllocBookkeeping(
      k: Constants, s: Variables, children: Option<seq<BT.G.Reference>>)
  requires WriteAllocConditions(k, s)
  requires ChildrenConditions(k, s, children)
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  ensures var (s1, newref) := allocBookkeeping(k, s, children);
    newref.Some? ==> ChildrenConditions(k, s1, Some([newref.value]))
  {
    reveal_allocBookkeeping();
    reveal_writeBookkeeping();
    //assert newref.value in s1.ephemeralIndirectionTable.graph;
  }

  lemma lemmaChildrenConditionsUpdateOfAllocBookkeeping(
      k: Constants, s: Variables, children: Option<seq<BT.G.Reference>>,
          children1: seq<BT.G.Reference>, i: int)
  requires WriteAllocConditions(k, s)
  requires ChildrenConditions(k, s, children)
  requires ChildrenConditions(k, s, Some(children1))
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  requires 0 <= i < |children1|
  ensures var (s1, newref) := allocBookkeeping(k, s, children);
    newref.Some? ==> ChildrenConditions(k, s1, Some(children1[i := newref.value]))
  {
    reveal_allocBookkeeping();
    reveal_writeBookkeeping();
  }

  lemma lemmaChildrenConditionsPreservedWriteBookkeeping(
      k: Constants, s: Variables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>,
      children1: Option<seq<BT.G.Reference>>)
  requires WriteAllocConditions(k, s)
  requires ChildrenConditions(k, s, children)
  requires ChildrenConditions(k, s, children1)
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  ensures var s1 := writeBookkeeping(k, s, ref, children);
    ChildrenConditions(k, s1, children1)
  {
    reveal_writeBookkeeping();
  }

  lemma lemmaChildrenConditionsOfReplace1With2(
      k: Constants, s: Variables,
      children: seq<BT.G.Reference>,
      i: int, a: BT.G.Reference, b: BT.G.Reference)
  requires s.Ready?
  requires ChildrenConditions(k, s, Some(children))
  requires a in s.ephemeralIndirectionTable.graph
  requires b in s.ephemeralIndirectionTable.graph
  requires 0 <= i < |children|
  requires |children| < MaxNumChildren()
  ensures ChildrenConditions(k, s, Some(replace1with2(children, a, b, i)))
  {
    reveal_replace1with2();
  }

  lemma lemmaRefInGraphOfWriteBookkeeping(k: Constants, s: Variables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  requires WriteAllocConditions(k, s)
  requires ChildrenConditions(k, s, children)
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  ensures var s1 := writeBookkeeping(k, s, ref, children);
    ref in s1.ephemeralIndirectionTable.graph
  {
    reveal_writeBookkeeping();
  }

  lemma lemmaRefInGraphPreservedWriteBookkeeping(k: Constants, s: Variables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>, ref2: BT.G.Reference)
  requires WriteAllocConditions(k, s)
  requires ChildrenConditions(k, s, children)
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  requires ref2 in s.ephemeralIndirectionTable.graph
  ensures var s1 := writeBookkeeping(k, s, ref, children);
    ref2 in s1.ephemeralIndirectionTable.graph
  {
    reveal_writeBookkeeping();
  }
}
