include "StateModel.i.dfy"
include "IOModel.i.dfy"
include "../lib/Base/Sets.i.dfy"

module BookkeepingModel { 
  import IT = IndirectionTable

  import opened StateModel
  import opened IOModel
  import opened DiskOpModel

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketWeights
  import opened Bounds
  import LruModel
  import DiskLayout

  import opened NativeTypes

  predicate RefAvailable(s: BCVariables, ref: Reference)
  {
    && s.Ready?
    && ref !in s.ephemeralIndirectionTable.graph
    && ref !in s.cache 
    && ref != BT.G.Root()
  }

  function getFreeRefIterate(s: BCVariables, i: uint64) 
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
  requires s.ephemeralIndirectionTable.Inv()
  requires i >= 1
  requires forall r | r in s.ephemeralIndirectionTable.graph :: r < i
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  decreases 0x1_0000_0000_0000_0000 - i as int
  {
    // NOTE: we shouldn't even need to do this check with the current
    // setup (because we start i at a value > than anything that has
    // *ever* been in the ephemeralIndirectionTable, which would include
    // anything in the cache. That requires some proof though.
    if i !in s.cache then (
      Some(i)
    ) else if i == 0xffff_ffff_ffff_ffff then (
      None
    ) else (
      getFreeRefIterate(s, i+1) 
    )
  }

  function {:opaque} getFreeRef(s: BCVariables)
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
  requires s.ephemeralIndirectionTable.Inv()
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  {
    var i := s.ephemeralIndirectionTable.getRefUpperBound();
    if i == 0xffff_ffff_ffff_ffff then (
      None
    ) else (
      getFreeRefIterate(s, i+1)
    )
  }

  function getFreeRef2Iterate(s: BCVariables, avoid: BT.G.Reference, i: uint64) 
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
  requires s.ephemeralIndirectionTable.Inv()
  requires i >= 1
  requires forall r | r in s.ephemeralIndirectionTable.graph :: r < i
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  ensures ref.Some? ==> ref.value != avoid
  decreases 0x1_0000_0000_0000_0000 - i as int
  {
    if i != avoid && i !in s.cache then (
      Some(i)
    ) else if i == 0xffff_ffff_ffff_ffff then (
      None
    ) else (
      getFreeRef2Iterate(s, avoid, i+1) 
    )
  }

  function {:opaque} getFreeRef2(s: BCVariables, avoid: BT.G.Reference)
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
  requires s.ephemeralIndirectionTable.Inv()
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  ensures ref.Some? ==> ref.value != avoid
  {
    var i := s.ephemeralIndirectionTable.getRefUpperBound();
    if i == 0xffff_ffff_ffff_ffff then (
      None
    ) else (
      getFreeRef2Iterate(s, avoid, i+1)
    )
  }

  // Conditions that will hold intermediately between writes and allocs
  predicate WriteAllocConditions(s: BCVariables)
  {
    && s.Ready?
    && s.ephemeralIndirectionTable.Inv()
    && s.ephemeralIndirectionTable.TrackingGarbage()
    && (forall loc |
        loc in s.ephemeralIndirectionTable.I().locs.Values :: 
          DiskLayout.ValidNodeLocation(loc))
    && ConsistentBitmap(s.ephemeralIndirectionTable.I(), MapOption(s.frozenIndirectionTable, (x: IndirectionTable) => x.I()),
        s.persistentIndirectionTable.I(), s.outstandingBlockWrites, s.blockAllocator)
    && BlockAllocatorModel.Inv(s.blockAllocator)
    && BC.AllLocationsForDifferentRefsDontOverlap(
        s.ephemeralIndirectionTable.I())
  }

  predicate ChildrenConditions(s: BCVariables, succs: Option<seq<BT.G.Reference>>)
  requires s.Ready?
  {
    succs.Some? ==> (
      && |succs.value| <= MaxNumChildren()
      && IndirectionTable.SuccsValid(succs.value, s.ephemeralIndirectionTable.graph)
    )
  }

  lemma lemmaIndirectionTableLocIndexValid(s: BCVariables, ref: BT.G.Reference)
  requires WriteAllocConditions(s)
  ensures ref in s.ephemeralIndirectionTable.locs ==>
    (
      && 0 <= s.ephemeralIndirectionTable.locs[ref].addr as int / NodeBlockSize() < NumBlocks()
      && (s.ephemeralIndirectionTable.locs[ref].addr as int / NodeBlockSize()) * NodeBlockSize() == s.ephemeralIndirectionTable.locs[ref].addr as int
    )
  {
    if ref in s.ephemeralIndirectionTable.locs {
      reveal_ConsistentBitmap();
      var loc := s.ephemeralIndirectionTable.locs[ref];
      var i := loc.addr as int / NodeBlockSize();
      assert s.ephemeralIndirectionTable.I().locs[ref] == loc;
      assert loc in s.ephemeralIndirectionTable.I().locs.Values;
      assert DiskLayout.ValidNodeLocation(loc);
      DiskLayout.reveal_ValidNodeAddr();
      assert i * NodeBlockSize() == loc.addr as int;
      assert IndirectionTable.IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
    }
  }

  // Bookkeeping only - we update the cache with the Node separately.
  // This turns out to be easier to do.

  function {:opaque} writeBookkeeping(s: BCVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  : (s': BCVariables)
  requires WriteAllocConditions(s)
  requires ChildrenConditions(s, children)
  requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures s'.Ready?
  ensures s'.cache == s.cache
  ensures WriteAllocConditions(s')
  ensures |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
    lemmaIndirectionTableLocIndexValid(s, ref);
    var (eph, oldLoc) := s.ephemeralIndirectionTable.updateAndRemoveLoc(ref,
        (if children.Some? then children.value else []));
    var blockAllocator' := if oldLoc.Some?
      then BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / NodeBlockSize())
      else s.blockAllocator;
    var s' := s.(ephemeralIndirectionTable := eph)
     .(lru := LruModel.Use(s.lru, ref))
     .(blockAllocator := blockAllocator');

    freeIndirectionTableLocCorrect(s, s', ref,
      if oldLoc.Some?
      then Some(oldLoc.value.addr as int / NodeBlockSize())
      else None);
    reveal_ConsistentBitmap();

    s'
  }

  function {:opaque} writeBookkeepingNoSuccsUpdate(s: BCVariables, ref: BT.G.Reference)
  : (s': BCVariables)
  requires WriteAllocConditions(s)
  requires ref in s.ephemeralIndirectionTable.graph
  ensures s'.Ready?
  ensures s'.cache == s.cache
  ensures WriteAllocConditions(s')
  ensures |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
    lemmaIndirectionTableLocIndexValid(s, ref);
    var (eph, oldLoc) := s.ephemeralIndirectionTable.removeLoc(ref);
    var blockAllocator' := if oldLoc.Some?
      then BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / NodeBlockSize())
      else s.blockAllocator;
    var s' := s.(ephemeralIndirectionTable := eph)
     .(lru := LruModel.Use(s.lru, ref))
     .(blockAllocator := blockAllocator');

    freeIndirectionTableLocCorrect(s, s', ref,
      if oldLoc.Some?
      then Some(oldLoc.value.addr as int / NodeBlockSize())
      else None);
    reveal_ConsistentBitmap();

    s'
  }


  function {:opaque} allocBookkeeping(s: BCVariables, children: Option<seq<BT.G.Reference>>)
  : (p: (BCVariables, Option<Reference>))
  requires WriteAllocConditions(s)
  requires ChildrenConditions(s, children)
  requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()

  ensures var (s', id) := p;
    && s'.Ready?
    && WriteAllocConditions(s')
    && |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
    var ref := getFreeRef(s);
    if ref.Some? then (
      (writeBookkeeping(s, ref.value, children), ref)
    ) else (
      (s, None)
    )
  }

  // fullWrite and fullAlloc are like writeBookkeeping/allocBookkeeping, except that fullWrite and fullAlloc update
  // the cache with the node. In the implementation of betree operations we use the above,
  // because it turns out to be easier to do the cache updates separately. However, for the proofs
  // it is easier to use the below.

  function writeWithNode(s: BCVariables, ref: BT.G.Reference, node: Node)
  : (s': BCVariables)
  requires WriteAllocConditions(s)
  requires ChildrenConditions(s, node.children)
  requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures WriteAllocConditions(s')
  ensures |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
    lemmaIndirectionTableLocIndexValid(s, ref);
    var (eph, oldLoc) := s.ephemeralIndirectionTable.updateAndRemoveLoc(ref,
        (if node.children.Some? then node.children.value else []));
    var blockAllocator' := if oldLoc.Some?
      then BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / NodeBlockSize())
      else s.blockAllocator;
    var s' := s.(ephemeralIndirectionTable := eph).(cache := s.cache[ref := node])
        .(lru := LruModel.Use(s.lru, ref))
        .(blockAllocator := blockAllocator');

    freeIndirectionTableLocCorrect(s, s', ref,
      if oldLoc.Some?
      then Some(oldLoc.value.addr as int / NodeBlockSize())
      else None);
    reveal_ConsistentBitmap();

    s'
  }

  function allocWithNode(s: BCVariables, node: Node)
  : (p: (BCVariables, Option<Reference>))
  requires WriteAllocConditions(s)
  requires ChildrenConditions(s, node.children)
  requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures var (s', id) := p;
      && WriteAllocConditions(s')
      && |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
    var ref := getFreeRef(s);
    if ref.Some? then (
      (writeWithNode(s, ref.value, node), ref)
    ) else (
      (s, None)
    )
  }

  lemma freeIndirectionTableLocCorrect(
      s: BCVariables, s': BCVariables, ref: BT.G.Reference, j: Option<int>)
  requires WriteAllocConditions(s)
  requires s'.Ready?
  requires forall r | r != ref ::
      MapsAgreeOnKey(
          s.ephemeralIndirectionTable.I().locs,
          s'.ephemeralIndirectionTable.I().locs,
          r)
  requires ref !in s'.ephemeralIndirectionTable.I().locs
  requires j.Some? ==> 0 <= j.value < NumBlocks()
  requires j.Some? ==> ref in s.ephemeralIndirectionTable.I().locs
  requires j.Some? ==> s.ephemeralIndirectionTable.I().locs[ref].addr as int == j.value * NodeBlockSize()
  requires j.Some? ==> s'.blockAllocator == BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, j.value)
  requires j.None? ==> s'.blockAllocator == s.blockAllocator
  requires j.None? ==> ref !in s.ephemeralIndirectionTable.I().locs
  ensures (forall i: int :: IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i)
      <==> IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.ephemeral, i))
  ensures BlockAllocatorModel.Inv(s'.blockAllocator)
  ensures BC.AllLocationsForDifferentRefsDontOverlap(
        s'.ephemeralIndirectionTable.I())
  ensures (forall loc |
        loc in s'.ephemeralIndirectionTable.I().locs.Values :: 
          DiskLayout.ValidNodeLocation(loc))
  {
    reveal_ConsistentBitmap();
    BitmapModel.reveal_IsSet();
    BitmapModel.reveal_BitUnset();
    lemmaIndirectionTableLocIndexValid(s, ref);

    forall r1, r2 | r1 in s'.ephemeralIndirectionTable.I().locs && r2 in s'.ephemeralIndirectionTable.I().locs
    ensures BC.LocationsForDifferentRefsDontOverlap(s'.ephemeralIndirectionTable.I(), r1, r2)
    {
      assert MapsAgreeOnKey( s.ephemeralIndirectionTable.I().locs, s'.ephemeralIndirectionTable.I().locs, r1);
      assert MapsAgreeOnKey( s.ephemeralIndirectionTable.I().locs, s'.ephemeralIndirectionTable.I().locs, r2);
    }

    forall loc | loc in s'.ephemeralIndirectionTable.I().locs.Values
    ensures DiskLayout.ValidNodeLocation(loc)
    {
      var r :| r in s'.ephemeralIndirectionTable.I().locs && s'.ephemeralIndirectionTable.I().locs[r] == loc;
      assert MapsAgreeOnKey(s.ephemeralIndirectionTable.I().locs, s'.ephemeralIndirectionTable.I().locs, r);
    }

    if j.Some? {
      assert DiskLayout.ValidNodeLocation(s.ephemeralIndirectionTable.I().locs[ref]);
      assert j.value >= MinNodeBlockIndex() by {
        DiskLayout.reveal_ValidNodeAddr();
      }
    }

    forall i: int
    | IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i)
    ensures IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.ephemeral, i)
    {
      if j.Some? && i == j.value {
        if 0 <= i < MinNodeBlockIndex() {
          assert false;
        } else {
          var r :| r in s'.ephemeralIndirectionTable.locs &&
              s'.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          assert MapsAgreeOnKey(
            s.ephemeralIndirectionTable.I().locs,
            s'.ephemeralIndirectionTable.I().locs, r);

          assert BC.LocationsForDifferentRefsDontOverlap(s.ephemeralIndirectionTable.I(), ref, r);

          assert ref !in s'.ephemeralIndirectionTable.I().locs;
          assert r in s'.ephemeralIndirectionTable.I().locs;
          assert s.ephemeralIndirectionTable.I().locs[r]
              == s.ephemeralIndirectionTable.I().locs[ref];
          assert r == ref;

          assert false;
        }
      } else {
        if 0 <= i < MinNodeBlockIndex() {
          assert IndirectionTable.IsLocAllocIndirectionTable(s.ephemeralIndirectionTable.I(), i);
          assert IndirectionTable.IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
          assert IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.ephemeral, i);
        } else {
          var r :| r in s'.ephemeralIndirectionTable.locs &&
              s'.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          assert MapsAgreeOnKey(
            s.ephemeralIndirectionTable.I().locs,
            s'.ephemeralIndirectionTable.I().locs, r);
          assert IndirectionTable.IsLocAllocIndirectionTable(s.ephemeralIndirectionTable.I(), i);
          assert IndirectionTable.IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
          assert IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.ephemeral, i);
        }
      }
    }

    forall i: int
    | IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.ephemeral, i)
    ensures IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i)
    {
      if j.Some? && i == j.value {
        assert IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i);
      } else {
        assert IndirectionTable.IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
        assert IndirectionTable.IsLocAllocIndirectionTable(s.ephemeralIndirectionTable.I(), i);
        if 0 <= i < MinNodeBlockIndex() {
          assert IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i);
        } else {
          var r :| r in s.ephemeralIndirectionTable.locs &&
            s.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          assert MapsAgreeOnKey(
            s.ephemeralIndirectionTable.I().locs,
            s'.ephemeralIndirectionTable.I().locs, r);
          assert r in s'.ephemeralIndirectionTable.locs &&
            s'.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          assert IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i);
        }
      }
    }

    if j.Some? {
      forall i | 0 <= i < NumBlocks()
      ensures BitmapModel.IsSet(s'.blockAllocator.full, i) == (
        || BitmapModel.IsSet(s'.blockAllocator.ephemeral, i)
        || (s'.blockAllocator.frozen.Some? && BitmapModel.IsSet(s'.blockAllocator.frozen.value, i))
        || BitmapModel.IsSet(s'.blockAllocator.persistent, i)
        || BitmapModel.IsSet(s'.blockAllocator.full, i)
      )
      {
        if i == j.value {
        } else {
          assert BitmapModel.IsSet(s'.blockAllocator.full, i) == BitmapModel.IsSet(s.blockAllocator.full, i);
          assert BitmapModel.IsSet(s'.blockAllocator.ephemeral, i) == BitmapModel.IsSet(s.blockAllocator.ephemeral, i);
          assert s'.blockAllocator.frozen.Some? ==> BitmapModel.IsSet(s'.blockAllocator.frozen.value, i) == BitmapModel.IsSet(s.blockAllocator.frozen.value, i);
          assert BitmapModel.IsSet(s'.blockAllocator.persistent, i) == BitmapModel.IsSet(s.blockAllocator.persistent, i);
          assert BitmapModel.IsSet(s'.blockAllocator.outstanding, i) == BitmapModel.IsSet(s.blockAllocator.outstanding, i);
        }
      }
    } else {
    }
  }

  lemma writeBookkeepingBitmapCorrect(s: BCVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  requires WriteAllocConditions(s)
  requires ChildrenConditions(s, children)
  requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures var s' := writeBookkeeping(s, ref, children);
    && WriteAllocConditions(s')
  {
    /*reveal_writeBookkeeping();
    var s' := writeBookkeeping(s, ref, children);

    lemmaIndirectionTableLocIndexValid(s, ref);
    assert s.ephemeralIndirectionTable.count as nat < 0x10000000000000000 / 8;
    var (eph, oldEntry) := MutableMapModel.InsertAndGetOld(s.ephemeralIndirectionTable, ref,
        (None, if children.Some? then children.value else []));

    var j := if oldEntry.Some? && oldEntry.value.0.Some? then
      Some(oldEntry.value.0.value.addr as int / NodeBlockSize())
    else
      None;
    freeIndirectionTableLocCorrect(s, s', ref, j);
    reveal_ConsistentBitmap();*/
  }

  lemma allocCorrect(s: BCVariables, node: Node)
  requires WFBCVars(s)
  requires WriteAllocConditions(s)
  requires BC.BlockPointsToValidReferences(INode(node), s.ephemeralIndirectionTable.I().graph)
  requires TotalCacheSize(s) <= MaxCacheSize() - 1
  requires WFNode(node)
  requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures var (s', ref) := allocWithNode(s, node);
    && WFBCVars(s')
    && (ref.Some? ==> BC.Alloc(IBlockCache(s), IBlockCache(s'), ref.value, INode(node)))
    && (ref.None? ==> s' == s)
    && (ref.Some? ==> TotalCacheSize(s') == TotalCacheSize(s) + 1)
    && WriteAllocConditions(s')
  {
    var ref := getFreeRef(s);
    if ref.Some? {
      lemmaIndirectionTableLocIndexValid(s, ref.value);
      LruModel.LruUse(s.lru, ref.value);
      writeBookkeepingBitmapCorrect(s, ref.value, node.children);
      reveal_writeBookkeeping();

      var s' := writeWithNode(s, ref.value, node);
    }
  }
  
  lemma writeCorrect(s: BCVariables, ref: BT.G.Reference, node: Node)
  requires s.Ready?
  requires WFBCVars(s)
  requires WriteAllocConditions(s)
  requires ref in s.ephemeralIndirectionTable.I().graph
  requires ref in s.cache
  requires WFNode(node)
  requires BC.BlockPointsToValidReferences(INode(node), s.ephemeralIndirectionTable.I().graph)
  requires s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value.graph ==> ref in s.frozenIndirectionTable.value.locs
  requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures var s' := writeWithNode(s, ref, node);
    && WFBCVars(s')
    && BC.Dirty(IBlockCache(s), IBlockCache(s'), ref, INode(node))
    && TotalCacheSize(s') == TotalCacheSize(s)
    && WriteAllocConditions(s')
  {
    lemmaIndirectionTableLocIndexValid(s, ref);
    WeightBucketEmpty();

    LruModel.LruUse(s.lru, ref);

    writeBookkeepingBitmapCorrect(s, ref, node.children);
    reveal_writeBookkeeping();

    var s' := writeWithNode(s, ref, node);
    assert WFBCVars(s');
  }
 
  lemma writeNewRefIsAlloc(s: BCVariables, ref: BT.G.Reference, node: Node)
  requires s.Ready?
  requires WFBCVars(s)
  requires WriteAllocConditions(s)
  requires RefAvailable(s, ref)
  requires WFNode(node)
  requires TotalCacheSize(s) <= MaxCacheSize() - 1
  requires BC.BlockPointsToValidReferences(INode(node), s.ephemeralIndirectionTable.I().graph)
  requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures var s' := writeWithNode(s, ref, node);
    && WFBCVars(s')
    && BC.Alloc(IBlockCache(s), IBlockCache(s'), ref, INode(node))
    && TotalCacheSize(s') == TotalCacheSize(s) + 1
    && WriteAllocConditions(s')
  {
    LruModel.LruUse(s.lru, ref);

    writeBookkeepingBitmapCorrect(s, ref, node.children);
    reveal_writeBookkeeping();
  }

  lemma lemmaChildInGraph(s: BCVariables, ref: BT.G.Reference, childref: BT.G.Reference)
  requires s.Ready?
  requires BCInv(s)
  requires ref in s.cache
  requires ref in s.ephemeralIndirectionTable.graph
  requires childref in BT.G.Successors(INode(s.cache[ref]))
  ensures childref in s.ephemeralIndirectionTable.graph
  {
    assert childref in s.ephemeralIndirectionTable.I().graph[ref];
  }

  lemma lemmaBlockPointsToValidReferences(s: BCVariables, ref: BT.G.Reference)
  requires BCInv(s)
  requires s.Ready?
  requires ref in s.cache
  requires ref in s.ephemeralIndirectionTable.graph
  ensures BC.BlockPointsToValidReferences(INode(s.cache[ref]), s.ephemeralIndirectionTable.I().graph);
  {
    var node := INode(s.cache[ref]);
    var graph := s.ephemeralIndirectionTable.I().graph;
    forall r | r in BT.G.Successors(node) ensures r in graph
    {
      lemmaChildInGraph(s, ref, r);
    }
  }

  lemma getFreeRefIterateDoesntEqual(s: BCVariables, i: uint64, ref: BT.G.Reference)
  requires s.Ready?
  requires ref in s.cache
  requires i >= 1
  requires s.ephemeralIndirectionTable.Inv()
  requires forall r | r in s.ephemeralIndirectionTable.graph :: r < i
  decreases 0x1_0000_0000_0000_0000 - i as int
  ensures getFreeRefIterate(s, i) != Some(ref)
  {
    if i !in s.cache {
    } else if i == 0xffff_ffff_ffff_ffff {
    } else {
      getFreeRefIterateDoesntEqual(s, i+1, ref);
    }
  }

  lemma getFreeRefDoesntEqual(s: BCVariables, ref: BT.G.Reference)
  requires s.Ready?
  requires ref in s.cache
  requires s.ephemeralIndirectionTable.Inv()
  ensures getFreeRef(s) != Some(ref)
  {
    reveal_getFreeRef();
    var i := s.ephemeralIndirectionTable.getRefUpperBound();
    if i == 0xffff_ffff_ffff_ffff {
    } else {
      getFreeRefIterateDoesntEqual(s, i+1, ref);
    }
  }

  lemma getFreeRef2IterateDoesntEqual(s: BCVariables, avoid: BT.G.Reference, i: uint64, ref: BT.G.Reference)
  requires s.Ready?
  requires ref in s.cache
  requires i >= 1
  requires s.ephemeralIndirectionTable.Inv()
  requires forall r | r in s.ephemeralIndirectionTable.graph :: r < i
  ensures getFreeRef2Iterate(s, avoid, i) != Some(ref)
  decreases 0x1_0000_0000_0000_0000 - i as int
  {
    if i != avoid && i !in s.cache {
    } else if i == 0xffff_ffff_ffff_ffff {
    } else {
      getFreeRef2IterateDoesntEqual(s, avoid, i+1, ref);
    }
  }

  lemma getFreeRef2DoesntEqual(s: BCVariables, avoid: BT.G.Reference, ref: BT.G.Reference)
  requires s.Ready?
  requires ref in s.cache
  requires s.ephemeralIndirectionTable.Inv()
  ensures getFreeRef2(s, avoid) != Some(ref)
  {
    reveal_getFreeRef2();
    var i := s.ephemeralIndirectionTable.getRefUpperBound();
    if i == 0xffff_ffff_ffff_ffff {
    } else {
      getFreeRef2IterateDoesntEqual(s, avoid, i+1, ref);
    }
  }

  lemma allocRefDoesntEqual(s: BCVariables, children: Option<seq<BT.G.Reference>>, ref: BT.G.Reference)
  requires allocBookkeeping.requires(s, children);
  requires ref in s.cache
  ensures allocBookkeeping(s, children).1 != Some(ref)
  {
    reveal_allocBookkeeping();
    getFreeRefDoesntEqual(s, ref);
  }

  lemma lemmaChildrenConditionsOfNode(
      s: BCVariables, ref: BT.G.Reference)
  requires s.Ready?
  requires BCInv(s)
  requires ref in s.cache
  requires ref in s.ephemeralIndirectionTable.graph
  ensures ChildrenConditions(s, s.cache[ref].children)
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
      s: BCVariables, children: Option<seq<BT.G.Reference>>)
  requires WriteAllocConditions(s)
  requires ChildrenConditions(s, children)
  requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures var (s1, newref) := allocBookkeeping(s, children);
    newref.Some? ==> ChildrenConditions(s1, Some([newref.value]))
  {
    reveal_allocBookkeeping();
    reveal_writeBookkeeping();
    //assert newref.value in s1.ephemeralIndirectionTable.graph;
  }

  lemma lemmaChildrenConditionsUpdateOfAllocBookkeeping(
      s: BCVariables, children: Option<seq<BT.G.Reference>>,
          children1: seq<BT.G.Reference>, i: int)
  requires WriteAllocConditions(s)
  requires ChildrenConditions(s, children)
  requires ChildrenConditions(s, Some(children1))
  requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  requires 0 <= i < |children1|
  ensures var (s1, newref) := allocBookkeeping(s, children);
    newref.Some? ==> ChildrenConditions(s1, Some(children1[i := newref.value]))
  {
    reveal_allocBookkeeping();
    reveal_writeBookkeeping();
  }

  lemma lemmaChildrenConditionsPreservedWriteBookkeeping(
      s: BCVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>,
      children1: Option<seq<BT.G.Reference>>)
  requires WriteAllocConditions(s)
  requires ChildrenConditions(s, children)
  requires ChildrenConditions(s, children1)
  requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures var s1 := writeBookkeeping(s, ref, children);
    ChildrenConditions(s1, children1)
  {
    reveal_writeBookkeeping();
  }

  lemma lemmaChildrenConditionsOfReplace1With2(
      s: BCVariables,
      children: seq<BT.G.Reference>,
      i: int, a: BT.G.Reference, b: BT.G.Reference)
  requires s.Ready?
  requires ChildrenConditions(s, Some(children))
  requires a in s.ephemeralIndirectionTable.graph
  requires b in s.ephemeralIndirectionTable.graph
  requires 0 <= i < |children|
  requires |children| < MaxNumChildren()
  ensures ChildrenConditions(s, Some(replace1with2(children, a, b, i)))
  {
    reveal_replace1with2();
  }

  lemma lemmaRefInGraphOfWriteBookkeeping(s: BCVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  requires WriteAllocConditions(s)
  requires ChildrenConditions(s, children)
  requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures var s1 := writeBookkeeping(s, ref, children);
    ref in s1.ephemeralIndirectionTable.graph
  {
    reveal_writeBookkeeping();
  }

  lemma lemmaRefInGraphPreservedWriteBookkeeping(s: BCVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>, ref2: BT.G.Reference)
  requires WriteAllocConditions(s)
  requires ChildrenConditions(s, children)
  requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  requires ref2 in s.ephemeralIndirectionTable.graph
  ensures var s1 := writeBookkeeping(s, ref, children);
    ref2 in s1.ephemeralIndirectionTable.graph
  {
    reveal_writeBookkeeping();
  }
}
