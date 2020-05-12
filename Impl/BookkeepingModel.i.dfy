include "StateModel.i.dfy"
include "IOModel.i.dfy"
include "../lib/Base/Sets.i.dfy"

module BookkeepingModel { 
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
  requires IndirectionTableModel.Inv(s.ephemeralIndirectionTable)
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
  requires IndirectionTableModel.Inv(s.ephemeralIndirectionTable)
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  {
    var i := IndirectionTableModel.getRefUpperBound(
      s.ephemeralIndirectionTable);
    if i == 0xffff_ffff_ffff_ffff then (
      None
    ) else (
      getFreeRefIterate(s, i+1)
    )
  }

  function getFreeRef2Iterate(s: BCVariables, avoid: BT.G.Reference, i: uint64) 
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
  requires IndirectionTableModel.Inv(s.ephemeralIndirectionTable)
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
  requires IndirectionTableModel.Inv(s.ephemeralIndirectionTable)
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  ensures ref.Some? ==> ref.value != avoid
  {
    var i := IndirectionTableModel.getRefUpperBound(
      s.ephemeralIndirectionTable);
    if i == 0xffff_ffff_ffff_ffff then (
      None
    ) else (
      getFreeRef2Iterate(s, avoid, i+1)
    )
  }

  // Conditions that will hold intermediately between writes and allocs
  predicate WriteAllocConditions(k: Constants, s: BCVariables)
  {
    && s.Ready?
    && IndirectionTableModel.Inv(s.ephemeralIndirectionTable)
    && IndirectionTableModel.TrackingGarbage(s.ephemeralIndirectionTable)
    && (forall loc |
        loc in IIndirectionTable(s.ephemeralIndirectionTable).locs.Values :: 
          DiskLayout.ValidNodeLocation(loc))
    && ConsistentBitmap(s.ephemeralIndirectionTable, s.frozenIndirectionTable,
        s.persistentIndirectionTable, s.outstandingBlockWrites, s.blockAllocator)
    && BlockAllocatorModel.Inv(s.blockAllocator)
    && BC.AllLocationsForDifferentRefsDontOverlap(
        IIndirectionTable(s.ephemeralIndirectionTable))
  }

  predicate ChildrenConditions(k: Constants, s: BCVariables, succs: Option<seq<BT.G.Reference>>)
  requires s.Ready?
  {
    succs.Some? ==> (
      && |succs.value| <= MaxNumChildren()
      && IndirectionTableModel.SuccsValid(succs.value, s.ephemeralIndirectionTable.graph)
    )
  }

  lemma lemmaIndirectionTableLocIndexValid(k: Constants, s: BCVariables, ref: BT.G.Reference)
  requires WriteAllocConditions(k, s)
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
      assert IIndirectionTable(s.ephemeralIndirectionTable).locs[ref] == loc;
      assert loc in IIndirectionTable(s.ephemeralIndirectionTable).locs.Values;
      assert DiskLayout.ValidNodeLocation(loc);
      DiskLayout.reveal_ValidNodeAddr();
      assert i * NodeBlockSize() == loc.addr as int;
      assert IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
    }
  }

  // Bookkeeping only - we update the cache with the Node separately.
  // This turns out to be easier to do.

  function {:opaque} writeBookkeeping(k: Constants, s: BCVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  : (s': BCVariables)
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
      then BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / NodeBlockSize())
      else s.blockAllocator;
    var s' := s.(ephemeralIndirectionTable := eph)
     .(lru := LruModel.Use(s.lru, ref))
     .(blockAllocator := blockAllocator');

    freeIndirectionTableLocCorrect(k, s, s', ref,
      if oldLoc.Some?
      then Some(oldLoc.value.addr as int / NodeBlockSize())
      else None);
    reveal_ConsistentBitmap();

    s'
  }

  function {:opaque} writeBookkeepingNoSuccsUpdate(k: Constants, s: BCVariables, ref: BT.G.Reference)
  : (s': BCVariables)
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
      then BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / NodeBlockSize())
      else s.blockAllocator;
    var s' := s.(ephemeralIndirectionTable := eph)
     .(lru := LruModel.Use(s.lru, ref))
     .(blockAllocator := blockAllocator');

    freeIndirectionTableLocCorrect(k, s, s', ref,
      if oldLoc.Some?
      then Some(oldLoc.value.addr as int / NodeBlockSize())
      else None);
    reveal_ConsistentBitmap();

    s'
  }


  function {:opaque} allocBookkeeping(k: Constants, s: BCVariables, children: Option<seq<BT.G.Reference>>)
  : (p: (BCVariables, Option<Reference>))
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

  function writeWithNode(k: Constants, s: BCVariables, ref: BT.G.Reference, node: Node)
  : (s': BCVariables)
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
      then BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator, oldLoc.value.addr as int / NodeBlockSize())
      else s.blockAllocator;
    var s' := s.(ephemeralIndirectionTable := eph).(cache := s.cache[ref := node])
        .(lru := LruModel.Use(s.lru, ref))
        .(blockAllocator := blockAllocator');

    freeIndirectionTableLocCorrect(k, s, s', ref,
      if oldLoc.Some?
      then Some(oldLoc.value.addr as int / NodeBlockSize())
      else None);
    reveal_ConsistentBitmap();

    s'
  }

  function allocWithNode(k: Constants, s: BCVariables, node: Node)
  : (p: (BCVariables, Option<Reference>))
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
      k: Constants, s: BCVariables, s': BCVariables, ref: BT.G.Reference, j: Option<int>)
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
  requires j.Some? ==> IIndirectionTable(s.ephemeralIndirectionTable).locs[ref].addr as int == j.value * NodeBlockSize()
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
          DiskLayout.ValidNodeLocation(loc))
  {
    reveal_ConsistentBitmap();
    BitmapModel.reveal_IsSet();
    BitmapModel.reveal_BitUnset();
    lemmaIndirectionTableLocIndexValid(k, s, ref);

    forall r1, r2 | r1 in IIndirectionTable(s'.ephemeralIndirectionTable).locs && r2 in IIndirectionTable(s'.ephemeralIndirectionTable).locs
    ensures BC.LocationsForDifferentRefsDontOverlap(IIndirectionTable(s'.ephemeralIndirectionTable), r1, r2)
    {
      assert MapsAgreeOnKey( IIndirectionTable(s.ephemeralIndirectionTable).locs, IIndirectionTable(s'.ephemeralIndirectionTable).locs, r1);
      assert MapsAgreeOnKey( IIndirectionTable(s.ephemeralIndirectionTable).locs, IIndirectionTable(s'.ephemeralIndirectionTable).locs, r2);
    }

    forall loc | loc in IIndirectionTable(s'.ephemeralIndirectionTable).locs.Values
    ensures DiskLayout.ValidNodeLocation(loc)
    {
      var r :| r in IIndirectionTable(s'.ephemeralIndirectionTable).locs && IIndirectionTable(s'.ephemeralIndirectionTable).locs[r] == loc;
      assert MapsAgreeOnKey(IIndirectionTable(s.ephemeralIndirectionTable).locs, IIndirectionTable(s'.ephemeralIndirectionTable).locs, r);
    }

    if j.Some? {
      assert DiskLayout.ValidNodeLocation(IIndirectionTable(s.ephemeralIndirectionTable).locs[ref]);
      assert j.value >= MinNodeBlockIndex() by {
        DiskLayout.reveal_ValidNodeAddr();
      }
    }

    forall i: int
    | IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable, i)
    ensures IsLocAllocBitmap(s'.blockAllocator.ephemeral, i)
    {
      if j.Some? && i == j.value {
        if 0 <= i < MinNodeBlockIndex() {
          assert false;
        } else {
          var r :| r in s'.ephemeralIndirectionTable.locs &&
              s'.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
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
        if 0 <= i < MinNodeBlockIndex() {
          assert IsLocAllocIndirectionTable(s.ephemeralIndirectionTable, i);
          assert IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
          assert IsLocAllocBitmap(s'.blockAllocator.ephemeral, i);
        } else {
          var r :| r in s'.ephemeralIndirectionTable.locs &&
              s'.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          //assert r != ref;
          assert MapsAgreeOnKey(
            IIndirectionTable(s.ephemeralIndirectionTable).locs,
            IIndirectionTable(s'.ephemeralIndirectionTable).locs, r);
          //assert r in IIndirectionTable(s'.ephemeralIndirectionTable).locs;
          //assert r in IIndirectionTable(s.ephemeralIndirectionTable).locs;
          //assert r in s.ephemeralIndirectionTable.contents;
          //assert s.ephemeralIndirectionTable.contents[r].0.Some?;
          //assert s.ephemeralIndirectionTable.contents[r].0.value.addr as int == i * NodeBlockSize() as int;
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
        if 0 <= i < MinNodeBlockIndex() {
          assert IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable, i);
        } else {
          var r :| r in s.ephemeralIndirectionTable.locs &&
            s.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          assert MapsAgreeOnKey(
            IIndirectionTable(s.ephemeralIndirectionTable).locs,
            IIndirectionTable(s'.ephemeralIndirectionTable).locs, r);
          assert r in s'.ephemeralIndirectionTable.locs &&
            s'.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          assert IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable, i);
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

  lemma writeBookkeepingBitmapCorrect(k: Constants, s: BCVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  requires WriteAllocConditions(k, s)
  requires ChildrenConditions(k, s, children)
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  ensures var s' := writeBookkeeping(k, s, ref, children);
    && WriteAllocConditions(k, s')
  {
    /*reveal_writeBookkeeping();
    var s' := writeBookkeeping(k, s, ref, children);

    lemmaIndirectionTableLocIndexValid(k, s, ref);
    assert s.ephemeralIndirectionTable.count as nat < 0x10000000000000000 / 8;
    var (eph, oldEntry) := MutableMapModel.InsertAndGetOld(s.ephemeralIndirectionTable, ref,
        (None, if children.Some? then children.value else []));

    var j := if oldEntry.Some? && oldEntry.value.0.Some? then
      Some(oldEntry.value.0.value.addr as int / NodeBlockSize())
    else
      None;
    freeIndirectionTableLocCorrect(k, s, s', ref, j);
    reveal_ConsistentBitmap();*/
  }

  lemma allocCorrect(k: Constants, s: BCVariables, node: Node)
  requires WFBCVars(s)
  requires WriteAllocConditions(k, s)
  requires BC.BlockPointsToValidReferences(INode(node), IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires TotalCacheSize(s) <= MaxCacheSize() - 1
  requires WFNode(node)
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  ensures var (s', ref) := allocWithNode(k, s, node);
    && WFBCVars(s')
    && (ref.Some? ==> BC.Alloc(Ik(k).bc, IBlockCache(s), IBlockCache(s'), ref.value, INode(node)))
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
  
  lemma writeCorrect(k: Constants, s: BCVariables, ref: BT.G.Reference, node: Node)
  requires s.Ready?
  requires WFBCVars(s)
  requires WriteAllocConditions(k, s)
  requires ref in IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in s.cache
  requires WFNode(node)
  requires BC.BlockPointsToValidReferences(INode(node), IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value.graph ==> ref in s.frozenIndirectionTable.value.locs
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  ensures var s' := writeWithNode(k, s, ref, node);
    && WFBCVars(s')
    && BC.Dirty(Ik(k).bc, IBlockCache(s), IBlockCache(s'), ref, INode(node))
    && TotalCacheSize(s') == TotalCacheSize(s)
    && WriteAllocConditions(k, s')
  {
    lemmaIndirectionTableLocIndexValid(k, s, ref);
    WeightBucketEmpty();

    LruModel.LruUse(s.lru, ref);

    writeBookkeepingBitmapCorrect(k, s, ref, node.children);
    reveal_writeBookkeeping();

    var s' := writeWithNode(k, s, ref, node);
    assert WFBCVars(s');
  }
 
  lemma writeNewRefIsAlloc(k: Constants, s: BCVariables, ref: BT.G.Reference, node: Node)
  requires s.Ready?
  requires WFBCVars(s)
  requires WriteAllocConditions(k, s)
  requires RefAvailable(s, ref)
  requires WFNode(node)
  requires TotalCacheSize(s) <= MaxCacheSize() - 1
  requires BC.BlockPointsToValidReferences(INode(node), IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  ensures var s' := writeWithNode(k, s, ref, node);
    && WFBCVars(s')
    && BC.Alloc(Ik(k).bc, IBlockCache(s), IBlockCache(s'), ref, INode(node))
    && TotalCacheSize(s') == TotalCacheSize(s) + 1
    && WriteAllocConditions(k, s')
  {
    LruModel.LruUse(s.lru, ref);

    writeBookkeepingBitmapCorrect(k, s, ref, node.children);
    reveal_writeBookkeeping();
  }

  lemma lemmaChildInGraph(k: Constants, s: BCVariables, ref: BT.G.Reference, childref: BT.G.Reference)
  requires s.Ready?
  requires BCInv(k, s)
  requires ref in s.cache
  requires ref in s.ephemeralIndirectionTable.graph
  requires childref in BT.G.Successors(INode(s.cache[ref]))
  ensures childref in s.ephemeralIndirectionTable.graph
  {
    assert childref in IIndirectionTable(s.ephemeralIndirectionTable).graph[ref];
  }

  lemma lemmaBlockPointsToValidReferences(k: Constants, s: BCVariables, ref: BT.G.Reference)
  requires BCInv(k, s)
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

  lemma getFreeRefIterateDoesntEqual(s: BCVariables, i: uint64, ref: BT.G.Reference)
  requires s.Ready?
  requires ref in s.cache
  requires i >= 1
  requires IndirectionTableModel.Inv(s.ephemeralIndirectionTable)
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
  requires IndirectionTableModel.Inv(s.ephemeralIndirectionTable)
  ensures getFreeRef(s) != Some(ref)
  {
    reveal_getFreeRef();
    var i := IndirectionTableModel.getRefUpperBound(
      s.ephemeralIndirectionTable);
    if i == 0xffff_ffff_ffff_ffff {
    } else {
      getFreeRefIterateDoesntEqual(s, i+1, ref);
    }
  }

  lemma getFreeRef2IterateDoesntEqual(s: BCVariables, avoid: BT.G.Reference, i: uint64, ref: BT.G.Reference)
  requires s.Ready?
  requires ref in s.cache
  requires i >= 1
  requires IndirectionTableModel.Inv(s.ephemeralIndirectionTable)
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
  requires IndirectionTableModel.Inv(s.ephemeralIndirectionTable)
  ensures getFreeRef2(s, avoid) != Some(ref)
  {
    reveal_getFreeRef2();
    var i := IndirectionTableModel.getRefUpperBound(
      s.ephemeralIndirectionTable);
    if i == 0xffff_ffff_ffff_ffff {
    } else {
      getFreeRef2IterateDoesntEqual(s, avoid, i+1, ref);
    }
  }

  lemma allocRefDoesntEqual(k: Constants, s: BCVariables, children: Option<seq<BT.G.Reference>>, ref: BT.G.Reference)
  requires allocBookkeeping.requires(k, s, children);
  requires ref in s.cache
  ensures allocBookkeeping(k, s, children).1 != Some(ref)
  {
    reveal_allocBookkeeping();
    getFreeRefDoesntEqual(s, ref);
  }

  lemma lemmaChildrenConditionsOfNode(
      k: Constants, s: BCVariables, ref: BT.G.Reference)
  requires s.Ready?
  requires BCInv(k, s)
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
      k: Constants, s: BCVariables, children: Option<seq<BT.G.Reference>>)
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
      k: Constants, s: BCVariables, children: Option<seq<BT.G.Reference>>,
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
      k: Constants, s: BCVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>,
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
      k: Constants, s: BCVariables,
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

  lemma lemmaRefInGraphOfWriteBookkeeping(k: Constants, s: BCVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  requires WriteAllocConditions(k, s)
  requires ChildrenConditions(k, s, children)
  requires |s.ephemeralIndirectionTable.graph| < IndirectionTableModel.MaxSize()
  ensures var s1 := writeBookkeeping(k, s, ref, children);
    ref in s1.ephemeralIndirectionTable.graph
  {
    reveal_writeBookkeeping();
  }

  lemma lemmaRefInGraphPreservedWriteBookkeeping(k: Constants, s: BCVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>, ref2: BT.G.Reference)
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
