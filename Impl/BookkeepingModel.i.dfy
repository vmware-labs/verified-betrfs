include "IOModel.i.dfy"
include "../lib/Base/Sets.i.dfy"

module BookkeepingModel { 
  import IT = IndirectionTable
  import opened StateBCModel
  import opened StateSectorModel
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

  predicate RefAvailable(s: BBC.Variables, ref: Reference)
  {
    && s.Ready?
    && ref !in s.ephemeralIndirectionTable.graph
    // && ref !in s.ephemeralIndirectionTable.locs
    && ref !in s.cache 
    && ref != BT.G.Root()
  }

  function getFreeRefIterate(s: BBC.Variables, i: uint64) 
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
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

  function {:opaque} getFreeRef(s: BBC.Variables)
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
  requires forall r | r in s.ephemeralIndirectionTable.graph :: r <= s.ephemeralIndirectionTable.refUpperBound
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  {
    var i := s.ephemeralIndirectionTable.refUpperBound;
    if i == 0xffff_ffff_ffff_ffff then (
      None
    ) else (
      getFreeRefIterate(s, i+1)
    )
  }

  function getFreeRef2Iterate(s: BBC.Variables, avoid: BT.G.Reference, i: uint64) 
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
  // requires s.ephemeralIndirectionTable.Inv()
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

  function {:opaque} getFreeRef2(s: BBC.Variables, avoid: BT.G.Reference)
  : (ref : Option<BT.G.Reference>)
  requires s.Ready?
  // requires s.ephemeralIndirectionTable.Inv()
  requires forall r | r in s.ephemeralIndirectionTable.graph :: r <= s.ephemeralIndirectionTable.refUpperBound
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  ensures ref.Some? ==> ref.value != avoid
  {
    var i := s.ephemeralIndirectionTable.refUpperBound;
    if i == 0xffff_ffff_ffff_ffff then (
      None
    ) else (
      getFreeRef2Iterate(s, avoid, i+1)
    )
  }

  predicate ChildrenConditions(s: BBC.Variables, succs: Option<seq<BT.G.Reference>>)
  requires s.Ready?
  {
    succs.Some? ==> (
      && |succs.value| <= MaxNumChildren()
      && IT.IndirectionTable.SuccsValid(succs.value, s.ephemeralIndirectionTable.graph)
    )
  }

  lemma lemmaIndirectionTableLocIndexValid(s: BBC.Variables, ref: BT.G.Reference)
  requires s.WriteAllocConditions()
  ensures ref in s.ephemeralIndirectionTable.locs ==>
    (
      // && 0 <= s.ephemeralIndirectionTable.locs[ref].addr as int / NodeBlockSize() < NumBlocks()
      && (s.ephemeralIndirectionTable.locs[ref].addr as int / NodeBlockSize()) * NodeBlockSize() == s.ephemeralIndirectionTable.locs[ref].addr as int
    )
  {
    if ref in s.ephemeralIndirectionTable.locs {
      var loc := s.ephemeralIndirectionTable.locs[ref];
      var i := loc.addr as int / NodeBlockSize();
      assert s.ephemeralIndirectionTable.locs[ref] == loc;
      assert loc in s.ephemeralIndirectionTable.locs.Values;
      assert DiskLayout.ValidNodeLocation(loc);
      DiskLayout.reveal_ValidNodeAddr();
      assert i * NodeBlockSize() == loc.addr as int;
    }
  }

  // Bookkeeping only - we update the cache with the Node separately.
  // This turns out to be easier to do.

  function {:opaque} writeBookkeeping(s: BBC.Variables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  : (s': BBC.Variables)
  requires s.WriteAllocConditions()
  requires ChildrenConditions(s, children)
  // requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures s'.Ready?
  ensures s'.cache == s.cache
  ensures s'.WriteAllocConditions()
  ensures |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
    // lemmaIndirectionTableLocIndexValid(s, ref);
    var succs := if children.Some? then children.value else [];
    // var oldLoc := MapLookupOption(s.ephemeralIndirectionTable.locs, ref);
    // TODO(andreal) s.ephemeralIndirectionTable.updateAndRemoveLoc(ref,
    // TODO(andreal)     (if children.Some? then children.value else []));
    var eph := s.ephemeralIndirectionTable.(
      graph := s.ephemeralIndirectionTable.graph[ref := succs]).
      (locs := MapRemove1(s.ephemeralIndirectionTable.locs, ref)).
      (refUpperBound := if ref > s.ephemeralIndirectionTable.refUpperBound then ref else s.ephemeralIndirectionTable.refUpperBound);

    var s' := s.(ephemeralIndirectionTable := eph);
    s'
  }

  function {:opaque} allocBookkeeping(s: BBC.Variables, children: Option<seq<BT.G.Reference>>)
  : (p: (BBC.Variables, Option<Reference>))
  requires s.WriteAllocConditions()
  requires ChildrenConditions(s, children)

  ensures var (s', id) := p;
    && s'.Ready?
    && s'.WriteAllocConditions()
    && |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
    var ref := getFreeRef(s);
    // var ref: Option<BT.G.Reference> :| ref.Some? ==> RefAvailable(s, ref.value);
    if ref.Some? then (
      (writeBookkeeping(s, ref.value, children), ref)
    ) else (
      (s, None)
    )
  }
/*

  function {:opaque} writeBookkeepingNoSuccsUpdate(s: BCVariables, ref: BT.G.Reference)
  : (s': BCVariables)
  requires s.WriteAllocConditions()
  requires ref in s.ephemeralIndirectionTable.graph
  ensures s'.Ready?
  ensures s'.cache == s.cache
  ensures s'.WriteAllocConditions()
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
*/

  // fullWrite and fullAlloc are like writeBookkeeping/allocBookkeeping, except that fullWrite and fullAlloc update
  // the cache with the node. In the implementation of betree operations we use the above,
  // because it turns out to be easier to do the cache updates separately. However, for the proofs
  // it is easier to use the below.

  function writeWithNode(s: BBC.Variables, ref: BT.G.Reference, node: Node)
  : (s': BBC.Variables)
  requires s.WriteAllocConditions()
  requires ChildrenConditions(s, node.children)
  // requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures s'.WriteAllocConditions()
  ensures |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
    // lemmaIndirectionTableLocIndexValid(s, ref);
    var succs := if node.children.Some? then node.children.value else [];
    // var oldLoc := MapLookupOption(s.ephemeralIndirectionTable.locs, ref);
    // var (eph, oldLoc) := s.ephemeralIndirectionTable.updateAndRemoveLoc(ref,
    //     (if node.children.Some? then node.children.value else []));
    var table := s.ephemeralIndirectionTable;

    var eph := table.
      (graph := table.graph[ref := succs]).
      (locs := MapRemove1(table.locs, ref)).
      (refUpperBound := if ref > table.refUpperBound then ref else table.refUpperBound);

    var s' := s.(ephemeralIndirectionTable := eph).(cache := s.cache[ref := node]);

    assert s'.WriteAllocConditions();
    s'
  }

  function allocWithNode(s: BBC.Variables, node: Node)
  : (p: (BBC.Variables, Option<Reference>))
  requires s.WriteAllocConditions()
  requires ChildrenConditions(s, node.children)
  ensures var (s', id) := p;
      && s'.WriteAllocConditions()
      && |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
    var ref := getFreeRef(s);
    if ref.Some? then (
      (writeWithNode(s, ref.value, node), ref)
    ) else (
      (s, None)
    )
  }
/*

  lemma freeIndirectionTableLocCorrect(
      s: BCVariables, s': BCVariables, ref: BT.G.Reference, j: Option<int>)
  requires s.WriteAllocConditions()
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
  ensures (forall i: int :: IT.IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i)
      <==> IT.IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.ephemeral, i))
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
    | IT.IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i)
    ensures IT.IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.ephemeral, i)
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
          assert IT.IndirectionTable.IsLocAllocIndirectionTable(s.ephemeralIndirectionTable.I(), i);
          assert IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
          assert IT.IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.ephemeral, i);
        } else {
          var r :| r in s'.ephemeralIndirectionTable.locs &&
              s'.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          assert MapsAgreeOnKey(
            s.ephemeralIndirectionTable.I().locs,
            s'.ephemeralIndirectionTable.I().locs, r);
          assert IT.IndirectionTable.IsLocAllocIndirectionTable(s.ephemeralIndirectionTable.I(), i);
          assert IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
          assert IT.IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.ephemeral, i);
        }
      }
    }

    forall i: int
    | IT.IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.ephemeral, i)
    ensures IT.IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i)
    {
      if j.Some? && i == j.value {
        assert IT.IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i);
      } else {
        assert IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
        assert IT.IndirectionTable.IsLocAllocIndirectionTable(s.ephemeralIndirectionTable.I(), i);
        if 0 <= i < MinNodeBlockIndex() {
          assert IT.IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i);
        } else {
          var r :| r in s.ephemeralIndirectionTable.locs &&
            s.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          assert MapsAgreeOnKey(
            s.ephemeralIndirectionTable.I().locs,
            s'.ephemeralIndirectionTable.I().locs, r);
          assert r in s'.ephemeralIndirectionTable.locs &&
            s'.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          assert IT.IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i);
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
*/

  lemma writeBookkeepingBitmapCorrect(s: BBC.Variables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  requires s.WriteAllocConditions()
  requires ChildrenConditions(s, children)
  ensures var s' := writeBookkeeping(s, ref, children);
    && s'.WriteAllocConditions()
  {
  }

  lemma allocCorrect(s: BBC.Variables, node: Node)
  requires BBC.Inv(s)
  requires s.WriteAllocConditions()
  requires BC.BlockPointsToValidReferences(INode(node), s.ephemeralIndirectionTable.graph)
  // requires TotalCacheSize(s) <= MaxCacheSize() - 1
  requires WFNode(node)
  requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures var (s', ref) := allocWithNode(s, node);
    && BBC.Inv(s')
    // && WFBCVars(s')
    && (ref.Some? ==> BC.Alloc(s, s', ref.value, INode(node)))
    && (ref.None? ==> s' == s)
    && (ref.Some? ==> s'.totalCacheSize() == s.totalCacheSize() + 1)
    && s'.WriteAllocConditions()
  {
    var ref := getFreeRef(s);
    if ref.Some? {
      lemmaIndirectionTableLocIndexValid(s, ref.value);
      // LruModel.LruUse(s.lru, ref.value);
      // writeBookkeepingBitmapCorrect(s, ref.value, node.children);
      reveal_writeBookkeeping();

      // var s' := writeWithNode(s, ref.value, node);
    }
  }

  lemma writeCorrect(s: BBC.Variables, ref: BT.G.Reference, node: Node)
  requires s.Ready?
  requires BBC.Inv(s)
  requires s.WriteAllocConditions()
  requires ref in s.ephemeralIndirectionTable.graph
  requires ref in s.cache
  requires WFNode(node)
  requires BC.BlockPointsToValidReferences(INode(node), s.ephemeralIndirectionTable.graph)
  requires s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value.graph ==> ref in s.frozenIndirectionTable.value.locs
  // requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures var s' := writeWithNode(s, ref, node);
    && BBC.Inv(s')
    && BC.Dirty(s, s', ref, INode(node))
    && s'.totalCacheSize() == s.totalCacheSize()
    && s'.WriteAllocConditions()
  {
    // lemmaIndirectionTableLocIndexValid(s, ref);
    WeightBucketEmpty();

    // LruModel.LruUse(s.lru, ref);

    // writeBookkeepingBitmapCorrect(s, ref, node.children);
    reveal_writeBookkeeping();

    // var s' := writeWithNode(s, ref, node);
    // assert WFBCVars(s');
  }
 
  lemma writeNewRefIsAlloc(s: BBC.Variables, ref: BT.G.Reference, node: Node)
  requires s.Ready?
  requires s.WriteAllocConditions()
  requires RefAvailable(s, ref)
  requires WFNode(node)
  // requires s.totalCacheSize() <= MaxCacheSize() - 1
  requires BC.BlockPointsToValidReferences(INode(node), s.ephemeralIndirectionTable.graph)
  // requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures var s' := writeWithNode(s, ref, node);
    && BC.Alloc(s, s', ref, INode(node))
    && s'.totalCacheSize() == s.totalCacheSize() + 1
    && s'.WriteAllocConditions()
  {
    assume s.ephemeralIndirectionTable.locs.Keys <= s.ephemeralIndirectionTable.graph.Keys;
    writeBookkeepingBitmapCorrect(s, ref, node.children);
  }

  lemma lemmaChildInGraph(s: BBC.Variables, ref: BT.G.Reference, childref: BT.G.Reference)
  requires s.Ready?
  requires BBC.Inv(s)
  requires ref in s.cache
  requires ref in s.ephemeralIndirectionTable.graph
  requires childref in BT.G.Successors(INode(s.cache[ref]))
  ensures childref in s.ephemeralIndirectionTable.graph
  {
    assert childref in s.ephemeralIndirectionTable.graph[ref];
  }

  lemma lemmaBlockPointsToValidReferences(s: BBC.Variables, ref: BT.G.Reference)
  requires BBC.Inv(s)
  requires s.Ready?
  requires ref in s.cache
  requires ref in s.ephemeralIndirectionTable.graph
  ensures BC.BlockPointsToValidReferences(INode(s.cache[ref]), s.ephemeralIndirectionTable.graph);
  {
    var node := INode(s.cache[ref]);
    var graph := s.ephemeralIndirectionTable.graph;
    forall r | r in BT.G.Successors(node) ensures r in graph
    {
      lemmaChildInGraph(s, ref, r);
    }
  }
/*

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
*/

  lemma lemmaChildrenConditionsOfNode(
      s: BBC.Variables, ref: BT.G.Reference)
  requires s.Ready?
  requires BBC.Inv(s)
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
      s: BBC.Variables, children: Option<seq<BT.G.Reference>>)
  requires s.WriteAllocConditions()
  requires ChildrenConditions(s, children)
  ensures var (s1, newref) := allocBookkeeping(s, children);
    newref.Some? ==> ChildrenConditions(s1, Some([newref.value]))
  {
    reveal_allocBookkeeping();
    reveal_writeBookkeeping();
    //assert newref.value in s1.ephemeralIndirectionTable.graph;
  }

  lemma lemmaChildrenConditionsUpdateOfAllocBookkeeping(
      s: BBC.Variables, children: Option<seq<BT.G.Reference>>,
          children1: seq<BT.G.Reference>, i: int)
  requires s.WriteAllocConditions()
  requires ChildrenConditions(s, children)
  requires ChildrenConditions(s, Some(children1))
  requires 0 <= i < |children1|
  ensures var (s1, newref) := allocBookkeeping(s, children);
    newref.Some? ==> ChildrenConditions(s1, Some(children1[i := newref.value]))
  {
    reveal_allocBookkeeping();
    reveal_writeBookkeeping();
  }

  lemma lemmaChildrenConditionsPreservedWriteBookkeeping(
      s: BBC.Variables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>,
      children1: Option<seq<BT.G.Reference>>)
  requires s.WriteAllocConditions()
  requires ChildrenConditions(s, children)
  requires ChildrenConditions(s, children1)
  ensures var s1 := writeBookkeeping(s, ref, children);
    ChildrenConditions(s1, children1)
  {
    reveal_writeBookkeeping();
  }

  lemma lemmaChildrenConditionsOfReplace1With2(
      s: BBC.Variables,
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

  lemma lemmaRefInGraphOfWriteBookkeeping(s: BBC.Variables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  requires s.WriteAllocConditions()
  requires ChildrenConditions(s, children)
  ensures var s1 := writeBookkeeping(s, ref, children);
    ref in s1.ephemeralIndirectionTable.graph
  {
    reveal_writeBookkeeping();
  }

  lemma lemmaRefInGraphPreservedWriteBookkeeping(s: BBC.Variables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>, ref2: BT.G.Reference)
  requires s.WriteAllocConditions()
  requires ChildrenConditions(s, children)
  requires ref2 in s.ephemeralIndirectionTable.graph
  ensures var s1 := writeBookkeeping(s, ref, children);
    ref2 in s1.ephemeralIndirectionTable.graph
  {
    reveal_writeBookkeeping();
  }
}