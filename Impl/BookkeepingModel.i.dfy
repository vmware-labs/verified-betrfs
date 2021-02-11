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
  import BBC = BetreeCache

  import opened NativeTypes

  predicate RefAvailable(s: BBC.Variables, ref: Reference)
    requires s.Ready?
  {
    && ref !in s.ephemeralIndirectionTable.graph
    && ref !in s.cache
    && ref != BT.G.Root()
  }

  // fullWrite and fullAlloc are like writeBookkeeping/allocBookkeeping, except that fullWrite and fullAlloc update
  // the cache with the node. In the implementation of betree operations we use the above,
  // because it turns out to be easier to do the cache updates separately. However, for the proofs
  // it is easier to use the below.

  function writeWithNode(s: BBC.Variables, ref: BT.G.Reference, node: Node)
  : (s': BBC.Variables)
    requires s.WriteAllocConditions()
    ensures s'.WriteAllocConditions()
    ensures |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
    var succs := if node.children.Some? then node.children.value else [];
    var oldLoc := MapLookupOption(s.ephemeralIndirectionTable.locs, ref);
    // TODO(andreal) s.ephemeralIndirectionTable.updateAndRemoveLoc(ref,
    // TODO(andreal)     (if node.children.Some? then node.children.value else []));
    var eph := s.ephemeralIndirectionTable.(
      graph := s.ephemeralIndirectionTable.graph[ref := succs]).(
      locs := MapRemove1(s.ephemeralIndirectionTable.locs, ref));
    var s' := s.(ephemeralIndirectionTable := eph).(cache := s.cache[ref := node]);
    assert s'.WriteAllocConditions();
    s'
  }

  lemma writeCorrect(s: BBC.Variables, ref: BT.G.Reference, node: Node)
  requires s.WriteAllocConditions()
  requires ref in s.ephemeralIndirectionTable.graph
  requires ref in s.cache
  // requires WFNode(node)
  requires BC.BlockPointsToValidReferences(INode(node), s.ephemeralIndirectionTable.graph)
  requires s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value.graph ==> ref in s.frozenIndirectionTable.value.locs
  // requires |s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  ensures var s' := writeWithNode(s, ref, node);
    && BC.Dirty(s, s', ref, INode(node))
    && s'.totalCacheSize() == s.totalCacheSize()
    && s'.WriteAllocConditions()
  {
    lemmaIndirectionTableLocIndexValid(s, ref);
  }

  function allocWithNode(s: BBC.Variables, node: Node)
  : (p: (BBC.Variables, Option<Reference>))
  requires s.WriteAllocConditions()
  requires BC.WFIndirectionTable(s.ephemeralIndirectionTable)
  requires BC.BlockPointsToValidReferences(INode(node), s.ephemeralIndirectionTable.graph)
  ensures var (s', ref) := p;
    && s'.WriteAllocConditions()
    && |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
    && (ref.Some? ==> BC.Alloc(s, s', ref.value, INode(node)))
    && (ref.None? ==> s' == s)
    && (ref.Some? ==> s'.totalCacheSize() == s.totalCacheSize() + 1)
    && s'.WriteAllocConditions()
  {
    var ref: Option<BT.G.Reference> :| ref.Some? ==> RefAvailable(s, ref.value);
    if ref.Some? then (
      lemmaIndirectionTableLocIndexValid(s, ref.value);
      var s' := writeWithNode(s, ref.value, node);
      assert ref.value !in s.ephemeralIndirectionTable.locs;
      assert s'.ephemeralIndirectionTable.locs == s.ephemeralIndirectionTable.locs;
      assert BC.Alloc(s, s', ref.value, INode(node));
      (s', ref)
    ) else (
      (s, None)
    )
  }

  // lemma allocCorrect(s: BBC.Variables, node: Node) //merged

  lemma lemmaIndirectionTableLocIndexValid(s: BBC.Variables, ref: BT.G.Reference)
  requires s.WriteAllocConditions()
  ensures ref in s.ephemeralIndirectionTable.locs ==>
    (
      // TODO needed? && 0 <= s.ephemeralIndirectionTable.locs[ref].addr as int / NodeBlockSize() < NumBlocks()
      && (s.ephemeralIndirectionTable.locs[ref].addr as int / NodeBlockSize()) * NodeBlockSize() == s.ephemeralIndirectionTable.locs[ref].addr as int
    )
  {
    if ref in s.ephemeralIndirectionTable.locs {
      reveal_ConsistentBitmap();
      var loc := s.ephemeralIndirectionTable.locs[ref];
      var i := loc.addr as int / NodeBlockSize();
      assert s.ephemeralIndirectionTable.locs[ref] == loc;
      assert loc in s.ephemeralIndirectionTable.locs.Values;
      assert DiskLayout.ValidNodeLocation(loc);
      DiskLayout.reveal_ValidNodeAddr();
      assert i * NodeBlockSize() == loc.addr as int;
      // TODO needed? assert 0 <= s.ephemeralIndirectionTable.locs[ref].addr as int / NodeBlockSize() < NumBlocks();
    }
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
  requires s.Ready?
  requires BBC.Inv(s)
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
  */
}
