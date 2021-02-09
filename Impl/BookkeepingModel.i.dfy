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

  // fullWrite and fullAlloc are like writeBookkeeping/allocBookkeeping, except that fullWrite and fullAlloc update
  // the cache with the node. In the implementation of betree operations we use the above,
  // because it turns out to be easier to do the cache updates separately. However, for the proofs
  // it is easier to use the below.

  function writeWithNodeTest(s: BBC.Variables, ref: BT.G.Reference, node: Node)
  : (s': BBC.Variables)
    requires s.WriteAllocConditions()
    requires var succs := node.children;
    succs.Some? ==> (
      // && |succs.value| <= MaxNumChildren()
      && IT.IndirectionTable.SuccsValid(succs.value, s.ephemeralIndirectionTable.graph)
    )

    ensures s'.WriteAllocConditions()
    ensures |s'.ephemeralIndirectionTable.graph| <= |s.ephemeralIndirectionTable.graph| + 1
  {
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
/*

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
