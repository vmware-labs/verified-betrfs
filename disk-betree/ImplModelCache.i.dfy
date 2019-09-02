include "ImplModel.i.dfy"
include "ImplModelIO.i.dfy"
include "../lib/Sets.i.dfy"

module ImplModelCache { 
  import opened ImplModel
  import opened ImplModelIO

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketWeights
  import opened Bounds
  import KMTable
  import LruModel

  import opened NativeTypes

  predicate RefAvailable(s: Variables, ref: Reference)
  {
    && s.Ready?
    && ref !in s.ephemeralIndirectionTable
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
    if i !in s.ephemeralIndirectionTable && i !in s.cache then (
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
    if i != avoid && i !in s.ephemeralIndirectionTable && i !in s.cache then (
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

  function {:opaque} write(k: Constants, s: Variables, ref: BT.G.Reference, node: Node)
  : (s': Variables)
  requires s.Ready?
  ensures s'.Ready?
  {
    var eph := s.ephemeralIndirectionTable[ref := (None, if node.children.Some? then node.children.value else [])];
    s.(ephemeralIndirectionTable := eph).(cache := s.cache[ref := node])
        .(lru := LruModel.Use(s.lru, ref))
  }

  function {:opaque} alloc(k: Constants, s: Variables, node: Node)
  : (p: (Variables, Option<Reference>))
  requires s.Ready?
  ensures var (s', id) := p;
    s'.Ready?
  {
    var ref := getFreeRef(s);
    if ref.Some? then (
      (write(k, s, ref.value, node), ref)
    ) else (
      (s, None)
    )
  }
 
  lemma allocCorrect(k: Constants, s: Variables, node: Node)
  requires s.Ready?
  requires WFVars(s)
  requires WFNode(node)
  requires BC.BlockPointsToValidReferences(INode(node), IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires TotalCacheSize(s) <= MaxCacheSize() - 1
  ensures var (s', ref) := alloc(k, s, node);
    && WFVars(s')
    && (ref.Some? ==> BC.Alloc(Ik(k), IVars(s), IVars(s'), ref.value, INode(node)))
    && (ref.None? ==> s' == s)
    && (ref.Some? ==> TotalCacheSize(s') == TotalCacheSize(s) + 1)
  {
    reveal_alloc();
    reveal_write();
    var ref := getFreeRef(s);
    if ref.Some? {
      LruModel.LruUse(s.lru, ref.value);
    }
  }
  
  lemma writeCorrect(k: Constants, s: Variables, ref: BT.G.Reference, node: Node)
  requires s.Ready?
  requires WFVars(s)
  requires ref in IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in s.cache
  requires ref == BT.G.Root() ==> s.rootBucket == map[] && s.rootBucketWeightBound == 0
  requires WFNode(node)
  requires BC.BlockPointsToValidReferences(INode(node), IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value ==> s.frozenIndirectionTable.value[ref].0.Some?
  ensures var s' := write(k, s, ref, node);
    && WFVars(s')
    && BC.Dirty(Ik(k), IVars(s), IVars(s'), ref, INode(node))
    && TotalCacheSize(s') == TotalCacheSize(s)
  {
    reveal_write();
    if (ref == BT.G.Root()) {
      INodeRootEqINodeForEmptyRootBucket(node);
    }
    WeightBucketEmpty();

    LruModel.LruUse(s.lru, ref);

    var s' := write(k, s, ref, node);
    assert WFVars(s');
  }
 
  lemma writeCorrectWithRootBucket(k: Constants, s: Variables, ref: BT.G.Reference, node: Node)
  requires s.Ready?
  requires WFVars(s)
  requires ref in IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in s.cache
  requires WFNode(node)
  requires BC.BlockPointsToValidReferences(INode(node), IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires s.frozenIndirectionTable.Some? && ref in s.frozenIndirectionTable.value ==> s.frozenIndirectionTable.value[ref].0.Some?
  requires WeightBucketList(KMTable.ISeq(s.cache[ref].buckets))
      == WeightBucketList(KMTable.ISeq(node.buckets))
  ensures var s' := write(k, s, ref, node);
    && WFVars(s')
    && BC.Dirty(Ik(k), IVars(s), IVars(s'), ref, if ref == BT.G.Root() then INodeRoot(node, s.rootBucket) else INode(node))
    && TotalCacheSize(s') == TotalCacheSize(s)
  {
    reveal_write();
    var s' := write(k, s, ref, node);

    LruModel.LruUse(s.lru, ref);

    if (ref == BT.G.Root()) {
      assert WFVars(s');
      var inode := INodeRoot(node, s.rootBucket);
      assert BC.BlockPointsToValidReferences(inode, IIndirectionTable(s.ephemeralIndirectionTable).graph);
    }
  }

  lemma writeNewRefIsAlloc(k: Constants, s: Variables, ref: BT.G.Reference, node: Node)
  requires s.Ready?
  requires WFVars(s)
  requires RefAvailable(s, ref)
  requires WFNode(node)
  requires TotalCacheSize(s) <= MaxCacheSize() - 1
  requires BC.BlockPointsToValidReferences(INode(node), IIndirectionTable(s.ephemeralIndirectionTable).graph)
  ensures var s' := write(k, s, ref, node);
    && WFVars(s')
    && BC.Alloc(Ik(k), IVars(s), IVars(s'), ref, INode(node))
    && TotalCacheSize(s') == TotalCacheSize(s) + 1
  {
    reveal_write();
    LruModel.LruUse(s.lru, ref);
  }

  lemma lemmaChildInGraph(k: Constants, s: Variables, ref: BT.G.Reference, childref: BT.G.Reference)
  requires s.Ready?
  requires Inv(k, s)
  requires ref in s.cache
  requires ref in s.ephemeralIndirectionTable
  requires childref in BT.G.Successors(INode(s.cache[ref]))
  ensures childref in s.ephemeralIndirectionTable
  {
    assert childref in IIndirectionTable(s.ephemeralIndirectionTable).graph[ref];
  }

  lemma lemmaGraphChildInGraph(k: Constants, s: Variables, ref: BT.G.Reference, childref: BT.G.Reference)
  requires s.Ready?
  requires Inv(k, s)
  requires ref in s.ephemeralIndirectionTable
  requires childref in s.ephemeralIndirectionTable[ref].1
  ensures childref in s.ephemeralIndirectionTable

  lemma lemmaBlockPointsToValidReferences(k: Constants, s: Variables, ref: BT.G.Reference)
  requires Inv(k, s)
  requires s.Ready?
  requires ref in s.cache
  requires ref in s.ephemeralIndirectionTable
  ensures BC.BlockPointsToValidReferences(INode(s.cache[ref]), IIndirectionTable(s.ephemeralIndirectionTable).graph);
  {
    var node := INode(s.cache[ref]);
    var graph := IIndirectionTable(s.ephemeralIndirectionTable).graph;
    forall r | r in BT.G.Successors(node) ensures r in graph
    {
      lemmaChildInGraph(k, s, ref, r);
    }
  }
}
