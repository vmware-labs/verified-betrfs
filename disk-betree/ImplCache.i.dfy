include "ImplIO.i.dfy"

module ImplCache { 
  import opened Impl
  import opened ImplIO

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened NativeTypes

  method getFreeRef(s: ImplVariables)
  returns (ref : Option<BT.G.Reference>)
  requires s.Ready?
  requires s.ephemeralIndirectionTable.Inv()
  ensures ref.Some? ==> ref.value !in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  ensures ref.Some? ==> ref.value !in s.cache
  {
    var ephemeral': map<uint64, (Option<BC.Location>, seq<IS.Reference>)> := s.ephemeralIndirectionTable.ToMap();
    var ephemeral_graph := map ref | ref in ephemeral' :: ephemeral'[ref].1;

    if r :| r !in ephemeral_graph && r !in s.cache {
      ref := Some(r);
    } else {
      ref := None;
    }
  }

  method write(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, node: IS.Node)
  returns (s': ImplVariables)
  requires s.Ready?
  requires IS.WFVars(s)
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in s.cache
  requires ref == BT.G.Root() ==> s.rootBucket == TTT.EmptyTree
  requires IS.WFNode(node)
  requires BC.BlockPointsToValidReferences(IS.INode(node), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph)
  requires s.frozenIndirectionTable.Some? && ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph ==>
      ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).locs
  ensures IS.WFVars(s')
  ensures BC.Dirty(k, old(IS.IVars(s)), IS.IVars(s'), ref, IS.INode(node))
  ensures s'.ephemeralIndirectionTable == s.ephemeralIndirectionTable
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies s.ephemeralIndirectionTable.Repr
  {
    if (ref == BT.G.Root()) {
      INodeRootEqINodeForEmptyRootBucket(node);
    }

    var lbaGraph := s.ephemeralIndirectionTable.Remove(ref);
    assert lbaGraph.Some?;
    var (lba, graph) := lbaGraph.value;

    // TODO how do we deal with this?
    assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;
    var _ := s.ephemeralIndirectionTable.Insert(ref, (None, if node.children.Some? then node.children.value else []));

    s' := s.(cache := s.cache[ref := node]);
    assert BC.Dirty(k, old(IS.IVars(s)), IS.IVars(s'), ref, IS.INode(node));
  }

  method alloc(k: ImplConstants, s: ImplVariables, node: IS.Node)
  returns (s': ImplVariables, ref: Option<BT.G.Reference>)
  requires IS.WFVars(s)
  requires IS.WFNode(node)
  requires BC.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires BC.BlockPointsToValidReferences(IS.INode(node), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph)
  ensures IS.WFVars(s)
  ensures IS.WFVars(s')
  ensures ref.Some? ==> BC.Alloc(k, old(IS.IVars(s)), IS.IVars(s'), ref.value, IS.INode(node))
  ensures ref.Some? ==> ref.value !in old(s.cache)
  ensures ref.Some? ==> ref.value !in old(IS.IVars(s)).ephemeralIndirectionTable.locs
  ensures ref.Some? ==> ref.value !in old(IS.IVars(s)).ephemeralIndirectionTable.graph

  ensures ref.Some? ==> s' == old(s.(cache := s.cache[ref.value := node]))
  ensures ref.Some? ==> IS.IVars(s') == old(IS.IVars(s))
      .(ephemeralIndirectionTable := BC.IndirectionTable(
          old(IS.IVars(s)).ephemeralIndirectionTable.locs,
          old(IS.IVars(s)).ephemeralIndirectionTable.graph[ref.value := if node.children.Some? then node.children.value else []]))
      .(cache := old(IS.IVars(s)).cache[ref.value := IS.INode(node)])

  ensures ref.None? ==> s' == s
  ensures ref.None? ==> IS.IVars(s') == old(IS.IVars(s))
  ensures ref.None? ==> IS.IVars(s) == old(IS.IVars(s))

  ensures s'.Ready?
  ensures s.rootBucket == s'.rootBucket
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s'.ephemeralIndirectionTable.Repr == s.ephemeralIndirectionTable.Repr
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies s.ephemeralIndirectionTable.Repr
  {
    ref := getFreeRef(s);
    if (ref.Some?) {
      // TODO how do we deal with this?
      assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;
      var _ := s.ephemeralIndirectionTable.Insert(ref.value, (None, if node.children.Some? then node.children.value else []));
      s' := s.(cache := s.cache[ref.value := node]);
      assert ref.Some? ==> IS.IVars(s') == old(IS.IVars(s))
          .(ephemeralIndirectionTable := BC.IndirectionTable(
              old(IS.IVars(s)).ephemeralIndirectionTable.locs,
              old(IS.IVars(s)).ephemeralIndirectionTable.graph[ref.value := if node.children.Some? then node.children.value else []]))
          .(cache := old(IS.IVars(s)).cache[ref.value := IS.INode(node)]);
      assert ref.Some? ==> BC.Alloc(k, old(IS.IVars(s)), IS.IVars(s'), ref.value, IS.INode(node));
    } else {
      s' := s;
    }
  }

  method rollbackAlloc(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, node: IS.Node, ghost is0: ImplADM.M.Variables)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires IS.WFNode(node)
  requires s.Ready?
  requires ref !in IS.IIndirectionTable(s.ephemeralIndirectionTable).locs
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in s.cache
  // requires ref != BT.G.Root()
  requires s.rootBucket != TTT.EmptyTree ==> ref != BT.G.Root()
  requires BC.Alloc(k, is0, IS.IVars(s), ref, IS.INode(node))
  ensures IS.WFVars(s)
  ensures IS.WFVars(s')
  ensures s'.Ready?
  ensures IS.IVars(s') == is0
  ensures s.rootBucket == s'.rootBucket
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s'.ephemeralIndirectionTable.Repr == s.ephemeralIndirectionTable.Repr
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies s.ephemeralIndirectionTable.Repr
  {
    var _ := s.ephemeralIndirectionTable.Remove(ref);
    s' := s.(cache := MapRemove1(s.cache, ref));
    assert IS.IVars(s') == old(IS.IVars(s))
        .(ephemeralIndirectionTable := BC.IndirectionTable(
            old(IS.IVars(s)).ephemeralIndirectionTable.locs,
            MapRemove1(old(IS.IVars(s)).ephemeralIndirectionTable.graph, ref)))
        .(cache := MapRemove1(old(IS.IVars(s)).cache, ref));
  }
}
