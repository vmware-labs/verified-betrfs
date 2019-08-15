include "ImplCache.i.dfy"

module ImplFlush { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes

  method flush(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference, slot: int)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires s.Ready?
  requires ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  requires ref in s.cache
  requires s.cache[ref].children.Some?
  requires 0 <= slot < |s.cache[ref].buckets|
  requires io.initialized()
  requires s.rootBucket == TTT.EmptyTree // FIXME we don't actually need this unless we're flushing the root
  modifies io
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies s.ephemeralIndirectionTable.Repr
  {
    if s.frozenIndirectionTable.Some? {
      var lbaGraph := s.frozenIndirectionTable.value.Get(ref);
      if lbaGraph.Some? {
        assert ref in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph;
        var (lba, _) := lbaGraph.value;
        if lba.None? {
          assert ref !in IS.IIndirectionTable(s.frozenIndirectionTable.value).locs;
          s' := s;
          assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
          print "giving up; flush can't run because frozen isn't written";
          return;
        }
      }
    }

    var node := s.cache[ref];

    INodeRootEqINodeForEmptyRootBucket(node);

    assert IS.INode(node) == IS.ICache(s.cache, s.rootBucket)[ref];
    assert BT.WFNode(IS.INode(node));

    var childref := node.children.value[slot];

    assert childref in BT.G.Successors(IS.INode(node));

    if (childref !in s.cache) {
      s' := PageInReq(k, s, io, childref);
      return;
    }

    var child := s.cache[childref];

    INodeRootEqINodeForEmptyRootBucket(child);

    assert IS.INode(child) == IS.ICache(s.cache, s.rootBucket)[childref];
    assert BT.WFNode(IS.INode(child));

    if (!(
      && |node.buckets[slot].keys| < 0x4000_0000_0000_0000
      && |child.buckets| < 0x1_0000_0000_0000_0000
      && (forall i | 0 <= i < |child.buckets| :: |child.buckets[i].keys| < 0x4000_0000_0000_0000)
    )) {
      s' := s;
      assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
      print "giving up; data is 2 big\n";
      return;
    }

    forall i, key | 0 <= i < |child.buckets| && key in KMTable.I(child.buckets[i]) ensures Pivots.Route(child.pivotTable, key) == i
    {
      //assert BT.NodeHasWFBucketAt(IS.INode(child), i);
    }

    var newbuckets := KMTable.Flush(node.buckets[slot], child.buckets, child.pivotTable);
    var newchild := child.(buckets := newbuckets);

    WFBucketListFlush(KMTable.I(node.buckets[slot]), KMTable.ISeq(child.buckets), child.pivotTable);

    assert BT.G.Successors(IS.INode(newchild)) == BT.G.Successors(IS.INode(child));
    assert BC.BlockPointsToValidReferences(IS.INode(newchild), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);

    var s1, newchildref := alloc(k, s, newchild);
    if newchildref.None? {
      s' := s;
      assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
      print "giving up; could not get ref\n";
      return;
    }
    ghost var s1Interpreted := IS.IVars(s1);

    var newparent := IS.Node(
        node.pivotTable,
        Some(node.children.value[slot := newchildref.value]),
        node.buckets[slot := KMTable.Empty()]
      );

    assert BC.BlockPointsToValidReferences(IS.INode(node), IS.IIndirectionTable(s1.ephemeralIndirectionTable).graph);
    forall ref | ref in BT.G.Successors(IS.INode(newparent)) ensures ref in IS.IIndirectionTable(s1.ephemeralIndirectionTable).graph {
      if (ref == newchildref.value) {
      } else {
        assert ref in BT.G.Successors(IS.INode(node));
      }
    }
    assert BC.BlockPointsToValidReferences(IS.INode(newparent), IS.IIndirectionTable(s1.ephemeralIndirectionTable).graph);

    assert ref in s.cache;
    assert ref in IS.ICache(s.cache, s.rootBucket);
    assert ref in IS.ICache(s1.cache, s1.rootBucket);
    assert ref in s1.cache;

    s' := write(k, s1, ref, newparent);

    ghost var flushStep := BT.NodeFlush(ref, IS.INode(node), childref, IS.INode(child), newchildref.value, IS.INode(newchild), slot);
    assert BT.ValidFlush(flushStep);
    ghost var step := BT.BetreeFlush(flushStep);
    assert IS.INode(newparent) == BT.FlushOps(flushStep)[1].node;
    BC.MakeTransaction2(k, old(IS.IVars(s)), s1Interpreted, IS.IVars(s'), BT.BetreeStepOps(step));
    assert stepsBetree(k, old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, step);
  }
}
