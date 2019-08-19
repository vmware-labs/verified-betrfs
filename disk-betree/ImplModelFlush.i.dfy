include "ImplModelCache.i.dfy"
include "ImplModelIO.i.dfy"
include "AsyncDiskModel.s.dfy"

module ImplModelFlush { 
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelCache

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes
  import D = AsyncDisk

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

  function flush(k: Constants, s: Variables, io: IO, parentref: BT.G.Reference, slot: int)
  : (Variables, IO)
  requires Inv(k, s)
  requires io.IOInit?
  requires s.Ready?
  requires parentref in s.ephemeralIndirectionTable
  requires parentref in s.cache
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].buckets|
  requires s.rootBucket == map[] // FIXME we don't actually need this unless we're flushing the root
  {
    if (
      && s.frozenIndirectionTable.Some?
      && parentref in s.frozenIndirectionTable.value
      && var entry := s.frozenIndirectionTable.value[parentref];
      && var (loc, _) := entry;
      && loc.None?
    ) then (
      (s, io)
    ) else (
      var node := s.cache[parentref];
      var childref := node.children.value[slot];

      lemmaChildInGraph(k, s, parentref, childref);

      if (childref !in s.cache) then (
        assert childref in IIndirectionTable(s.ephemeralIndirectionTable).graph;
        assert childref in IIndirectionTable(s.ephemeralIndirectionTable).locs;
        PageInReq(k, s, io, childref)
      ) else (
        var child := s.cache[childref];
        if (!(
          && |node.buckets[slot].keys| < 0x4000_0000_0000_0000
          && |child.buckets| < 0x1_0000_0000_0000_0000
          && (forall i | 0 <= i < |child.buckets| :: |child.buckets[i].keys| < 0x4000_0000_0000_0000)
        )) then (
          (s, io)
        ) else (
          var newbuckets := KMTable.flush(node.buckets[slot], child.buckets, child.pivotTable);
          var newchild := child.(buckets := newbuckets);
          var (s1, newchildref) := alloc(k, s, newchild);
          if newchildref.None? then (
            (s1, io)
          ) else (
            var newparent := Node(
              node.pivotTable,
              Some(node.children.value[slot := newchildref.value]),
              node.buckets[slot := KMTable.Empty()]
            );
            var s' := write(k, s1, parentref, newparent);
            (s', io)
          )
        )
      )
    )
  }

  lemma flushCorrect(k: Constants, s: Variables, io: IO, parentref: BT.G.Reference, slot: int)
  requires flush.requires(k, s, io, parentref, slot)
  ensures
      var (s', io') := flush(k, s, io, parentref, slot);
      && WFVars(s')
      && M.Next(Ik(k), I(k, s), I(k, s'), UI.NoOp, diskOp(io'))
  {
    if (
      && s.frozenIndirectionTable.Some?
      && parentref in s.frozenIndirectionTable.value
      && var entry := s.frozenIndirectionTable.value[parentref];
      && var (loc, _) := entry;
      && loc.None?
    ) {
      assert noop(k, IVars(s), IVars(s));
    } else {
      var node := s.cache[parentref];
      var childref := node.children.value[slot];

      lemmaChildInGraph(k, s, parentref, childref);
      INodeRootEqINodeForEmptyRootBucket(node);

      if (childref !in s.cache) {
        assert childref in IIndirectionTable(s.ephemeralIndirectionTable).graph;
        assert childref in IIndirectionTable(s.ephemeralIndirectionTable).locs;
        PageInReqCorrect(k, s, io, childref);
      } else {
        var child := s.cache[childref];
        INodeRootEqINodeForEmptyRootBucket(child);
        if (!(
          && |node.buckets[slot].keys| < 0x4000_0000_0000_0000
          && |child.buckets| < 0x1_0000_0000_0000_0000
          && (forall i | 0 <= i < |child.buckets| :: |child.buckets[i].keys| < 0x4000_0000_0000_0000)
        )) {
          assert noop(k, IVars(s), IVars(s));
        } else {
          var newbuckets := KMTable.flush(node.buckets[slot], child.buckets, child.pivotTable);
          KMTable.flushRes(node.buckets[slot], child.buckets, child.pivotTable);
          assume WFBuckets(newbuckets); // at the moment, only the KMTable.Flush method proves this.
          WFBucketListFlush(KMTable.I(node.buckets[slot]), KMTable.ISeq(child.buckets), child.pivotTable);
          
          var newchild := child.(buckets := newbuckets);
          var (s1, newchildref) := alloc(k, s, newchild);
          reveal_alloc();
          if newchildref.None? {
            assert noop(k, IVars(s), IVars(s1));
          } else {
            var newparent := Node(
              node.pivotTable,
              Some(node.children.value[slot := newchildref.value]),
              node.buckets[slot := KMTable.Empty()]
            );
            INodeRootEqINodeForEmptyRootBucket(newparent);

            var s' := write(k, s1, parentref, newparent);
            reveal_write();

            forall ref | ref in BT.G.Successors(INode(newparent)) ensures ref in IIndirectionTable(s1.ephemeralIndirectionTable).graph {
              if (ref == newchildref.value) {
              } else {
                assert ref in BT.G.Successors(INode(node));
                lemmaChildInGraph(k, s, parentref, ref);
                assert ref in IIndirectionTable(s1.ephemeralIndirectionTable).graph;
              }
            }
            assert BC.BlockPointsToValidReferences(INode(newparent), IIndirectionTable(s1.ephemeralIndirectionTable).graph);

            forall ref | ref in BT.G.Successors(INode(newchild)) ensures ref in IIndirectionTable(s.ephemeralIndirectionTable).graph {
              lemmaChildInGraph(k, s, childref, ref);
            }

            allocCorrect(k, s, newchild);
            writeCorrect(k, s1, parentref, newparent);

            ghost var flushStep := BT.NodeFlush(parentref, INode(node), childref, INode(child), newchildref.value, INode(newchild), slot);
            assert BT.ValidFlush(flushStep);
            ghost var step := BT.BetreeFlush(flushStep);
            assert INode(newparent) == BT.FlushOps(flushStep)[1].node;
            assert BC.Dirty(Ik(k), IVars(s1), IVars(s'), parentref, INode(newparent));
            BC.MakeTransaction2(Ik(k), IVars(s), IVars(s1), IVars(s'), BT.BetreeStepOps(step));
            assert stepsBetree(k, IVars(s), IVars(s'), UI.NoOp, step);
          }
        }
      }
    }
  }
}
