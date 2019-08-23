include "ImplCache.i.dfy"
include "ImplModelFlush.i.dfy"

module ImplFlush { 
  import opened Impl
  import opened ImplCache

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes
  import ImplModel
  import ImplModelCache
  import ImplModelFlush

  method flush(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, parentref: BT.G.Reference, slot: int)
  returns (s': ImplVariables)
  requires IS.Inv(k, s)
  requires IS.WFVars(s)
  requires s.Ready?
  requires parentref in IS.IIndirectionTable(s.ephemeralIndirectionTable)
  requires parentref in s.cache
  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].buckets|
  requires io.initialized()
  requires s.rootBucket == TTT.EmptyTree // FIXME we don't actually need this unless we're flushing the root
  modifies io
  ensures IS.WVars(s')
  ensures ImplModelFlush.flush(IS.Ic(k), old(IS.IVars(s)), old(IS.IIO(io)), parentref, slot) == (IS.IVars(s'), IS.IIO(io))
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies s.ephemeralIndirectionTable.Repr
  {
    if s.frozenIndirectionTable.Some? {
      var lbaGraph := s.frozenIndirectionTable.value.Get(parentref);
      if lbaGraph.Some? {
        var (lba, _) := lbaGraph.value;
        if lba.None? {
          s' := s;
          print "giving up; flush can't run because frozen isn't written";
          return;
        }
      }
    }

    var node := s.cache[parentref];
    var childref := node.children.value[slot];
    if (childref !in s.cache) {
      ImplModelCache.lemmaChildInGraph(IS.Ic(k), IS.IVars(s), parentref, childref);
      // trigger something in Inv about every child pointer points to allocated
      // indirection record.
      assert childref in ImplModel.IIndirectionTable(IS.IIndirectionTable(s.ephemeralIndirectionTable)).graph;
      s' := ImplIO.PageInReq(k, s, io, childref);
      return;
    }

    var child := s.cache[childref];
    if (!(
      && |node.buckets[slot].keys| < 0x4000_0000_0000_0000
      && |child.buckets| < 0x1_0000_0000_0000_0000
      && (forall i | 0 <= i < |child.buckets| :: |child.buckets[i].keys| < 0x4000_0000_0000_0000)
    )) {
      s' := s;
      print "giving up; data is 2 big\n";
      return;
    }

    var newbuckets := KMTable.Flush(node.buckets[slot], child.buckets, child.pivotTable);
    var newchild := child.(buckets := newbuckets);
    var s1, newchildref := alloc(k, s, newchild);
    if newchildref.None? {
      s' := s1;
      print "giving up; could not get parentref\n";
      return;
    }

    var newparent := IS.IM.Node(
        node.pivotTable,
        Some(node.children.value[slot := newchildref.value]),
        node.buckets[slot := KMTable.Empty()]
      );

    s' := write(k, s1, parentref, newparent);
  }
}
