include "ImplCache.i.dfy"
include "ImplModelFlush.i.dfy"
include "ImplFlushRootBucket.i.dfy"

module ImplFlush { 
  import opened Impl
  import opened ImplCache
  import opened ImplState
  import opened ImplFlushRootBucket

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
  import ImplModelFlushRootBucket

  method flush(k: ImplConstants, s: ImplVariables, parentref: BT.G.Reference, slot: int, childref: BT.G.Reference, child: ImplModel.Node)
  returns (s': ImplVariables)
  requires Inv(k, s)
  requires WFVars(s)
  requires s.Ready?

  requires parentref in IIndirectionTable(s.ephemeralIndirectionTable)
  requires parentref in s.cache

  requires s.cache[parentref].children.Some?
  requires 0 <= slot < |s.cache[parentref].buckets|
  requires s.cache[parentref].children.value[slot] == childref

  requires childref in IIndirectionTable(s.ephemeralIndirectionTable)
  requires childref in s.cache
  requires s.cache[childref] == child

  ensures WVars(s')
  ensures ImplModelFlush.flush(Ic(k), old(IVars(s)), parentref, slot, childref, child) == IVars(s')
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

    var s1;
    if parentref == BT.G.Root() {
      ImplModelFlushRootBucket.flushRootBucketCorrect(Ic(k), IVars(s));
      s1 := flushRootBucket(k, s);
    } else {
      s1 := s;
    }

    var node := s1.cache[parentref];
    var childref := node.children.value[slot];

    assume forall i | 0 <= i < |child.buckets| :: |child.buckets[i].keys| + |node.buckets[slot].keys| < 0x8000_0000_0000_0000; // TODO should follow from node weight bound

    var newbuckets := KMTable.Flush(node.buckets[slot], child.buckets, child.pivotTable);
    var newchild := child.(buckets := newbuckets);
    var s2, newchildref := alloc(k, s1, newchild);
    if newchildref.None? {
      s' := s2;
      print "giving up; could not get parentref\n";
      return;
    }

    var newparent := IM.Node(
        node.pivotTable,
        Some(node.children.value[slot := newchildref.value]),
        node.buckets[slot := KMTable.Empty()]
      );

    s' := write(k, s2, parentref, newparent);
  }
}
