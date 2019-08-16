include "ImplModelCache.i.dfy"
include "AsyncDiskModel.s.dfy"

module ImplModelFlush { 
  import opened ImplModel
  import opened ImplModelCache

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes
  import D = AsyncDisk

  function flush(k: Constants, s: Variables, parentref: BT.G.Reference, slot: int)
  : (Variables, DiskOp)
  requires Inv(k, s)
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
      (s, D.NoDiskOp)
    ) else (
      var node := s.cache[parentref];
      var childref := node.children.value[slot];
      if (childref !in s.cache) then (
        PageInReq(k, s, io, childref)
      ) else (
        var child := s.cache[childref];
        if (!(
          && |node.buckets[slot].keys| < 0x4000_0000_0000_0000
          && |child.buckets| < 0x1_0000_0000_0000_0000
          && (forall i | 0 <= i < |child.buckets| :: |child.buckets[i].keys| < 0x4000_0000_0000_0000)
        )) then (
          (s, NoDiskOp)
        ) else (
          var newbuckets := KMTable.Flush(node.buckets[slot], child.buckets, child.pivotTable);
          var newchild := child.(buckets := newbuckets);
          var s1, newchildref := alloc(k, s, newchild);
          if newchildref.None? then (
            (s1, NoDiskOp)
          ) else (
            var newparent := Node(
              node.pivotTable,
              Some(node.children.value[slot := newchildref.value]),
              node.buckets[slot := KMTable.Empty()]
            );
            var s' := write(k, s1, parentref, newparent);
            s'
          )
        )
      )
    )
  }

  lemma flushCorrect(k: Constants, s: Variables, parentref: BT.G.Reference, slot: int)
  requires flush.requires(k, s, parentref, slot)
  ensures
      var (s', diskOp) := flush(k, s, parentref, slot);
      && WFVars(s')
      && ImplADM.M.Next(Ik(k), I(k, s), I(k, s'), UI.NoOp, diskOp)
}
