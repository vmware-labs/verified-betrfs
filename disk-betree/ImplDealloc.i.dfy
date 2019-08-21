include "ImplCache.i.dfy"

module ImplDealloc { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened NativeTypes

  method Deallocable(s: ImplVariables, ref: BT.G.Reference) returns (result: bool)
  requires s.Ready? ==> s.ephemeralIndirectionTable.Inv()
  ensures result == ImplModelDealloc.deallocable(s, ref)
  {
    if ref == BT.G.Root() {
      return false;
    }
    assert ref != BT.G.Root();
    if !s.Ready? {
      return false;
    }
    assert s.Ready?;
    var lbaGraph := s.ephemeralIndirectionTable.Get(ref);
    if !lbaGraph.Some? {
      return false;
    }
    assert ref in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph;
    var table := s.ephemeralIndirectionTable.ToMap();
    var graph := map k | k in table :: table[k].1;
    assert graph == IS.IIndirectionTable(s.ephemeralIndirectionTable).graph;
    result := forall r | r in graph :: ref !in graph[r];
    assert result == deallocable(s, ref);
  }

  method Dealloc(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  returns (s': ImplVariables)
  requires IS.WFVars(s)
  requires io.initialized()
  requires deallocable(s, ref)
  modifies io
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp())
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s'.ephemeralIndirectionTable.Repr == s.ephemeralIndirectionTable.Repr
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
          print "giving up; dealloc can't dealloc because frozen isn't written\n";
          return;
        }
      }
    }

    if !BC.OutstandingBlockReadsDoesNotHaveRef(s.outstandingBlockReads, ref) {
      s' := s;
      assert noop(k, old(IS.IVars(s)), IS.IVars(s'));
      print "giving up; dealloc can't dealloc because of outstanding read\n";
      return;
    }

    var _ := s.ephemeralIndirectionTable.Remove(ref);

    assert IS.IIndirectionTable(s.ephemeralIndirectionTable) ==
      old(BC.IndirectionTable(
        MapRemove(IS.IIndirectionTable(s.ephemeralIndirectionTable).locs, {ref}),
        MapRemove(IS.IIndirectionTable(s.ephemeralIndirectionTable).graph, {ref})
      ));

    s' := s
      .(cache := MapRemove(s.cache, {ref}));
    ghost var iDiskOp := ImplADM.M.IDiskOp(io.diskOp());
    assert BC.Unalloc(Ik(k), old(IS.IVars(s)), IS.IVars(s'), iDiskOp, ref);
    assert BBC.BlockCacheMove(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, iDiskOp, BC.UnallocStep(ref));
    assert stepsBC(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io, BC.UnallocStep(ref));
    // assert ImplADM.M.NextStep(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.NoOp, io.diskOp(), ImplADM.M.Step(BBC.BlockCacheMoveStep(BC.UnallocStep(ref))));
  }

  method FindDeallocable(s: ImplVariables) returns (ref: Option<IS.Reference>)
  requires IS.WFVars(s)
  requires s.Ready?
  ensures ref.Some? ==> ref.value in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
  ensures ref.Some? ==> deallocable(s, ref.value)
  ensures ref.None? ==> forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph :: !deallocable(s, r)
  {
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralRefs := SetToSeq(ephemeralTable.Keys);

    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;

    var i: uint64 := 0;
    while i as int < |ephemeralRefs|
    invariant i as int <= |ephemeralRefs|
    invariant forall k : nat | k < i as nat :: (
        && ephemeralRefs[k] in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph
        && !deallocable(s, ephemeralRefs[k]))
    {
      var ref := ephemeralRefs[i];
      var isDeallocable := Deallocable(s, ref);
      if isDeallocable {
        return Some(ref);
      }
      i := i + 1;
    }
    assert forall r | r in IS.IIndirectionTable(s.ephemeralIndirectionTable).graph :: !deallocable(s, r);
    return None;
  }
}
