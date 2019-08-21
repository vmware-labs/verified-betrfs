include "ImplModelCache.i.dfy"

module ImplModelDealloc { 
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelCache

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened NativeTypes

  predicate deallocable(s: Variables, ref: BT.G.Reference)
  {
    && s.Ready?
    && ref in IIndirectionTable(s.ephemeralIndirectionTable).graph
    && ref != BT.G.Root()
    && forall r | r in IIndirectionTable(s.ephemeralIndirectionTable).graph :: ref !in IIndirectionTable(s.ephemeralIndirectionTable).graph[r]
  }

  function Dealloc(k: Constants, s: Variables, io: IO, ref: BT.G.Reference)
  : (res : (Variables, IO))
  requires Inv(k, s)
  requires io.IOInit?
  requires deallocable(s, ref)
  {
    if (
      && s.frozenIndirectionTable.Some?
      && ref in s.frozenIndirectionTable.value
      && var entry := s.frozenIndirectionTable.value[ref];
      && var (loc, _) := entry;
      && loc.None?
    ) then (
      (s, io)
    ) else if !BC.OutstandingBlockReadsDoesNotHaveRef(s.outstandingBlockReads, ref) then (
      (s, io)
    ) else (
      var s' := s
        .(ephemeralIndirectionTable := MapRemove1(s.ephemeralIndirectionTable, ref))
        .(cache := MapRemove1(s.cache, ref));
      (s', io)
    )
  }

  lemma DeallocCorrect(k: Constants, s: Variables, io: IO, ref: BT.G.Reference)
  requires Inv(k, s)
  requires io.IOInit?
  requires deallocable(s, ref)
  ensures var (s', io') := Dealloc(k, s, io, ref);
      && WFVars(s')
      &&  M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    var (s', io') := Dealloc(k, s, io, ref);

    if (
      && s.frozenIndirectionTable.Some?
      && ref in s.frozenIndirectionTable.value
      && var entry := s.frozenIndirectionTable.value[ref];
      && var (loc, _) := entry;
      && loc.None?
    ) {
      assert noop(k, IVars(s), IVars(s'));
      return;
    }

    if !BC.OutstandingBlockReadsDoesNotHaveRef(s.outstandingBlockReads, ref) {
      assert noop(k, IVars(s), IVars(s'));
      return;
    }

    var iDiskOp := M.IDiskOp(diskOp(io));
    assert BC.Unalloc(Ik(k), IVars(s), IVars(s'), iDiskOp, ref);
    assert BBC.BlockCacheMove(Ik(k), IVars(s), IVars(s'), UI.NoOp, iDiskOp, BC.UnallocStep(ref));
    assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.UnallocStep(ref));
    // assert M.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, io.diskOp(), M.Step(BBC.BlockCacheMoveStep(BC.UnallocStep(ref))));
  }

  /*
  method FindDeallocable(s: Variables) returns (ref: Option<Reference>)
  requires WFVars(s)
  requires s.Ready?
  ensures ref.Some? ==> ref.value in IIndirectionTable(s.ephemeralIndirectionTable).graph
  ensures ref.Some? ==> deallocable(s, ref.value)
  ensures ref.None? ==> forall r | r in IIndirectionTable(s.ephemeralIndirectionTable).graph :: !deallocable(s, r)
  {
    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralRefs := SetToSeq(ephemeralTable.Keys);

    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;

    var i: uint64 := 0;
    while i as int < |ephemeralRefs|
    invariant i as int <= |ephemeralRefs|
    invariant forall k : nat | k < i as nat :: (
        && ephemeralRefs[k] in IIndirectionTable(s.ephemeralIndirectionTable).graph
        && !deallocable(s, ephemeralRefs[k]))
    {
      var ref := ephemeralRefs[i];
      var isDeallocable := Deallocable(s, ref);
      if isDeallocable {
        return Some(ref);
      }
      i := i + 1;
    }
    assert forall r | r in IIndirectionTable(s.ephemeralIndirectionTable).graph :: !deallocable(s, r);
    return None;
  }
  */
}
