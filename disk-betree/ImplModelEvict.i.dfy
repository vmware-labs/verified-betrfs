include "ImplModelDealloc.i.dfy"
include "ImplModelSync.i.dfy"

module ImplModelEvict {
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelCache
  import opened ImplModelDealloc
  import opened ImplModelSync

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened NativeTypes

  import LruModel

  function Evict(k: Constants, s: Variables, ref: BT.G.Reference) : (s' : Variables)
  requires s.Ready?
  requires ref in s.cache
  {
    s.(cache := MapRemove1(s.cache, ref))
     .(lru := LruModel.Remove(s.lru, ref))
  }

  predicate NeedToWrite(s: Variables, ref: BT.G.Reference)
  requires s.Ready?
  {
    || (
      && ref in s.ephemeralIndirectionTable.contents
      && s.ephemeralIndirectionTable.contents[ref].0.None?
    )
    || (
      && s.frozenIndirectionTable.Some?
      && ref in s.frozenIndirectionTable.value.contents
      && s.frozenIndirectionTable.value.contents[ref].0.None?
    )
  }

  predicate CanEvict(s: Variables, ref: BT.G.Reference)
  requires s.Ready?
  requires ref in s.ephemeralIndirectionTable.contents ==>
      s.ephemeralIndirectionTable.contents[ref].0.Some?
  {
    && (ref in s.ephemeralIndirectionTable.contents ==>
      && BC.OutstandingWrite(ref, s.ephemeralIndirectionTable.contents[ref].0.value) !in s.outstandingBlockWrites.Values
    )
  }

  predicate EvictOrDealloc(k: Constants, s: Variables, io: IO,
      s': Variables, io': IO)
  requires Inv(k, s)
  requires s.Ready?
  requires io.IOInit?
  requires |s.cache| > 0
  {
    var ref := FindDeallocable(s);
    FindDeallocableCorrect(s);

    if ref.Some? then (
      // If we can deallocate something, just do that.
      (s', io') == Dealloc(k, s, io, ref.value)
    ) else (
      var ref := LruModel.Next(s.lru);
      if ref == BT.G.Root() then (
        && s' == s
        && io' == io
      ) else if NeedToWrite(s, ref) then (
        if && s.outstandingIndirectionTableWrite.None? then (
          && TryToWriteBlock(k, s, io, ref, s', io')
        ) else (
          && s' == s
          && io' == io
        )
      ) else if CanEvict(s, ref) then (
        && s' == Evict(k, s, ref)
        && io' == io
      ) else (
        && s' == s
        && io' == io
      )
    )
  }

  lemma EvictOrDeallocCorrect(k: Constants, s: Variables, io: IO,
      s': Variables, io': IO)
  requires EvictOrDealloc.requires(k, s, io, s', io')
  requires EvictOrDealloc(k, s, io, s', io')
  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    var ref := FindDeallocable(s);
    FindDeallocableCorrect(s);

    if ref.Some? {
      DeallocCorrect(k, s, io, ref.value);
    } else {
      var ref := LruModel.Next(s.lru);
      if ref == BT.G.Root() {
        assert noop(k, IVars(s), IVars(s));
      } else if (NeedToWrite(s, ref)) {
        if s.outstandingIndirectionTableWrite.None? {
          TryToWriteBlockCorrect(k, s, io, ref, s', io');
        } else {
          assert noop(k, IVars(s), IVars(s));
        }
      } else if CanEvict(s, ref) {
        LruModel.LruRemove(s.lru, ref);
        assert WFVars(s');
        assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io', BC.EvictStep(ref));
      } else {
        assert noop(k, IVars(s), IVars(s));
      }
    }
  }
}
