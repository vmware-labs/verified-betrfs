include "ImplCache.i.dfy"
include "ImplModelDealloc.i.dfy"

module ImplDealloc { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache
  import ImplModelDealloc
  import opened ImplState

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import LruModel

  import opened NativeTypes

  method Deallocable(s: ImplVariables, ref: BT.G.Reference) returns (result: bool)
  requires WVars(s)
  requires s.Ready? ==> s.ephemeralIndirectionTable.Inv()
  ensures result == ImplModelDealloc.deallocable(IVars(s), ref)
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
    assert ref in IM.IIndirectionTable(IIndirectionTable(s.ephemeralIndirectionTable)).graph;
    var table := s.ephemeralIndirectionTable.ToMap();
    var graph := map k | k in table :: table[k].1;
    assert graph == IM.IIndirectionTable(IIndirectionTable(s.ephemeralIndirectionTable)).graph;
    result := forall r | r in graph :: ref !in graph[r];
  }

  method Dealloc(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, ref: BT.G.Reference)
  returns (s': ImplVariables)
  requires Inv(k, s)
  requires io.initialized()
  requires ImplModelDealloc.deallocable(IVars(s), ref)
  requires io !in VariablesReadSet(s)
  modifies io
  ensures WVars(s')
  ensures s'.Ready?
  ensures (IVars(s'), IIO(io)) == ImplModelDealloc.Dealloc(Ic(k), old(IVars(s)), old(IIO(io)), ref);
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s'.Ready?
  ensures s'.ephemeralIndirectionTable.Repr == s.ephemeralIndirectionTable.Repr
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  ensures forall r | r in s'.lru.Repr :: fresh(r) || r in old(s.lru.Repr)
  modifies s.ephemeralIndirectionTable.Repr
  modifies s.lru.Repr
  {
    ImplModelDealloc.reveal_Dealloc();

    if s.frozenIndirectionTable.Some? {
      var lbaGraph := s.frozenIndirectionTable.value.Get(ref);
      if lbaGraph.Some? {
        var (lba, _) := lbaGraph.value;
        if lba.None? {
          s' := s;
          print "giving up; dealloc can't dealloc because frozen isn't written\n";
          return;
        }
      }
    }

    if !BC.OutstandingBlockReadsDoesNotHaveRef(s.outstandingBlockReads, ref) {
      s' := s;
      print "giving up; dealloc can't dealloc because of outstanding read\n";
      return;
    }

    var _ := s.ephemeralIndirectionTable.Remove(ref);

    s.lru.Remove(ref);
    s' := s
      .(cache := MapRemove(s.cache, {ref}));

    assume s'.ephemeralIndirectionTable.Contents
        == MapRemove(old(s'.ephemeralIndirectionTable.Contents), {ref});
  }

  method FindDeallocable(s: ImplVariables) returns (ref: Option<Reference>)
  requires WFVars(s)
  requires s.Ready?
  ensures ref == ImplModelDealloc.FindDeallocable(IVars(s))
  {
    ImplModelDealloc.reveal_FindDeallocable();

    // TODO once we have an lba freelist, rewrite this to avoid extracting a `map` from `s.ephemeralIndirectionTable`
    var ephemeralTable := s.ephemeralIndirectionTable.ToMap();
    var ephemeralRefs := SetToSeq(ephemeralTable.Keys);

    assume |ephemeralRefs| < 0x1_0000_0000_0000_0000;

    var i: uint64 := 0;
    while i as int < |ephemeralRefs|
    invariant 0 <= i as int <= |ephemeralRefs|
    invariant ImplModelDealloc.FindDeallocableIterate(IVars(s), ephemeralRefs, i)
           == ImplModelDealloc.FindDeallocable(IVars(s))
    {
      var ref := ephemeralRefs[i];
      var isDeallocable := Deallocable(s, ref);
      if isDeallocable {
        return Some(ref);
      }
      i := i + 1;
    }
    return None;
  }
}
