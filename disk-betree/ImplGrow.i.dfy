include "ImplCache.i.dfy"
include "ImplModelGrow.i.dfy"
include "ImplFlushRootBucket.i.dfy"

module ImplGrow { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache
  import opened ImplState
  import opened ImplFlushRootBucket
  import ImplModelGrow
  import ImplModelFlushRootBucket

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened NativeTypes

  /// The root was found to be too big: grow
  method grow(k: ImplConstants, s: ImplVariables)
  returns (s': ImplVariables)
  requires Inv(k, s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  ensures IS.WVars(s')
  ensures s'.Ready?
  ensures IVars(s') == ImplModelGrow.grow(Ic(k), old(IVars(s)))
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  ensures forall r | r in s'.lru.Repr :: fresh(r) || r in old(s.lru.Repr)
  modifies s.ephemeralIndirectionTable.Repr
  modifies s.lru.Repr
  {
    ImplModelGrow.reveal_grow();

    if s.frozenIndirectionTable.Some? {
      var rootLbaGraph := s.frozenIndirectionTable.value.Get(BT.G.Root());
      if rootLbaGraph.Some? {
        var (lba, _) := rootLbaGraph.value;
        if lba.None? {
          s' := s;
          print "giving up; grow can't run because frozen isn't written\n";
          return;
        }
      }
    }

    var s0 := flushRootBucket(k, s);
    ImplModelFlushRootBucket.flushRootBucketCorrect(Ic(k), IVars(s));

    var oldroot := s0.cache[BT.G.Root()];
    var s1, newref := alloc(k, s0, oldroot);

    // NOALIAS statically enforced no-aliasing would probably help here
    /* (doc) assert forall r | r in s1.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s0.ephemeralIndirectionTable.Repr); */
    /* (doc) assert forall r | r in s1.ephemeralIndirectionTable.Repr :: fresh(r) || r in s0.ephemeralIndirectionTable.Repr; */

    match newref {
      case None => {
        s' := s1;
        print "giving up; could not allocate ref\n";
      }
      case Some(newref) => {
        var newroot := IM.Node([], Some([newref]), [KMTable.Empty()]);

        // NOALIAS statically enforced no-aliasing would probably help here
        /* (doc) assert forall r | r in s1.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s0.ephemeralIndirectionTable.Repr); */
        /* (doc) assert forall r | r in s1.ephemeralIndirectionTable.Repr :: fresh(r) || r in s0.ephemeralIndirectionTable.Repr; */

        s' := write(k, s1, BT.G.Root(), newroot);
      }
    }
  }

}
