include "ImplCache.i.dfy"
include "ImplModelGrow.i.dfy"

module ImplGrow { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache
  import opened ImplState
  import ImplModelGrow

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened NativeTypes

  /// The root was found to be too big: grow
  method fixBigRoot(k: ImplConstants, s: ImplVariables, io: DiskIOHandler)
  returns (s': ImplVariables)
  requires Inv(k, s)
  requires s.Ready?
  requires io.initialized()
  requires s.rootBucket == TTT.EmptyTree
  modifies io
  ensures IS.WVars(s')
  ensures (IVars(s'), IIO(io)) == ImplModelGrow.fixBigRoot(Ic(k), old(IVars(s)), old(IIO(io)))
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  modifies s.ephemeralIndirectionTable.Repr
  {
    ImplModelGrow.reveal_fixBigRoot();

    if (BT.G.Root() !in s.cache) {
      s' := PageInReq(k, s, io, BT.G.Root());
      return;
    }

    if s.frozenIndirectionTable.Some? {
      var rootLbaGraph := s.frozenIndirectionTable.value.Get(BT.G.Root());
      if rootLbaGraph.Some? {
        var (lba, _) := rootLbaGraph.value;
        if lba.None? {
          s' := s;
          print "giving up; fixBigRoot can't run because frozen isn't written\n";
          return;
        }
      }
    }

    var oldroot := s.cache[BT.G.Root()];
    var s1, newref := alloc(k, s, oldroot);

    // NOALIAS statically enforced no-aliasing would probably help here
    /* (doc) assert forall r | r in s1.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr); */
    /* (doc) assert forall r | r in s1.ephemeralIndirectionTable.Repr :: fresh(r) || r in s.ephemeralIndirectionTable.Repr; */

    match newref {
      case None => {
        s' := s1;
        print "giving up; could not allocate ref\n";
      }
      case Some(newref) => {
        var newroot := IM.Node([], Some([newref]), [KMTable.Empty()]);

        // NOALIAS statically enforced no-aliasing would probably help here
        /* (doc) assert forall r | r in s1.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr); */
        /* (doc) assert forall r | r in s1.ephemeralIndirectionTable.Repr :: fresh(r) || r in s.ephemeralIndirectionTable.Repr; */

        s' := write(k, s1, BT.G.Root(), newroot);
      }
    }
  }

}
