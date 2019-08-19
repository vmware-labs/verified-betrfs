include "ImplModelCache.i.dfy"

module ImplGrow { 
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelCache

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened NativeTypes

  /// The root was found to be too big: grow
  function fixBigRoot(k: Constants, s: Variables, io: IO)
  : (Variables, IO)
  requires Inv(k, s)
  requires s.Ready?
  requires io.IOInit?
  requires s.rootBucket == map[]
  {
    if (BT.G.Root() !in s.cache) then (
      PageInReq(k, s, io, BT.G.Root())
    ) else if (
      && s.frozenIndirectionTable.Some?
      && BT.G.Root() in s.frozenIndirectionTable.value
      && var entry := s.frozenIndirectionTable.value[BT.G.Root()];
      && var (loc, _) := entry;
      && loc.None?
    ) then (
      (s, io)
    ) else (
      var oldroot := s.cache[BT.G.Root()];
      var (s1, newref) := alloc(k, s, oldroot);
      match newref {
        case None => (
          (s1, io)
        )
        case Some(newref) => (
          var newroot := Node([], Some([newref]), [KMTable.Empty()]);
          var s' := write(k, s1, BT.G.Root(), newroot);
          (s', io)
        )
      }
    )
  }

  lemma fixBigRootCorrect(k: Constants, s: Variables, io: IO)
  requires Inv(k, s)
  requires s.Ready?
  requires io.IOInit?
  requires s.rootBucket == map[]
  ensures var (s', io') := fixBigRoot(k, s, io);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    if (BT.G.Root() !in s.cache) {
      PageInReqCorrect(k, s, io, BT.G.Root());
      return;
    }

    INodeRootEqINodeForEmptyRootBucket(s.cache[BT.G.Root()]);

    if (
      && s.frozenIndirectionTable.Some?
      && BT.G.Root() in s.frozenIndirectionTable.value
      && var entry := s.frozenIndirectionTable.value[BT.G.Root()];
      && var (loc, _) := entry;
      && loc.None?
    ) {
      assert noop(k, IVars(s), IVars(s));
      return;
    }

    var oldroot := s.cache[BT.G.Root()];
    var (s1, newref) := alloc(k, s, oldroot);
    reveal_alloc();
    reveal_write();

    match newref {
      case None => {
        assert noop(k, IVars(s), IVars(s1));
      }
      case Some(newref) => {
        var newroot := Node([], Some([newref]), [KMTable.Empty()]);

        assert BT.G.Root() in s.cache;
        assert BT.G.Root() in ICache(s.cache, s.rootBucket);
        assert BT.G.Root() in ICache(s1.cache, s1.rootBucket);
        assert BT.G.Root() in s1.cache;

        var s' := write(k, s1, BT.G.Root(), newroot);

        allocCorrect(k, s, oldroot);
        writeCorrect(k, s1, BT.G.Root(), newroot);

        var growth := BT.RootGrowth(INode(oldroot), newref);
        assert INode(newroot) == BT.G.Node([], Some([growth.newchildref]), [map[]]);
        var step := BT.BetreeGrow(growth);
        BC.MakeTransaction2(Ik(k), IVars(s), IVars(s1), IVars(s'), BT.BetreeStepOps(step));
        assert stepsBetree(k, IVars(s), IVars(s'), UI.NoOp, step);
      }
    }
  }
}
