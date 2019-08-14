include "Impl.i.dfy"
include "ImplSync.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Option.s.dfy"
include "../lib/Sets.i.dfy"
include "PivotBetreeSpec.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplDo { 
  import opened Impl
  import opened ImplSync
  import opened ImplIO

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sets
  import opened Sequences

  import opened BucketsLib

  import opened PBS = PivotBetreeSpec`Spec

  // == insert ==

  lemma LemmaInsertToRootBucket(node: IS.Node, rootBucket: IS.TreeMap, rootBucket': IS.TreeMap, key: Key, msg: Message)
  requires IS.WFNode(node)
  requires TTT.TTTree(rootBucket)
  requires TTT.TTTree(rootBucket')
  requires TTT.I(rootBucket') == TTT.I(rootBucket)[key := msg]
  requires BT.WFNode(IS.INodeRoot(node, rootBucket))
  ensures IS.INodeRoot(node, rootBucket') == BT.AddMessageToNode(IS.INodeRoot(node, rootBucket), key, msg)
  {
    assume false;
  }

  method RemoveLBAFromIndirectionTable(table: IS.MutIndirectionTable, ref: IS.Reference)
  requires table.Inv()
  ensures table.Inv()
  ensures table.Contents == if ref in old(table.Contents)
      then old(
        var (_, graph) := table.Contents[ref];
        table.Contents[ref := (None, graph)])
      else old(table.Contents)
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in table.Repr :: fresh(r) || r in old(table.Repr)
  modifies table.Repr
  {
    var lbaGraph := table.Remove(ref);
    if lbaGraph.Some? {
      // TODO how do we deal with this?
      assume table.Count as nat < 0x10000000000000000 / 8;
      var (lba, graph) := lbaGraph.value;
      var _ := table.Insert(ref, (None, graph));
    }
  }

  method InsertKeyValue(k: ImplConstants, s: ImplVariables, key: MS.Key, value: MS.Value)
  returns (s': ImplVariables, success: bool)
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  requires s.Ready?
  requires BT.G.Root() in s.cache
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), if success then UI.PutOp(key, value) else UI.NoOp, D.NoDiskOp)
  modifies s.ephemeralIndirectionTable.Repr
  {
    if s.frozenIndirectionTable.Some? {
      var rootInFrozenLbaGraph := s.frozenIndirectionTable.value.Get(BT.G.Root());
      if (
        && (s.frozenIndirectionTable.Some? && rootInFrozenLbaGraph.Some?)
        && rootInFrozenLbaGraph.value.0.None?
      ) {
        assert (s.frozenIndirectionTable.Some? && BT.G.Root() in IS.IIndirectionTable(s.frozenIndirectionTable.value).graph) &&
            !(BT.G.Root() in IS.IIndirectionTable(s.frozenIndirectionTable.value).locs);
        // TODO write out the root here instead of giving up
        s' := s;
        success := false;
        assert noop(k, IS.IVars(s), IS.IVars(s'));
        print "giving up; can't dirty root when frozen is not written yet\n";
        return;
      }
    }

    var msg := Messages.Define(value);

    ghost var baseroot := s.cache[BT.G.Root()];

    ghost var r := Pivots.Route(baseroot.pivotTable, key);
    ghost var bucket := baseroot.buckets[r];

    assert BC.BlockPointsToValidReferences(IS.INodeRoot(baseroot, s.rootBucket), IS.IIndirectionTable(s.ephemeralIndirectionTable).graph);

    var newRootBucket := TTT.Insert(s.rootBucket, key, msg);

    // TODO how do we deal with this?
    assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;

    ghost var iVarsBeforeRemoval := IS.IVars(s);

    label before_removal: assert true;

    RemoveLBAFromIndirectionTable(s.ephemeralIndirectionTable, BT.G.Root());

    assert IS.IVars(s) == iVarsBeforeRemoval.(ephemeralIndirectionTable := BC.IndirectionTable(
        MapRemove1(iVarsBeforeRemoval.ephemeralIndirectionTable.locs, BT.G.Root()),
        iVarsBeforeRemoval.ephemeralIndirectionTable.graph));

    s' := s.(rootBucket := newRootBucket);
    success := true;

    ghost var oldroot := IS.INodeRoot(baseroot, s.rootBucket);
    ghost var newroot := IS.INodeRoot(baseroot, newRootBucket);

    assert IS.IVars(s') == old@before_removal(IS.IVars(s) // timeout observe
        .(cache := IS.IVars(s).cache[BT.G.Root() := newroot])
        .(ephemeralIndirectionTable := BC.IndirectionTable(
          MapRemove1(IS.IVars(s).ephemeralIndirectionTable.locs, BT.G.Root()),
          IS.IVars(s).ephemeralIndirectionTable.graph
        )));

    LemmaInsertToRootBucket(baseroot, s.rootBucket, newRootBucket, key, msg);
    assert newroot == BT.AddMessageToNode(oldroot, key, msg);

    assert BT.G.Successors(newroot) == BT.G.Successors(oldroot);

    ghost var btStep := BT.BetreeInsert(BT.MessageInsertion(key, msg, oldroot));

    assert BC.Dirty(Ik(k), old(IS.IVars(s)), IS.IVars(s'), BT.G.Root(), newroot);
    assert BC.OpStep(Ik(k), old(IS.IVars(s)), IS.IVars(s'), BT.G.WriteOp(BT.G.Root(), newroot));
    assert BC.OpStep(Ik(k), old(IS.IVars(s)), IS.IVars(s'), BT.BetreeStepOps(btStep)[0]);
    assert BC.OpTransaction(Ik(k), old(IS.IVars(s)), IS.IVars(s'), BT.BetreeStepOps(btStep));
    assert BBC.BetreeMove(Ik(k), old(IS.IVars(s)), IS.IVars(s'), UI.PutOp(key, value), SD.NoDiskOp, btStep);
    assert stepsBetree(k, old(IS.IVars(s)), IS.IVars(s'), UI.PutOp(key, value), btStep);

    if success {
      assert ImplADM.M.NextStep(Ik(k), old(IS.IVars(s)), IS.IVars(s'), if success then UI.PutOp(key, value) else UI.NoOp, D.NoDiskOp,
          ImplADM.M.Step(BBC.BetreeMoveStep(btStep)));
    }
    /* (doc) assert ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'), if success then UI.PutOp(key, value) else UI.NoOp, D.NoDiskOp); */
  }

  method insert(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (s': ImplVariables, success: bool)
  requires io.initialized()
  modifies io
  requires IS.WFVars(s)
  requires BBC.Inv(k, IS.IVars(s))
  ensures IS.WFVars(s')
  ensures ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'),
    if success then UI.PutOp(key, value) else UI.NoOp,
    io.diskOp())
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  {
    if (s.Unready?) {
      s' := PageInIndirectionTableReq(k, s, io);
      success := false;
      return;
    }

    if (BT.G.Root() !in s.cache) {
      s' := PageInReq(k, s, io, BT.G.Root());
      success := false;
      return;
    }

    s', success := InsertKeyValue(k, s, key, value);
    assert ImplADM.M.Next(Ik(k), old(IS.IVars(s)), IS.IVars(s'),
      if success then UI.PutOp(key, value) else UI.NoOp,
      io.diskOp());
  }
}
