include "Impl.i.dfy"
include "ImplIO.i.dfy"
include "ImplCache.i.dfy"
include "ImplModelInsert.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "../lib/Option.s.dfy"
include "../lib/Sets.i.dfy"
include "PivotBetreeSpec.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplInsert { 
  import opened Impl
  import opened ImplIO
  import opened ImplCache
  import opened ImplModelInsert
  import opened ImplState

  import opened Options
  import opened Maps
  import opened Sets
  import opened Sequences

  import opened BucketsLib

  import opened PBS = PivotBetreeSpec`Spec

  method RemoveLBAFromIndirectionTable(table: IS.MutIndirectionTable, ref: IS.Reference)
  requires table.Inv()
  ensures table.Inv()
  ensures table.Contents == ImplModelInsert.removeLBAFromIndirectionTable(old(table.Contents), ref)
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
  requires IS.Inv(k, s)
  requires s.Ready?
  requires BT.G.Root() in s.cache
  ensures IS.WVars(s')
  ensures (IS.IVars(s'), success) == ImplModelInsert.InsertKeyValue(IS.Ic(k), old(IS.IVars(s)), key, value)
  modifies s.ephemeralIndirectionTable.Repr
  {
    ImplModelInsert.reveal_InsertKeyValue();

    if s.frozenIndirectionTable.Some? {
      var rootInFrozenLbaGraph := s.frozenIndirectionTable.value.Get(BT.G.Root());
      if (
        && (s.frozenIndirectionTable.Some? && rootInFrozenLbaGraph.Some?)
        && rootInFrozenLbaGraph.value.0.None?
      ) {
        // TODO write out the root here instead of giving up
        s' := s;
        success := false;
        print "giving up; can't dirty root when frozen is not written yet\n";
        return;
      }
    }

    var msg := Messages.Define(value);
    var newRootBucket := TTT.Insert(s.rootBucket, key, msg);

    // TODO how do we deal with this?
    assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;

    RemoveLBAFromIndirectionTable(s.ephemeralIndirectionTable, BT.G.Root());

    s' := s.(rootBucket := newRootBucket);
    success := true;
  }

  method insert(k: ImplConstants, s: ImplVariables, io: DiskIOHandler, key: MS.Key, value: MS.Value)
  returns (s': ImplVariables, success: bool)
  requires io.initialized()
  requires IS.Inv(k, s)
  ensures IS.WVars(s')
  ensures (IS.IVars(s'), success, IS.IIO(io)) == ImplModelInsert.insert(Ic(k), old(IS.IVars(s)), old(IS.IIO(io)), key, value)
  modifies io
  modifies if s.Ready? then s.ephemeralIndirectionTable.Repr else {}
  {
    ImplModelInsert.reveal_insert();

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
  }
}
