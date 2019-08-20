include "ImplIO.i.dfy"
include "ImplModelCache.i.dfy"

module ImplCache { 
  import opened Impl
  import opened ImplIO
  import opened ImplState
  import ImplModelCache

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened NativeTypes

  method getFreeRef(s: ImplVariables)
  returns (ref : Option<BT.G.Reference>)
  requires s.Ready?
  requires IS.WVars(s)
  ensures ref == ImplModelCache.getFreeRef(IS.IVars(s))

  method write(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, node: IS.Node)
  returns (s': ImplVariables)
  requires s.Ready?
  requires IS.WVars(s)
  ensures s'.Ready?
  ensures s'.ephemeralIndirectionTable == s.ephemeralIndirectionTable
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)

  ensures IS.WVars(s')
  ensures IS.IVars(s') == ImplModelCache.write(Ic(k), old(IS.IVars(s)), ref, node)

  modifies s.ephemeralIndirectionTable.Repr
  {
    ImplModelCache.reveal_write();

    // TODO how do we deal with this?
    assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;
    var _ := s.ephemeralIndirectionTable.Insert(ref, (None, if node.children.Some? then node.children.value else []));

    s' := s.(cache := s.cache[ref := node]);
  }

  method alloc(k: ImplConstants, s: ImplVariables, node: IS.Node)
  returns (s': ImplVariables, ref: Option<BT.G.Reference>)
  requires s.Ready?
  requires IS.WVars(s)

  ensures s'.Ready?
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures s'.ephemeralIndirectionTable.Repr == s.ephemeralIndirectionTable.Repr
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)

  ensures IS.WVars(s')
  ensures (IS.IVars(s'), ref) == ImplModelCache.alloc(Ic(k), old(IS.IVars(s)), node)

  modifies s.ephemeralIndirectionTable.Repr
  {
    ImplModelCache.reveal_alloc();
    
    ref := getFreeRef(s);
    if (ref.Some?) {
      s' := write(k, s, ref.value, node);
    } else {
      s' := s;
    }
  }
}
