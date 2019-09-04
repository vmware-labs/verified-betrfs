include "ImplIO.i.dfy"
include "ImplModelCache.i.dfy"

module ImplCache { 
  import opened Impl
  import opened ImplIO
  import opened ImplState
  import ImplModelCache
  import LruModel

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
  {
    ImplModelCache.reveal_getFreeRef();
    var i := 1;
    while true
    invariant i >= 1
    invariant ImplModelCache.getFreeRefIterate(IS.IVars(s), i)
           == ImplModelCache.getFreeRef(IS.IVars(s))
    decreases 0x1_0000_0000_0000_0000 - i as int
    {
      var lookup := s.ephemeralIndirectionTable.Get(i);
      if lookup.None? && i !in s.cache {
        return Some(i);
      } else if i == 0xffff_ffff_ffff_ffff {
        return None;
      } else {
        i := i + 1;
      }
    }
  }

  method getFreeRef2(s: ImplVariables, avoid: BT.G.Reference)
  returns (ref : Option<BT.G.Reference>)
  requires s.Ready?
  requires IS.WVars(s)
  ensures ref == ImplModelCache.getFreeRef2(IS.IVars(s), avoid)
  {
    ImplModelCache.reveal_getFreeRef2();
    var i := 1;
    while true
    invariant i >= 1
    invariant ImplModelCache.getFreeRef2Iterate(IS.IVars(s), avoid, i)
           == ImplModelCache.getFreeRef2(IS.IVars(s), avoid)
    decreases 0x1_0000_0000_0000_0000 - i as int
    {
      var lookup := s.ephemeralIndirectionTable.Get(i);
      if lookup.None? && i != avoid && i !in s.cache {
        return Some(i);
      } else if i == 0xffff_ffff_ffff_ffff {
        return None;
      } else {
        i := i + 1;
      }
    }
  }

  method write(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, node: IS.Node)
  returns (s': ImplVariables)
  requires s.Ready?
  requires IS.WVars(s)
  ensures s'.Ready?
  ensures s'.ephemeralIndirectionTable == s.ephemeralIndirectionTable
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall r | r in s.ephemeralIndirectionTable.Repr :: fresh(r) || r in old(s.ephemeralIndirectionTable.Repr)
  ensures forall r | r in s'.lru.Repr :: fresh(r) || r in old(s.lru.Repr)

  ensures IS.WVars(s')
  ensures IS.IVars(s') == ImplModelCache.write(Ic(k), old(IS.IVars(s)), ref, node)

  modifies s.ephemeralIndirectionTable.Repr
  modifies s.lru.Repr
  {
    ImplModelCache.reveal_write();

    // TODO how do we deal with this?
    assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;
    var _ := s.ephemeralIndirectionTable.Insert(ref, (None, if node.children.Some? then node.children.value else []));

    assume |LruModel.I(s.lru.Queue)| <= 0x10000;
    s.lru.Use(ref);
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
  ensures forall r | r in s'.lru.Repr :: fresh(r) || r in old(s.lru.Repr)

  ensures IS.WVars(s')
  ensures (IS.IVars(s'), ref) == ImplModelCache.alloc(Ic(k), old(IS.IVars(s)), node)

  modifies s.ephemeralIndirectionTable.Repr
  modifies s.lru.Repr
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
