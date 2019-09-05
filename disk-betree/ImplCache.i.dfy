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
  requires s.ready
  requires s.W()
  ensures ref == ImplModelCache.getFreeRef(s.I())
  {
    ImplModelCache.reveal_getFreeRef();
    var i := 1;
    while true
    invariant i >= 1
    invariant ImplModelCache.getFreeRefIterate(s.I(), i)
           == ImplModelCache.getFreeRef(s.I())
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
  requires s.ready
  requires s.W()
  ensures ref == ImplModelCache.getFreeRef2(s.I(), avoid)
  {
    ImplModelCache.reveal_getFreeRef2();
    var i := 1;
    while true
    invariant i >= 1
    invariant ImplModelCache.getFreeRef2Iterate(s.I(), avoid, i)
           == ImplModelCache.getFreeRef2(s.I(), avoid)
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
  requires s.ready
  requires s.W()
  modifies s.Repr()
  ensures s.ready
  ensures WellUpdated(s)
  ensures s.I() == ImplModelCache.write(Ic(k), old(s.I()), ref, node)
  {
    ImplModelCache.reveal_write();

    // TODO how do we deal with this?
    assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;
    var _ := s.ephemeralIndirectionTable.Insert(ref, (None, if node.children.Some? then node.children.value else []));

    assume |LruModel.I(s.lru.Queue)| <= 0x10000;
    s.lru.Use(ref);
    s.cache := s.cache[ref := node];
  }

  method alloc(k: ImplConstants, s: ImplVariables, node: IS.Node)
  returns (ref: Option<BT.G.Reference>)
  requires s.ready
  requires s.W()
  modifies s.Repr()
  ensures s.ready
  ensures WellUpdated(s)
  ensures (s.I(), ref) == ImplModelCache.alloc(Ic(k), old(s.I()), node)
  {
    ImplModelCache.reveal_alloc();
    
    ref := getFreeRef(s);
    if (ref.Some?) {
      write(k, s, ref.value, node);
    }
  }
}
