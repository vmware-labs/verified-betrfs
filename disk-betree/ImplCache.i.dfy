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

  import opened Bounds

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
      if lookup.None? {
        var cacheLookup := s.cache.GetOpt(i);
        if cacheLookup.None? {
          return Some(i);
        }
      }
      
      if i == 0xffff_ffff_ffff_ffff {
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
      if i != avoid {
        var lookup := s.ephemeralIndirectionTable.Get(i);
        if lookup.None? {
          var cacheLookup := s.cache.GetOpt(i);
          if cacheLookup.None? {
            return Some(i);
          }
        }
      }
      
      if i == 0xffff_ffff_ffff_ffff {
        return None;
      } else {
        i := i + 1;
      }
    }
  }

  method writeBookkeeping(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  requires s.ready
  requires s.W()
  modifies s.Repr()
  ensures s.ready
  ensures WellUpdated(s)
  ensures s.I() == ImplModelCache.writeBookkeeping(Ic(k), old(s.I()), ref, children)
  ensures s.cache.I() == old(s.cache.I())
  {
    ImplModelCache.reveal_writeBookkeeping();

    // TODO how do we deal with this?
    assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;
    var _ := s.ephemeralIndirectionTable.Insert(ref, (None, if children.Some? then children.value else []));

    assume |LruModel.I(s.lru.Queue)| <= 0x10000;
    assume |s.cache.I()| <= MaxCacheSize();

    s.lru.Use(ref);
  }

  method allocBookkeeping(k: ImplConstants, s: ImplVariables, children: Option<seq<BT.G.Reference>>)
  returns (ref: Option<BT.G.Reference>)
  requires s.ready
  requires s.W()
  modifies s.Repr()
  ensures s.ready
  ensures WellUpdated(s)
  ensures (s.I(), ref) == ImplModelCache.allocBookkeeping(Ic(k), old(s.I()), children)
  ensures s.cache.I() == old(s.cache.I())
  {
    ImplModelCache.reveal_allocBookkeeping();
    
    ref := getFreeRef(s);
    if (ref.Some?) {
      writeBookkeeping(k, s, ref.value, children);
    }
  }
}
