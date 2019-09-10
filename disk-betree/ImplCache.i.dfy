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
        var cacheLookup := s.cache.Get(i);
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
          var cacheLookup := s.cache.Get(i);
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

  method write(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, node: IS.Node)
  requires s.ready
  requires s.W()
  //requires s.Repr() !! NodeRepr(node)
  requires forall i | 0 <= i < |node.buckets| :: node.buckets[i].Repr !! s.Repr()
  requires BucketListReprInv(node.buckets)
  requires forall i | 0 <= i < |node.buckets| :: node.buckets[i].Inv()
  modifies s.Repr()
  ensures s.ready
  ensures s.W()
  ensures (forall o | o in s.Repr() :: o in old(s.Repr()) || o in NodeRepr(node) || fresh(o))
  ensures s.I() == ImplModelCache.write(Ic(k), old(s.I()), ref, INode(node))
  {
    ImplModelCache.reveal_write();

    // TODO how do we deal with this?
    assume s.ephemeralIndirectionTable.Count as nat < 0x10000000000000000 / 8;
    var _ := s.ephemeralIndirectionTable.Insert(ref, (None, if node.children.Some? then node.children.value else []));

    assume |LruModel.I(s.lru.Queue)| <= 0x10000;
    assume |s.cache.Contents| <= MaxCacheSize();

    //ghost var blah := s.cache.Repr;

    s.lru.Use(ref);
    var _ := s.cache.Insert(ref, node);

    /*forall o | o in CacheRepr(s.cache.Contents)
    ensures o in old(CacheRepr(s.cache.Contents)) || o in old(NodeRepr(node));
    {
      var r: BT.G.Reference, i: int :| r in s.cache.Contents && 0 <= i < |s.cache.Contents[r].buckets| && o in s.cache.Contents[r].buckets[i].Repr;
      if (r == ref) {
        assert o in old(NodeRepr(node));
      } else {
        assert o in old(CacheRepr(s.cache.Contents));
      }
    }*/

    /*forall r, i | r in s.cache.Contents && 0 <= i < |s.cache.Contents[r].buckets|
    ensures s.cache.Contents[r].buckets[i].Inv()
    {
      if (r == ref) {
        assert s.cache.Contents[r].buckets[i].Inv();
      } else {
        assert s.cache.Contents[r].buckets[i]
            == old(s.cache.Contents[r].buckets[i]);
        assert old(s.cache.Contents[r].buckets[i].Inv());
        assert s.cache.Contents[r].buckets[i].Repr <= old(CacheRepr(s.cache.Contents));
        assert s.cache.Contents[r].buckets[i].Repr !! old(s.cache.Repr);
        assert old(CacheRepr(s.cache.Contents)) !! old(s.ephemeralIndirectionTable.Repr);
        assert s.cache.Contents[r].buckets[i].Repr !! old(s.ephemeralIndirectionTable.Repr);
        assert s.cache.Contents[r].buckets[i].Repr !! old(s.lru.Repr);
        assert s.cache.Contents[r].buckets[i].Repr !! blah;
        assert s.cache.Contents[r].buckets[i].Inv();
      }
    }*/

    /*forall ref1, i1, ref2, i2 | ref1 in s.cache.Contents && ref2 in s.cache.Contents
          && 0 <= i1 < |s.cache.Contents[ref1].buckets|
          && 0 <= i2 < |s.cache.Contents[ref2].buckets|
          && (ref1 != ref2 || i1 != i2) ensures
          s.cache.Contents[ref1].buckets[i1].Repr !! s.cache.Contents[ref2].buckets[i2].Repr
    {
      if (ref1 == ref) {
        assert s.cache.Contents[ref1].buckets[i1].Repr <= NodeRepr(node);
      }
      if (ref2 == ref) {
        assert s.cache.Contents[ref2].buckets[i2].Repr <= NodeRepr(node);
      }

      /*if (ref1 == ref) {
        if (ref2 == ref) {
          assert s.cache.Contents[ref1].buckets[i1].Repr !! s.cache.Contents[ref2].buckets[i2].Repr;
        } else {
          assert s.cache.Contents[ref1].buckets[i1].Repr !! s.cache.Contents[ref2].buckets[i2].Repr;
        }
      } else {
        if (ref2 == ref) {
          assert s.cache.Contents[ref1].buckets[i1].Repr !! s.cache.Contents[ref2].buckets[i2].Repr;
        } else {
          assert s.cache.Contents[ref1].buckets[i1].Repr !! s.cache.Contents[ref2].buckets[i2].Repr;
        }
      }*/
    }*/

    //assert s.W();
    //assert s.I().cache == ImplModelCache.write(Ic(k), old(s.I()), ref, INode(node)).cache;
  }

  method alloc(k: ImplConstants, s: ImplVariables, node: IS.Node)
  returns (ref: Option<BT.G.Reference>)
  requires s.ready
  requires s.W()
  modifies s.Repr()
  requires s.Repr() !! NodeRepr(node)
  requires BucketListReprInv(node.buckets)
  requires forall i | 0 <= i < |node.buckets| :: node.buckets[i].Inv()
  ensures s.ready
  ensures s.W()
  ensures (forall o | o in s.Repr() :: o in old(s.Repr()) || o in NodeRepr(node) || fresh(o))
  ensures (s.I(), ref) == ImplModelCache.alloc(Ic(k), old(s.I()), INode(node))
  {
    ImplModelCache.reveal_alloc();
    
    ref := getFreeRef(s);
    if (ref.Some?) {
      write(k, s, ref.value, node);
    }
  }
}
