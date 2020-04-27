include "IOImpl.i.dfy"
include "BookkeepingModel.i.dfy"

module BookkeepingImpl { 
  import opened IOImpl
  import opened StateImpl
  import opened DiskOpImpl
  import BookkeepingModel
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
  ensures ref == BookkeepingModel.getFreeRef(s.I())
  {
    BookkeepingModel.reveal_getFreeRef();

    var i := s.ephemeralIndirectionTable.GetRefUpperBound();
    if i == 0xffff_ffff_ffff_ffff {
      return None;
    }

    i := i + 1;

    while true
    invariant i >= 1
    invariant forall r | r in s.ephemeralIndirectionTable.I().graph :: r < i
    invariant BookkeepingModel.getFreeRefIterate(s.I(), i)
           == BookkeepingModel.getFreeRef(s.I())
    decreases 0x1_0000_0000_0000_0000 - i as int
    {
      var cacheLookup := s.cache.GetOpt(i);
      if cacheLookup.None? {
        return Some(i);
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
  ensures ref == BookkeepingModel.getFreeRef2(s.I(), avoid)
  ensures ref.Some? ==> ref.value != avoid;
  {
    BookkeepingModel.reveal_getFreeRef2();

    var i := s.ephemeralIndirectionTable.GetRefUpperBound();
    if i == 0xffff_ffff_ffff_ffff {
      return None;
    }

    i := i + 1;

    while true
    invariant i >= 1
    invariant forall r | r in s.ephemeralIndirectionTable.I().graph :: r < i
    invariant BookkeepingModel.getFreeRef2Iterate(s.I(), avoid, i)
           == BookkeepingModel.getFreeRef2(s.I(), avoid)
    decreases 0x1_0000_0000_0000_0000 - i as int
    {
      if i != avoid {
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

  method writeBookkeeping(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  requires s.W()
  requires |LruModel.I(s.lru.Queue)| <= 0x1_0000_0000
  requires BookkeepingModel.WriteAllocConditions(Ic(k), s.I())
  requires BookkeepingModel.ChildrenConditions(Ic(k), s.I(), children)
  requires |s.ephemeralIndirectionTable.I().graph| < IndirectionTableModel.MaxSize()
  modifies s.lru.Repr
  modifies s.ephemeralIndirectionTable.Repr
  modifies s.blockAllocator.Repr
  ensures s.W()
  ensures s.I() == BookkeepingModel.writeBookkeeping(Ic(k), old(s.I()), ref, children)
  ensures forall o | o in s.lru.Repr :: o in old(s.lru.Repr) || fresh(o)
  ensures forall o | o in s.ephemeralIndirectionTable.Repr :: o in old(s.ephemeralIndirectionTable.Repr) || fresh(o)
  ensures forall o | o in s.blockAllocator.Repr :: o in old(s.blockAllocator.Repr) || fresh(o)
  ensures |LruModel.I(s.lru.Queue)| <= |LruModel.I(old(s.lru.Queue))| + 1
  {
    BookkeepingModel.reveal_writeBookkeeping();

    BookkeepingModel.lemmaIndirectionTableLocIndexValid(Ic(k), s.I(), ref);

    var oldLoc := s.ephemeralIndirectionTable.UpdateAndRemoveLoc(ref, (if children.Some? then children.value else []));

    s.lru.Use(ref);

    if oldLoc.Some? {
      s.blockAllocator.MarkFreeEphemeral(oldLoc.value.addr / NodeBlockSizeUint64());
    }

    LruModel.LruUse(old(s.lru.Queue), ref);
    assert LruModel.I(s.lru.Queue) == LruModel.I(old(s.lru.Queue)) + {ref};
    assert |LruModel.I(s.lru.Queue)| == |LruModel.I(old(s.lru.Queue)) + {ref}|
        <= |LruModel.I(old(s.lru.Queue))| + |{ref}|
        == |LruModel.I(old(s.lru.Queue))| + 1;
  }

  method writeBookkeepingNoSuccsUpdate(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference)
  requires s.W()
  requires |LruModel.I(s.lru.Queue)| <= 0x1_0000_0000
  requires BookkeepingModel.WriteAllocConditions(Ic(k), s.I())
  requires ref in s.ephemeralIndirectionTable.I().graph
  modifies s.lru.Repr
  modifies s.ephemeralIndirectionTable.Repr
  modifies s.blockAllocator.Repr
  ensures s.W()
  ensures s.I() == BookkeepingModel.writeBookkeepingNoSuccsUpdate(Ic(k), old(s.I()), ref)
  ensures forall o | o in s.lru.Repr :: o in old(s.lru.Repr) || fresh(o)
  ensures forall o | o in s.ephemeralIndirectionTable.Repr :: o in old(s.ephemeralIndirectionTable.Repr) || fresh(o)
  ensures forall o | o in s.blockAllocator.Repr :: o in old(s.blockAllocator.Repr) || fresh(o)
  ensures |LruModel.I(s.lru.Queue)| <= |LruModel.I(old(s.lru.Queue))| + 1
  {
    BookkeepingModel.reveal_writeBookkeepingNoSuccsUpdate();

    BookkeepingModel.lemmaIndirectionTableLocIndexValid(Ic(k), s.I(), ref);

    var oldLoc := s.ephemeralIndirectionTable.RemoveLoc(ref);

    s.lru.Use(ref);

    if oldLoc.Some? {
      s.blockAllocator.MarkFreeEphemeral(oldLoc.value.addr / NodeBlockSizeUint64());
    }

    LruModel.LruUse(old(s.lru.Queue), ref);
    assert LruModel.I(s.lru.Queue) == LruModel.I(old(s.lru.Queue)) + {ref};
    assert |LruModel.I(s.lru.Queue)| == |LruModel.I(old(s.lru.Queue)) + {ref}|
        <= |LruModel.I(old(s.lru.Queue))| + |{ref}|
        == |LruModel.I(old(s.lru.Queue))| + 1;
  }


  method allocBookkeeping(k: ImplConstants, s: ImplVariables, children: Option<seq<BT.G.Reference>>)
  returns (ref: Option<BT.G.Reference>)
  requires s.W()
  requires |LruModel.I(s.lru.Queue)| <= 0x1_0000_0000
  requires BookkeepingModel.WriteAllocConditions(Ic(k), s.I())
  requires BookkeepingModel.ChildrenConditions(Ic(k), s.I(), children)
  requires |s.ephemeralIndirectionTable.I().graph| < IndirectionTableModel.MaxSize()
  modifies s.lru.Repr
  modifies s.ephemeralIndirectionTable.Repr
  modifies s.blockAllocator.Repr
  ensures s.ready
  ensures s.W()
  ensures (s.I(), ref) == BookkeepingModel.allocBookkeeping(Ic(k), old(s.I()), children)
  ensures forall o | o in s.lru.Repr :: o in old(s.lru.Repr) || fresh(o)
  ensures forall o | o in s.ephemeralIndirectionTable.Repr :: o in old(s.ephemeralIndirectionTable.Repr) || fresh(o)
  ensures forall o | o in s.blockAllocator.Repr :: o in old(s.blockAllocator.Repr) || fresh(o)
  ensures |LruModel.I(s.lru.Queue)| <= |LruModel.I(old(s.lru.Queue))| + 1
  {
    BookkeepingModel.reveal_allocBookkeeping();
    
    ref := getFreeRef(s);
    if (ref.Some?) {
      writeBookkeeping(k, s, ref.value, children);
    }
  }
}
