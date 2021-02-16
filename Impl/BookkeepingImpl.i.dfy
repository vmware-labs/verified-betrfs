include "IOImpl.i.dfy"
include "BookkeepingModel.i.dfy"

module BookkeepingImpl { 
  import opened IOImpl
  import opened StateBCImpl
  import opened DiskOpImpl
  import BookkeepingModel
  import LruModel

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets
  import opened NativeTypes
  import IndirectionTable

  import opened Bounds

  predicate RefAvailable(s: ImplVariables, ref: Reference)
    requires s.Ready? && s.W()
  {
    && ref !in s.ephemeralIndirectionTable.I().graph
    && ref !in s.cache.I()
    && ref != BT.G.Root()
  }

  method getFreeRef(shared s: ImplVariables)
  returns (ref : Option<BT.G.Reference>)
  requires s.Ready?
  requires s.W()

  ensures s.Ready?
  ensures s.W()
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  ensures forall ref1 | ref1 in s.cache.I() :: Some(ref1) != ref

  ensures var gs := s.IBlockCache2();
    && (forall r | r in gs.ephemeralIndirectionTable.graph :: r < gs.ephemeralIndirectionTable.refUpperBound)
    && ref == BookkeepingModel.getFreeRef(gs);
  {
    BookkeepingModel.reveal_getFreeRef();

    ghost var getable := s.IBlockCache2().ephemeralIndirectionTable;

    assume forall r | r in getable.graph :: r < getable.refUpperBound;

    var i := s.ephemeralIndirectionTable.GetRefUpperBound();
    if i == 0xffff_ffff_ffff_ffff {
      return None;
    }

    i := i + 1;

    while true
    invariant i >= 1
    invariant forall r | r in s.ephemeralIndirectionTable.graph :: r < i
    invariant BookkeepingModel.getFreeRefIterate(s.IBlockCache2(), i)
           == BookkeepingModel.getFreeRef(s.IBlockCache2())
    decreases 0x1_0000_0000_0000_0000 - i as int
    {
      var cacheLookup := s.cache.InCache(i);
      if !cacheLookup {
        return Some(i);
      }
      
      if i == 0xffff_ffff_ffff_ffff {
        return None;
      } else {
        i := i + 1;
      }
    }
  }

  // method getFreeRef2(shared s: ImplVariables, avoid: BT.G.Reference)
  // returns (ref : Option<BT.G.Reference>)
  // requires s.Ready?
  // requires s.W()

  // ensures ref.Some? ==> ref.value != avoid;
  // ensures ref.Some? ==> RefAvailable(s, ref.value)
  // ensures forall ref1 | ref1 in s.cache.I() :: Some(ref1) != ref
  // {
  //   var i := s.ephemeralIndirectionTable.GetRefUpperBound();
  //   if i == 0xffff_ffff_ffff_ffff {
  //     return None;
  //   }

  //   i := i + 1;

  //   while true
  //   invariant i >= 1
  //   invariant forall r | r in s.ephemeralIndirectionTable.I().graph :: r < i
  //   decreases 0x1_0000_0000_0000_0000 - i as int
  //   {
  //     if i != avoid {
  //       var cacheLookup := s.cache.InCache(i);
  //       if !cacheLookup {
  //         return Some(i);
  //       }
  //     }
      
  //     if i == 0xffff_ffff_ffff_ffff {
  //       return None;
  //     } else {
  //       i := i + 1;
  //     }
  //   }
  // }

  lemma lemmaIndirectionTableLocIndexValid(s: ImplVariables, ref: BT.G.Reference)
  requires s.W()
  requires s.WriteAllocConditions()
  ensures ref in s.ephemeralIndirectionTable.locs ==>
    (
      && 0 <= s.ephemeralIndirectionTable.locs[ref].addr as int / NodeBlockSize() < NumBlocks()
      && (s.ephemeralIndirectionTable.locs[ref].addr as int / NodeBlockSize()) * NodeBlockSize() == s.ephemeralIndirectionTable.locs[ref].addr as int
    )
  {
    if ref in s.ephemeralIndirectionTable.locs {
      reveal_ConsistentBitmap();
      var loc := s.ephemeralIndirectionTable.locs[ref];
      var i := loc.addr as int / NodeBlockSize();
      assert s.ephemeralIndirectionTable.I().locs[ref] == loc;
      assert loc in s.ephemeralIndirectionTable.I().locs.Values;
      assert DiskLayout.ValidNodeLocation(loc);
      DiskLayout.reveal_ValidNodeAddr();
      assert i * NodeBlockSize() == loc.addr as int;
      assert IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.I().ephemeral, i);
    }
  }

  method writeBookkeeping(linear inout s: ImplVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  requires old_s.W()
  requires old_s.Ready?
  requires |LruModel.I(old_s.lru.Queue())| <= 0x1_0000_0000
  requires old_s.WriteAllocConditions()
  requires old_s.ChildrenConditions(children)
  requires |old_s.ephemeralIndirectionTable.I().graph| < IndirectionTable.MaxSize()

  ensures s.W()
  ensures s.Ready?
  ensures |LruModel.I(s.lru.Queue())| <= |LruModel.I(old_s.lru.Queue())| + 1
  ensures s.cache.I() == old_s.cache.I()

  ensures s.IBlockCache2() == BookkeepingModel.writeBookkeeping(old_s.IBlockCache2(), ref, children)
  ensures s.ChildrenConditions(Some([ref]))
  ensures s.WriteAllocConditions()
  {
    lemmaIndirectionTableLocIndexValid(s, ref);
    var oldLoc := inout s.ephemeralIndirectionTable.UpdateAndRemoveLoc(ref, (if children.Some? then children.value else []));

    inout s.lru.Use(ref);

    if oldLoc.Some? {
      inout s.blockAllocator.MarkFreeEphemeral(oldLoc.value.addr / NodeBlockSizeUint64());
    }

    LruModel.LruUse(old_s.lru.Queue(), ref);
    assert LruModel.I(s.lru.Queue()) == LruModel.I(old_s.lru.Queue()) + {ref};
    assert |LruModel.I(s.lru.Queue())| == |LruModel.I(old_s.lru.Queue()) + {ref}|
        <= |LruModel.I(old_s.lru.Queue())| + |{ref}|
        == |LruModel.I(old_s.lru.Queue())| + 1;

    reveal BookkeepingModel.writeBookkeeping();

    assume s.WriteAllocConditions();
    // freeIndirectionTableLocCorrect(old_s, s, ref,
    //   if oldLoc.Some?
    //   then Some(oldLoc.value.addr as int / NodeBlockSize())
    //   else None);
    // reveal_ConsistentBitmap();
  }

  method allocBookkeeping(linear inout s: ImplVariables, children: Option<seq<BT.G.Reference>>)
  returns (ref: Option<BT.G.Reference>)
  requires old_s.W()
  requires old_s.Ready?
  requires |LruModel.I(old_s.lru.Queue())| <= 0x1_0000_0000
  requires old_s.WriteAllocConditions()
  requires old_s.ChildrenConditions(children)
  requires |old_s.ephemeralIndirectionTable.I().graph| < IndirectionTable.MaxSize()
  ensures s.Ready?

  ensures s.W()
  ensures |LruModel.I(s.lru.Queue())| <= |LruModel.I(old_s.lru.Queue())| + 1
  ensures s.cache.I() == old_s.cache.I()
  ensures (s.IBlockCache2(), ref) == BookkeepingModel.allocBookkeeping(old_s.IBlockCache2(), children)
  ensures ref.None? ==> s == old_s

  ensures ref.Some? ==> s.ChildrenConditions(Some([ref.value]))
  ensures s.WriteAllocConditions()
  {
    BookkeepingModel.reveal_allocBookkeeping();
    
    ref := getFreeRef(s);
    if (ref.Some?) {
      writeBookkeeping(inout s, ref.value, children);
    }
  }

/*

  method writeBookkeepingNoSuccsUpdate(linear inout s: ImplVariables, ref: BT.G.Reference)
  requires old_s.W()
  requires old_s.Ready?
  requires |LruModel.I(old_s.lru.Queue())| <= 0x1_0000_0000
  requires BookkeepingModel.WriteAllocConditions(old_s.I())
  requires ref in old_s.ephemeralIndirectionTable.I().graph
  ensures s.W()
  ensures s.I() == BookkeepingModel.writeBookkeepingNoSuccsUpdate(old_s.I(), ref)
  ensures |LruModel.I(s.lru.Queue())| <= |LruModel.I(old_s.lru.Queue())| + 1
  {
    BookkeepingModel.reveal_writeBookkeepingNoSuccsUpdate();

    BookkeepingModel.lemmaIndirectionTableLocIndexValid(s.I(), ref);

    var oldLoc := inout s.ephemeralIndirectionTable.RemoveLoc(ref);

    inout s.lru.Use(ref);

    if oldLoc.Some? {
      inout s.blockAllocator.MarkFreeEphemeral(oldLoc.value.addr / NodeBlockSizeUint64());
    }

    LruModel.LruUse(old_s.lru.Queue(), ref);
    assert LruModel.I(s.lru.Queue()) == LruModel.I(old_s.lru.Queue()) + {ref};
    assert |LruModel.I(s.lru.Queue())| == |LruModel.I(old_s.lru.Queue()) + {ref}|
        <= |LruModel.I(old_s.lru.Queue())| + |{ref}|
        == |LruModel.I(old_s.lru.Queue())| + 1;
  }
  */
}