// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

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

  method getFreeRef(shared s: ImplVariables)
  returns (ref : Option<BT.G.Reference>)
  requires s.Ready?
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

  method getFreeRef2(shared s: ImplVariables, avoid: BT.G.Reference)
  returns (ref : Option<BT.G.Reference>)
  requires s.Ready?
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
        var cacheLookup := s.cache.InCache(i);
        if !cacheLookup {
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

  method writeBookkeeping(linear inout s: ImplVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  requires old_s.W()
  requires old_s.Ready?
  requires |LruModel.I(old_s.lru.Queue())| <= 0x1_0000_0000
  requires BookkeepingModel.WriteAllocConditions(old_s.I())
  requires BookkeepingModel.ChildrenConditions(old_s.I(), children)
  requires |old_s.ephemeralIndirectionTable.I().graph| < IndirectionTable.MaxSize()
  ensures s.W()
  ensures s.I() == BookkeepingModel.writeBookkeeping(old_s.I(), ref, children)
  ensures |LruModel.I(s.lru.Queue())| <= |LruModel.I(old_s.lru.Queue())| + 1
  ensures s.cache.I() == old_s.cache.I()
  {
    BookkeepingModel.reveal_writeBookkeeping();

    BookkeepingModel.lemmaIndirectionTableLocIndexValid(s.I(), ref);

    assert s.ephemeralIndirectionTable.TrackingGarbage();
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
  }

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

  method allocBookkeeping(linear inout s: ImplVariables, children: Option<seq<BT.G.Reference>>)
  returns (ref: Option<BT.G.Reference>)
  requires old_s.W()
  requires old_s.Ready?
  requires |LruModel.I(old_s.lru.Queue())| <= 0x1_0000_0000
  requires BookkeepingModel.WriteAllocConditions(old_s.I())
  requires BookkeepingModel.ChildrenConditions(old_s.I(), children)
  requires |old_s.ephemeralIndirectionTable.I().graph| < IndirectionTable.MaxSize()
  ensures s.Ready?
  ensures s.W()
  ensures (s.I(), ref) == BookkeepingModel.allocBookkeeping(old_s.I(), children)
  ensures |LruModel.I(s.lru.Queue())| <= |LruModel.I(old_s.lru.Queue())| + 1
  ensures s.cache.I() == old_s.cache.I()
  {
    BookkeepingModel.reveal_allocBookkeeping();
    
    ref := getFreeRef(s);
    if (ref.Some?) {
      writeBookkeeping(inout s, ref.value, children);
    }
  }
}
