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
  modifies s
  ensures s.W()
  ensures s.ready
  // ensures WellUpdated(s)
  ensures s == old(s)
  ensures s.Repr() == old(s.Repr())
  // NOALIAS statically enforced no-aliasing would probably help here
  ensures forall o | o in s.lru.Repr :: o in old(s.lru.Repr) || fresh(o)
  ensures forall o | o in s.ephemeralIndirectionTable.Repr :: o in old(s.ephemeralIndirectionTable.Repr) || fresh(o)
  ensures forall o | o in s.blockAllocator.Repr :: o in old(s.blockAllocator.Repr) || fresh(o)
  ensures (
    var (mS, mRef) := ImplModelCache.getFreeRef(old(s.I()));
    && mS == s.I()
    && mRef == ref)
  {
    // ImplModelCache.reveal_getFreeRef();

    if (s.nextFreeRef < 0xffff_ffff_ffff_ffff) {
      ref := Some(s.nextFreeRef);
      s.nextFreeRef := s.nextFreeRef + 1;
    } else {
      ref := None;
    }
  }

  method get2FreeRefs(s: ImplVariables)
  returns (refs : Option<(BT.G.Reference, BT.G.Reference)>)
  requires s.ready
  requires s.W()
  modifies s
  ensures s.W()
  ensures s.ready
  ensures s.Repr == old(s.Repr)
  ensures (
    var (mS, mRefs) := ImplModelCache.get2FreeRefs(old(s.I()));
    && mS == s.I()
    && mRefs == refs)
  {
    // ImplModelCache.reveal_get2FreeRefs();

    if (s.nextFreeRef < (0xffff_ffff_ffff_ffff - 1)) {
      var ref1 := s.nextFreeRef;
      var ref2 := ref1 + 1;
      refs := Some((ref1, ref2));
      s.nextFreeRef := s.nextFreeRef + 2;
    } else {
      refs := None;
    }
  }

  method writeBookkeeping(k: ImplConstants, s: ImplVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  requires s.W()
  requires |LruModel.I(s.lru.Queue)| <= 0x1_0000_0000
  requires ImplModelCache.WriteAllocConditions(Ic(k), s.I())
  requires ImplModelCache.ChildrenConditions(Ic(k), s.I(), children)
  requires |s.ephemeralIndirectionTable.I().graph| < IndirectionTableModel.MaxSize()
  modifies s.lru.Repr
  modifies s.ephemeralIndirectionTable.Repr
  modifies s.blockAllocator.Repr
  ensures s.W()
  ensures s.I() == ImplModelCache.writeBookkeeping(Ic(k), old(s.I()), ref, children)
  ensures forall o | o in s.lru.Repr :: o in old(s.lru.Repr) || fresh(o)
  ensures forall o | o in s.ephemeralIndirectionTable.Repr :: o in old(s.ephemeralIndirectionTable.Repr) || fresh(o)
  ensures forall o | o in s.blockAllocator.Repr :: o in old(s.blockAllocator.Repr) || fresh(o)
  ensures |LruModel.I(s.lru.Queue)| <= |LruModel.I(old(s.lru.Queue))| + 1
  {
    ImplModelCache.reveal_writeBookkeeping();

    ImplModelCache.lemmaIndirectionTableLocIndexValid(Ic(k), s.I(), ref);

    var oldLoc := s.ephemeralIndirectionTable.UpdateAndRemoveLoc(ref, (if children.Some? then children.value else []));

    s.lru.Use(ref);

    if oldLoc.Some? {
      s.blockAllocator.MarkFreeEphemeral(oldLoc.value.addr / BlockSizeUint64());
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
  requires ImplModelCache.WriteAllocConditions(Ic(k), s.I())
  requires ref in s.ephemeralIndirectionTable.I().graph
  modifies s.lru.Repr
  modifies s.ephemeralIndirectionTable.Repr
  modifies s.blockAllocator.Repr
  ensures s.W()
  ensures s.I() == ImplModelCache.writeBookkeepingNoSuccsUpdate(Ic(k), old(s.I()), ref)
  ensures forall o | o in s.lru.Repr :: o in old(s.lru.Repr) || fresh(o)
  ensures forall o | o in s.ephemeralIndirectionTable.Repr :: o in old(s.ephemeralIndirectionTable.Repr) || fresh(o)
  ensures forall o | o in s.blockAllocator.Repr :: o in old(s.blockAllocator.Repr) || fresh(o)
  ensures |LruModel.I(s.lru.Queue)| <= |LruModel.I(old(s.lru.Queue))| + 1
  {
    ImplModelCache.reveal_writeBookkeepingNoSuccsUpdate();

    ImplModelCache.lemmaIndirectionTableLocIndexValid(Ic(k), s.I(), ref);

    var oldLoc := s.ephemeralIndirectionTable.RemoveLoc(ref);

    s.lru.Use(ref);

    if oldLoc.Some? {
      s.blockAllocator.MarkFreeEphemeral(oldLoc.value.addr / BlockSizeUint64());
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
  requires ImplModelCache.WriteAllocConditions(Ic(k), s.I())
  requires ImplModelCache.ChildrenConditions(Ic(k), s.I(), children)
  requires |s.ephemeralIndirectionTable.I().graph| < IndirectionTableModel.MaxSize()
  modifies s
  modifies s.lru.Repr
  modifies s.ephemeralIndirectionTable.Repr
  modifies s.blockAllocator.Repr
  ensures s.ready
  ensures s.W()
  ensures (s.I(), ref) == ImplModelCache.allocBookkeeping(Ic(k), old(s.I()), children)
  ensures forall o | o in s.lru.Repr :: o in old(s.lru.Repr) || fresh(o)
  ensures forall o | o in s.ephemeralIndirectionTable.Repr :: o in old(s.ephemeralIndirectionTable.Repr) || fresh(o)
  ensures forall o | o in s.blockAllocator.Repr :: o in old(s.blockAllocator.Repr) || fresh(o)
  ensures |LruModel.I(s.lru.Queue)| <= |LruModel.I(old(s.lru.Queue))| + 1
  {
    ImplModelCache.reveal_allocBookkeeping();
    
    ref := getFreeRef(s);
    if (ref.Some?) {
      writeBookkeeping(k, s, ref.value, children);
    }
  }
}
