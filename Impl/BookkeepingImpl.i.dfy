include "IOImpl.i.dfy"
// include "BookkeepingModel.i.dfy"

module BookkeepingImpl { 
  import opened IOImpl
  import opened StateBCImpl
  import opened DiskOpImpl
  // import BookkeepingModel
  import LruModel

  import opened Options
  import opened MainDiskIOHandler
  import opened Maps
  import opened Sequences
  import opened Sets
  import opened NativeTypes
  import IndirectionTable

  import opened Bounds
  import opened NodeImpl

  import SSM = StateSectorModel

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
  {
    var i := s.ephemeralIndirectionTable.GetRefUpperBound();
    if i == 0xffff_ffff_ffff_ffff {
      return None;
    }

    i := i + 1;

    while true
    invariant i >= 1
    invariant forall r | r in s.ephemeralIndirectionTable.I().graph :: r < i
    decreases 0x1_0000_0000_0000_0000 - i as int
    {
      var cacheLookup := s.cache.InCache(i);
      if !cacheLookup {
        // assert RefAvailable(s, i);
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

  ensures s.Ready?
  ensures s.W()
  ensures ref.Some? ==> ref.value != avoid;
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  ensures forall ref1 | ref1 in s.cache.I() :: Some(ref1) != ref
  {
    var i := s.ephemeralIndirectionTable.GetRefUpperBound();
    if i == 0xffff_ffff_ffff_ffff {
      return None;
    }

    i := i + 1;

    while true
    invariant i >= 1
    invariant forall r | r in s.ephemeralIndirectionTable.I().graph :: r < i
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

  // Conditions that will hold intermediately between writes and allocs
  predicate WriteAllocConditions(s: ImplVariables)
  {
    && s.WFBCVars()

    && s.Ready?
    && s.blockAllocator.Inv()
    && s.ephemeralIndirectionTable.Inv()
    && s.ephemeralIndirectionTable.TrackingGarbage()
    // && (forall loc |
    //     loc in s.ephemeralIndirectionTable.I().locs.Values :: 
    //       DiskLayout.ValidNodeLocation(loc))
    && ConsistentBitmap(s.ephemeralIndirectionTable.I(), s.frozenIndirectionTable.Map((x: IT.IndirectionTable) => x.I()),
        s.persistentIndirectionTable.I(), s.outstandingBlockWrites, s.blockAllocator.I())
    && BlockAllocatorModel.Inv(s.blockAllocator.I())
    // && BC.AllLocationsForDifferentRefsDontOverlap(
    //     s.ephemeralIndirectionTable.I())
    && s.IBlockCache().WriteAllocConditions()
  }

  predicate ChildrenConditions(s: ImplVariables, succs: Option<seq<BT.G.Reference>>)
  requires s.Ready?
  requires s.W()
  {
    succs.Some? ==> (
      && |succs.value| <= MaxNumChildren()
      && IT.IndirectionTable.SuccsValid(succs.value, s.ephemeralIndirectionTable.graph)
    )
  }

  lemma lemmaIndirectionTableLocIndexValid(s: ImplVariables, ref: BT.G.Reference)
  requires s.W()
  requires WriteAllocConditions(s)
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

  lemma freeIndirectionTableLocCorrect(
      s: ImplVariables, s': ImplVariables, ref: BT.G.Reference, j: Option<int>)
  requires WriteAllocConditions(s)
  requires s'.Ready?
  requires s'.blockAllocator.Inv()
  requires forall r | r != ref ::
      MapsAgreeOnKey(
          s.ephemeralIndirectionTable.I().locs,
          s'.ephemeralIndirectionTable.I().locs,
          r)
  requires ref !in s'.ephemeralIndirectionTable.I().locs
  requires j.Some? ==> 0 <= j.value < NumBlocks()
  requires j.Some? ==> ref in s.ephemeralIndirectionTable.I().locs
  requires j.Some? ==> s.ephemeralIndirectionTable.I().locs[ref].addr as int == j.value * NodeBlockSize()
  requires j.Some? ==> s'.blockAllocator.I() == BlockAllocatorModel.MarkFreeEphemeral(s.blockAllocator.I(), j.value)
  requires j.None? ==> s'.blockAllocator.I() == s.blockAllocator.I()
  requires j.None? ==> ref !in s.ephemeralIndirectionTable.I().locs
  ensures (forall i: int :: IT.IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i)
      <==> IT.IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.I().ephemeral, i))
  ensures BlockAllocatorModel.Inv(s'.blockAllocator.I())
  ensures BC.AllLocationsForDifferentRefsDontOverlap(
        s'.ephemeralIndirectionTable.I())
  ensures (forall loc |
        loc in s'.ephemeralIndirectionTable.I().locs.Values :: 
          DiskLayout.ValidNodeLocation(loc))
  {
    assume false;
    // reveal_ConsistentBitmap();
    // BitmapModel.reveal_IsSet();
    // BitmapModel.reveal_BitUnset();
    // lemmaIndirectionTableLocIndexValid(s, ref);

    // forall r1, r2 | r1 in s'.ephemeralIndirectionTable.I().locs && r2 in s'.ephemeralIndirectionTable.I().locs
    // ensures BC.LocationsForDifferentRefsDontOverlap(s'.ephemeralIndirectionTable.I(), r1, r2)
    // {
    //   assert MapsAgreeOnKey( s.ephemeralIndirectionTable.I().locs, s'.ephemeralIndirectionTable.I().locs, r1);
    //   assert MapsAgreeOnKey( s.ephemeralIndirectionTable.I().locs, s'.ephemeralIndirectionTable.I().locs, r2);
    // }

    // forall loc | loc in s'.ephemeralIndirectionTable.I().locs.Values
    // ensures DiskLayout.ValidNodeLocation(loc)
    // {
    //   var r :| r in s'.ephemeralIndirectionTable.I().locs && s'.ephemeralIndirectionTable.I().locs[r] == loc;
    //   assert MapsAgreeOnKey(s.ephemeralIndirectionTable.I().locs, s'.ephemeralIndirectionTable.I().locs, r);
    // }

    // if j.Some? {
    //   assert DiskLayout.ValidNodeLocation(s.ephemeralIndirectionTable.I().locs[ref]);
    //   assert j.value >= MinNodeBlockIndex() by {
    //     DiskLayout.reveal_ValidNodeAddr();
    //   }
    // }

    // forall i: int
    // | IT.IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i)
    // ensures IT.IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.ephemeral, i)
    // {
    //   if j.Some? && i == j.value {
    //     if 0 <= i < MinNodeBlockIndex() {
    //       assert false;
    //     } else {
    //       var r :| r in s'.ephemeralIndirectionTable.locs &&
    //           s'.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
    //       assert MapsAgreeOnKey(
    //         s.ephemeralIndirectionTable.I().locs,
    //         s'.ephemeralIndirectionTable.I().locs, r);

    //       assert BC.LocationsForDifferentRefsDontOverlap(s.ephemeralIndirectionTable.I(), ref, r);

    //       assert ref !in s'.ephemeralIndirectionTable.I().locs;
    //       assert r in s'.ephemeralIndirectionTable.I().locs;
    //       assert s.ephemeralIndirectionTable.I().locs[r]
    //           == s.ephemeralIndirectionTable.I().locs[ref];
    //       assert r == ref;

    //       assert false;
    //     }
    //   } else {
    //     if 0 <= i < MinNodeBlockIndex() {
    //       assert IT.IndirectionTable.IsLocAllocIndirectionTable(s.ephemeralIndirectionTable.I(), i);
    //       assert IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
    //       assert IT.IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.ephemeral, i);
    //     } else {
    //       var r :| r in s'.ephemeralIndirectionTable.locs &&
    //           s'.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
    //       assert MapsAgreeOnKey(
    //         s.ephemeralIndirectionTable.I().locs,
    //         s'.ephemeralIndirectionTable.I().locs, r);
    //       assert IT.IndirectionTable.IsLocAllocIndirectionTable(s.ephemeralIndirectionTable.I(), i);
    //       assert IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
    //       assert IT.IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.ephemeral, i);
    //     }
    //   }
    // }

    // forall i: int
    // | IT.IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.ephemeral, i)
    // ensures IT.IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i)
    // {
    //   if j.Some? && i == j.value {
    //     assert IT.IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i);
    //   } else {
    //     assert IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.ephemeral, i);
    //     assert IT.IndirectionTable.IsLocAllocIndirectionTable(s.ephemeralIndirectionTable.I(), i);
    //     if 0 <= i < MinNodeBlockIndex() {
    //       assert IT.IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i);
    //     } else {
    //       var r :| r in s.ephemeralIndirectionTable.locs &&
    //         s.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
    //       assert MapsAgreeOnKey(
    //         s.ephemeralIndirectionTable.I().locs,
    //         s'.ephemeralIndirectionTable.I().locs, r);
    //       assert r in s'.ephemeralIndirectionTable.locs &&
    //         s'.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
    //       assert IT.IndirectionTable.IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable.I(), i);
    //     }
    //   }
    // }

    // if j.Some? {
    //   forall i | 0 <= i < NumBlocks()
    //   ensures BitmapModel.IsSet(s'.blockAllocator.full, i) == (
    //     || BitmapModel.IsSet(s'.blockAllocator.ephemeral, i)
    //     || (s'.blockAllocator.frozen.Some? && BitmapModel.IsSet(s'.blockAllocator.frozen.value, i))
    //     || BitmapModel.IsSet(s'.blockAllocator.persistent, i)
    //     || BitmapModel.IsSet(s'.blockAllocator.full, i)
    //   )
    //   {
    //     if i == j.value {
    //     } else {
    //       assert BitmapModel.IsSet(s'.blockAllocator.full, i) == BitmapModel.IsSet(s.blockAllocator.full, i);
    //       assert BitmapModel.IsSet(s'.blockAllocator.ephemeral, i) == BitmapModel.IsSet(s.blockAllocator.ephemeral, i);
    //       assert s'.blockAllocator.frozen.Some? ==> BitmapModel.IsSet(s'.blockAllocator.frozen.value, i) == BitmapModel.IsSet(s.blockAllocator.frozen.value, i);
    //       assert BitmapModel.IsSet(s'.blockAllocator.persistent, i) == BitmapModel.IsSet(s.blockAllocator.persistent, i);
    //       assert BitmapModel.IsSet(s'.blockAllocator.outstanding, i) == BitmapModel.IsSet(s.blockAllocator.outstanding, i);
    //     }
    //   }
    // } else {
    // }
  }

  method writeBookkeeping(linear inout s: ImplVariables, ref: BT.G.Reference, children: Option<seq<BT.G.Reference>>)
  requires old_s.W()
  requires old_s.Ready?
  requires |LruModel.I(old_s.lru.Queue())| <= 0x1_0000_0000
  requires WriteAllocConditions(old_s)
  requires ChildrenConditions(old_s, children)
  requires |old_s.ephemeralIndirectionTable.I().graph| < IndirectionTable.MaxSize()

  ensures s.Ready?
  ensures s.W()
  ensures |LruModel.I(s.lru.Queue())| <= |LruModel.I(old_s.lru.Queue())| + 1
  ensures s.cache.I() == old_s.cache.I()
  ensures s.totalCacheSize() == old_s.totalCacheSize();
  ensures WriteAllocConditions(s)
  ensures |s.ephemeralIndirectionTable.graph| <= |old_s.ephemeralIndirectionTable.graph| + 1

  ensures forall children1 :: ChildrenConditions(old_s, children1) ==> ChildrenConditions(s, children1)
  ensures forall childrenValue:: ChildrenConditions(old_s, Some(childrenValue)) ==> (
        forall i :: 0 <= i < |childrenValue| ==> ChildrenConditions(s, Some(childrenValue[i := ref])))
  ensures forall ref2 :: ref2 in old_s.ephemeralIndirectionTable.I().graph ==>  ref2 in s.ephemeralIndirectionTable.I().graph
  ensures ref in s.ephemeralIndirectionTable.I().graph
  ensures ChildrenConditions(s, Some([ref]))
  ensures LruModel.I(s.lru.Queue()) == LruModel.I(old_s.lru.Queue()) + {ref}
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
    
    freeIndirectionTableLocCorrect(old_s, s, ref,
      if oldLoc.Some?
      then Some(oldLoc.value.addr as int / NodeBlockSize())
      else None);
    reveal_ConsistentBitmap();
  }

  method writeBookkeepingNoSuccsUpdate(linear inout s: ImplVariables, ref: BT.G.Reference)
  requires old_s.W()
  requires old_s.Ready?

  requires |LruModel.I(old_s.lru.Queue())| <= 0x1_0000_0000
  requires WriteAllocConditions(old_s)
  requires ref in old_s.ephemeralIndirectionTable.I().graph

  ensures s.W()
  ensures s.Ready?
  ensures |LruModel.I(s.lru.Queue())| <= |LruModel.I(old_s.lru.Queue())| + 1
  ensures WriteAllocConditions(s)
  ensures |s.ephemeralIndirectionTable.graph| <= |old_s.ephemeralIndirectionTable.graph| + 1
  // [yizhou7] post condition probably not strong enough
  {
    lemmaIndirectionTableLocIndexValid(s, ref);

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

    freeIndirectionTableLocCorrect(old_s, s, ref,
      if oldLoc.Some?
      then Some(oldLoc.value.addr as int / NodeBlockSize())
      else None);
    reveal_ConsistentBitmap();
  }

  method allocBookkeeping(linear inout s: ImplVariables, children: Option<seq<BT.G.Reference>>)
  returns (ref: Option<BT.G.Reference>)
  requires old_s.W()
  requires old_s.Ready?
  requires |LruModel.I(old_s.lru.Queue())| <= 0x1_0000_0000
  requires WriteAllocConditions(old_s)
  requires ChildrenConditions(old_s, children)
  requires |old_s.ephemeralIndirectionTable.I().graph| < IndirectionTable.MaxSize()
  ensures s.Ready?
  ensures s.W()
  ensures |LruModel.I(s.lru.Queue())| <= |LruModel.I(old_s.lru.Queue())| + 1
  ensures s.cache.I() == old_s.cache.I()
  ensures s.totalCacheSize() == old_s.totalCacheSize();
  ensures WriteAllocConditions(s)
  ensures |s.ephemeralIndirectionTable.graph| <= |old_s.ephemeralIndirectionTable.graph| + 1
  ensures ref.Some? ==> ChildrenConditions(s, Some([ref.value]))
  ensures ref.Some? ==> (forall ref2 :: ref2 in old_s.cache.I() ==> ref.value != ref2)
  ensures ref.Some? ==> (ref.value !in old_s.cache.I())
  ensures ref.Some? ==> 
      (
        forall childrenValue:: ChildrenConditions(old_s, Some(childrenValue)) ==> (
        forall i :: 0 <= i < |childrenValue| ==> ChildrenConditions(s, Some(childrenValue[i := ref.value])))
      )
  ensures ref.Some? ==> (LruModel.I(s.lru.Queue()) == LruModel.I(old_s.lru.Queue()) + {ref.value})
  ensures ref.None? ==> (LruModel.I(s.lru.Queue()) == LruModel.I(old_s.lru.Queue()))
  {
    ref := getFreeRef(s);
    if ref.Some? {
      writeBookkeeping(inout s, ref.value, children);
    }
  }

  lemma lemmaChildrenConditionsOfNode(
      s: ImplVariables, ref: BT.G.Reference)
  requires s.Ready?
  requires s.BCInv()
  requires ref in s.cache.I()
  requires ref in s.ephemeralIndirectionTable.graph
  ensures ChildrenConditions(s, s.cache.I()[ref].children)
  // {
  //   if s.cache[ref].children.Some? {
  //     forall r | r in s.cache[ref].children.value
  //     ensures r in s.ephemeralIndirectionTable.graph
  //     {
  //       // Trigger the forall in CacheConsistentWithSuccessors
  //       assert r in BT.G.Successors(INode(s.cache[ref]));
  //       assert r in s.ephemeralIndirectionTable.graph[ref];
  //     }
  //   }
  // }

  // method writeWithNode(linear inout s: ImplVariables, ref: BT.G.Reference, linear node: Node)
  // requires old_s.WFBCVars()
  // requires old_s.Ready?
  // requires old_s.totalCacheSize() <= MaxCacheSize()
  
  // requires WriteAllocConditions(old_s)
  // requires ChildrenConditions(old_s, node.children)
  // requires |old_s.ephemeralIndirectionTable.graph| < IT.MaxSize()
  // requires |LruModel.I(old_s.lru.Queue())| <= 0x1_0000_0000
  // requires node.Inv()
  // requires SSM.WFNode(node.I())

  // requires ref in old_s.ephemeralIndirectionTable.I().graph
  // requires ref in old_s.cache.I()

  // requires BC.BlockPointsToValidReferences(node.I(), old_s.ephemeralIndirectionTable.I().graph)
  // requires old_s.frozenIndirectionTable.lSome? && ref in old_s.frozenIndirectionTable.value.graph ==> ref in old_s.frozenIndirectionTable.value.locs

  // ensures s.WFBCVars()
  // ensures s.Ready?

  // ensures BC.Dirty(old_s.IBlockCache(), s.IBlockCache(), ref, node.I())
  // ensures old_s.TotalCacheSize() == s.TotalCacheSize()

  // ensures WriteAllocConditions(s)
  // ensures |s.ephemeralIndirectionTable.graph| <= |old_s.ephemeralIndirectionTable.graph| + 1
  // {
  //   lemmaIndirectionTableLocIndexValid(s, ref);
  //   var oldLoc := inout s.ephemeralIndirectionTable.UpdateAndRemoveLoc(ref, (if node.children.Some? then node.children.value else []));

  //   inout s.lru.Use(ref);

  //   if oldLoc.Some? {
  //     inout s.blockAllocator.MarkFreeEphemeral(oldLoc.value.addr / NodeBlockSizeUint64());
  //   }

  //   inout s.cache.Insert(ref, node);

  //   LruModel.LruUse(old_s.lru.Queue(), ref);
  //   assert LruModel.I(s.lru.Queue()) == LruModel.I(old_s.lru.Queue()) + {ref};
  //   assert |LruModel.I(s.lru.Queue())| == |LruModel.I(old_s.lru.Queue()) + {ref}|
  //       <= |LruModel.I(old_s.lru.Queue())| + |{ref}|
  //       == |LruModel.I(old_s.lru.Queue())| + 1;
    
  //   freeIndirectionTableLocCorrect(old_s, s, ref,
  //     if oldLoc.Some?
  //     then Some(oldLoc.value.addr as int / NodeBlockSize())
  //     else None);
  //   reveal_ConsistentBitmap();

  //   assert s.WFBCVars();
  // }
}
