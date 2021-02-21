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

  predicate RefAvailable(s: ImplVariables, ref: BT.G.Reference)
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

  ensures var gs := s.IBlockCache();
    && (forall r | r in gs.ephemeralIndirectionTable.graph :: r <= gs.ephemeralIndirectionTable.refUpperBound)
    && ref == BookkeepingModel.getFreeRef(gs);
  {
    BookkeepingModel.reveal_getFreeRef();

    ghost var getable := s.IBlockCache().ephemeralIndirectionTable;

    assert forall r | r in getable.graph :: r <= getable.refUpperBound by {
      s.ephemeralIndirectionTable.UpperBounded();
      assert forall r | r in s.ephemeralIndirectionTable.graph :: r <= s.ephemeralIndirectionTable.refUpperBound;
    }

    var i := s.ephemeralIndirectionTable.GetRefUpperBound();
    if i == 0xffff_ffff_ffff_ffff {
      return None;
    }

    i := i + 1;

    while true
    invariant i >= 1
    invariant forall r | r in s.ephemeralIndirectionTable.graph :: r < i
    invariant BookkeepingModel.getFreeRefIterate(s.IBlockCache(), i)
           == BookkeepingModel.getFreeRef(s.IBlockCache())
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

  ensures ref.Some? ==> ref.value != avoid;
  ensures ref.Some? ==> RefAvailable(s, ref.value)
  ensures forall ref1 | ref1 in s.cache.I() :: Some(ref1) != ref

  ensures var gs := s.IBlockCache();
    && (forall r | r in gs.ephemeralIndirectionTable.graph :: r <= gs.ephemeralIndirectionTable.refUpperBound)
    && ref == BookkeepingModel.getFreeRef2(gs, avoid);
  {
    BookkeepingModel.reveal_getFreeRef2();

    ghost var getable := s.IBlockCache().ephemeralIndirectionTable;

    assert forall r | r in getable.graph :: r <= getable.refUpperBound by {
      s.ephemeralIndirectionTable.UpperBounded();
      assert forall r | r in s.ephemeralIndirectionTable.graph :: r <= s.ephemeralIndirectionTable.refUpperBound;
    }

    var i := s.ephemeralIndirectionTable.GetRefUpperBound();
    if i == 0xffff_ffff_ffff_ffff {
      return None;
    }

    i := i + 1;

    while true
    invariant i >= 1
    invariant forall r | r in s.ephemeralIndirectionTable.I().graph :: r < i
    invariant BookkeepingModel.getFreeRef2Iterate(s.IBlockCache(), avoid, i)
           == BookkeepingModel.getFreeRef2(s.IBlockCache(), avoid)
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

  lemma freeIndirectionTableLocCorrect(
      s: ImplVariables, s': ImplVariables, ref: BT.G.Reference, j: Option<int>)
  requires s.WriteAllocConditions()
  requires s.W()
  requires s'.W()
  requires s'.Ready?
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
  requires j.None? ==> s'.blockAllocator == s.blockAllocator
  requires j.None? ==> ref !in s.ephemeralIndirectionTable.I().locs
  ensures (forall i: int :: s'.ephemeralIndirectionTable.I().IsLocAllocIndirectionTable(i)
      <==> IT.IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.I().ephemeral, i))
  ensures BlockAllocatorModel.Inv(s'.blockAllocator.I())
  ensures BC.AllLocationsForDifferentRefsDontOverlap(
        s'.ephemeralIndirectionTable.I())
  ensures (forall loc |
        loc in s'.ephemeralIndirectionTable.I().locs.Values :: 
          DiskLayout.ValidNodeLocation(loc))
  {
    reveal_ConsistentBitmap();
    BitmapModel.reveal_IsSet();
    BitmapModel.reveal_BitUnset();
    lemmaIndirectionTableLocIndexValid(s, ref);

    forall r1, r2 | r1 in s'.ephemeralIndirectionTable.I().locs && r2 in s'.ephemeralIndirectionTable.I().locs
    ensures BC.LocationsForDifferentRefsDontOverlap(s'.ephemeralIndirectionTable.I(), r1, r2)
    {
      assert MapsAgreeOnKey( s.ephemeralIndirectionTable.I().locs, s'.ephemeralIndirectionTable.I().locs, r1);
      assert MapsAgreeOnKey( s.ephemeralIndirectionTable.I().locs, s'.ephemeralIndirectionTable.I().locs, r2);
    }

    forall loc | loc in s'.ephemeralIndirectionTable.I().locs.Values
    ensures DiskLayout.ValidNodeLocation(loc)
    {
      var r :| r in s'.ephemeralIndirectionTable.I().locs && s'.ephemeralIndirectionTable.I().locs[r] == loc;
      assert MapsAgreeOnKey(s.ephemeralIndirectionTable.I().locs, s'.ephemeralIndirectionTable.I().locs, r);
    }

    if j.Some? {
      assert DiskLayout.ValidNodeLocation(s.ephemeralIndirectionTable.I().locs[ref]);
      assert j.value >= MinNodeBlockIndex() by {
        DiskLayout.reveal_ValidNodeAddr();
      }
    }

    forall i: int
    | s'.ephemeralIndirectionTable.I().IsLocAllocIndirectionTable(i)
    ensures IT.IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.I().ephemeral, i)
    {
      if j.Some? && i == j.value {
        if 0 <= i < MinNodeBlockIndex() {
          assert false;
        } else {
          var r :| r in s'.ephemeralIndirectionTable.locs &&
              s'.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          assert MapsAgreeOnKey(
            s.ephemeralIndirectionTable.I().locs,
            s'.ephemeralIndirectionTable.I().locs, r);

          assert BC.LocationsForDifferentRefsDontOverlap(s.ephemeralIndirectionTable.I(), ref, r);

          assert ref !in s'.ephemeralIndirectionTable.I().locs;
          assert r in s'.ephemeralIndirectionTable.I().locs;
          assert s.ephemeralIndirectionTable.I().locs[r]
              == s.ephemeralIndirectionTable.I().locs[ref];
          assert r == ref;

          assert false;
        }
      } else {
        if 0 <= i < MinNodeBlockIndex() {
          assert s.ephemeralIndirectionTable.I().IsLocAllocIndirectionTable(i);
          assert IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.I().ephemeral, i);
          assert IT.IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.I().ephemeral, i);
        } else {
          var r :| r in s'.ephemeralIndirectionTable.locs &&
              s'.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          assert MapsAgreeOnKey(
            s.ephemeralIndirectionTable.I().locs,
            s'.ephemeralIndirectionTable.I().locs, r);
          assert s.ephemeralIndirectionTable.I().IsLocAllocIndirectionTable(i);
          assert IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.I().ephemeral, i);
          assert IT.IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.I().ephemeral, i);
        }
      }
    }

    forall i: int
    | IT.IndirectionTable.IsLocAllocBitmap(s'.blockAllocator.I().ephemeral, i)
    ensures s'.ephemeralIndirectionTable.I().IsLocAllocIndirectionTable(i)
    {
      if j.Some? && i == j.value {
        assert s'.ephemeralIndirectionTable.I().IsLocAllocIndirectionTable(i);
      } else {
        assert IT.IndirectionTable.IsLocAllocBitmap(s.blockAllocator.I().ephemeral, i);
        assert s.ephemeralIndirectionTable.I().IsLocAllocIndirectionTable(i);
        if 0 <= i < MinNodeBlockIndex() {
          assert s'.ephemeralIndirectionTable.I().IsLocAllocIndirectionTable(i);
        } else {
          var r :| r in s.ephemeralIndirectionTable.locs &&
            s.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          assert MapsAgreeOnKey(
            s.ephemeralIndirectionTable.I().locs,
            s'.ephemeralIndirectionTable.I().locs, r);
          assert r in s'.ephemeralIndirectionTable.locs &&
            s'.ephemeralIndirectionTable.locs[r].addr as int == i * NodeBlockSize() as int;
          assert s'.ephemeralIndirectionTable.I().IsLocAllocIndirectionTable(i);
        }
      }
    }

    if j.Some? {
      forall i | 0 <= i < NumBlocks()
      ensures BitmapModel.IsSet(s'.blockAllocator.I().full, i) == (
        || BitmapModel.IsSet(s'.blockAllocator.I().ephemeral, i)
        || (s'.blockAllocator.I().frozen.Some? && BitmapModel.IsSet(s'.blockAllocator.I().frozen.value, i))
        || BitmapModel.IsSet(s'.blockAllocator.I().persistent, i)
        || BitmapModel.IsSet(s'.blockAllocator.I().full, i)
      )
      {
        if i == j.value {
        } else {
          assert BitmapModel.IsSet(s'.blockAllocator.I().full, i) == BitmapModel.IsSet(s.blockAllocator.I().full, i);
          assert BitmapModel.IsSet(s'.blockAllocator.I().ephemeral, i) == BitmapModel.IsSet(s.blockAllocator.I().ephemeral, i);
          assert s'.blockAllocator.I().frozen.Some? ==> BitmapModel.IsSet(s'.blockAllocator.I().frozen.value, i) == BitmapModel.IsSet(s.blockAllocator.I().frozen.value, i);
          assert BitmapModel.IsSet(s'.blockAllocator.I().persistent, i) == BitmapModel.IsSet(s.blockAllocator.I().persistent, i);
          assert BitmapModel.IsSet(s'.blockAllocator.I().outstanding, i) == BitmapModel.IsSet(s.blockAllocator.I().outstanding, i);
        }
      }
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

  ensures s.WriteAllocConditions()
  ensures s.ChildrenConditions(Some([ref]))
  ensures s.IBlockCache() == BookkeepingModel.writeBookkeeping(old_s.IBlockCache(), ref, children)
  ensures s.cache == old_s.cache
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

    freeIndirectionTableLocCorrect(old_s, s, ref,
      if oldLoc.Some?
      then Some(oldLoc.value.addr as int / NodeBlockSize())
      else None);
    reveal_ConsistentBitmap();
    assert s.WriteAllocConditions();
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
  ensures ref.Some? ==> s.ChildrenConditions(Some([ref.value]))
  ensures s.WriteAllocConditions()

  ensures (s.IBlockCache(), ref) == BookkeepingModel.allocBookkeeping(old_s.IBlockCache(), children)
  ensures ref.None? ==> s == old_s
  {
    BookkeepingModel.reveal_allocBookkeeping();
    
    ref := getFreeRef(s);
    if (ref.Some?) {
      writeBookkeeping(inout s, ref.value, children);
    }
  }

  method writeBookkeepingNoSuccsUpdate(linear inout s: ImplVariables, ref: BT.G.Reference)
  requires old_s.W()
  requires old_s.Ready?
  requires |LruModel.I(old_s.lru.Queue())| <= 0x1_0000_0000
  requires old_s.WriteAllocConditions()
  requires ref in old_s.ephemeralIndirectionTable.I().graph
  ensures s.W()
  ensures s.IBlockCache() == BookkeepingModel.writeBookkeepingNoSuccsUpdate(old_s.IBlockCache(), ref)
  ensures |LruModel.I(s.lru.Queue())| <= |LruModel.I(old_s.lru.Queue())| + 1
  {
    BookkeepingModel.reveal_writeBookkeepingNoSuccsUpdate();

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
  }
}