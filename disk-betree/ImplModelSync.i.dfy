include "ImplModel.i.dfy"
include "ImplModelIO.i.dfy"
include "ImplModelDealloc.i.dfy"
include "../lib/Option.s.dfy"
include "../lib/Sets.i.dfy"

// See dependency graph in MainImpl.dfy

module ImplModelSync { 
  import opened ImplModel
  import opened ImplModelIO
  import opened ImplModelCache
  import opened ImplModelDealloc
  import opened Bounds

  import IMM = ImplMarshallingModel

  import opened Options
  import opened Maps
  import opened Sequences
  import opened Sets

  import opened BucketsLib

  import opened NativeTypes

  lemma lemmaRefHasLoc(k: Constants, s: Variables, ref: BT.G.Reference)
  requires Inv(k, s)
  requires s.Ready?
  requires ref !in s.cache
  requires ref in s.ephemeralIndirectionTable.contents
  ensures s.ephemeralIndirectionTable.contents[ref].0.Some?;
  {
    assert ref in IIndirectionTable(s.ephemeralIndirectionTable).graph.Keys;
    assert ref in s.cache.Keys + IIndirectionTable(s.ephemeralIndirectionTable).locs.Keys;
    assert ref !in s.cache.Keys;
    assert ref in IIndirectionTable(s.ephemeralIndirectionTable).locs.Keys;
  }

  function {:opaque} AssignRefToLocEphemeral(k: Constants, s: Variables, ref: BT.G.Reference, loc: BC.Location) : (s' : Variables)
  requires s.Ready?
  requires MutableMapModel.Inv(s.ephemeralIndirectionTable)
  requires BlockAllocator.Inv(s.blockAllocator)
  requires 0 <= loc.addr as int / BlockSize() < NumBlocks()
  ensures s'.Ready?
  ensures s'.frozenIndirectionTable == s.frozenIndirectionTable
  ensures s'.blockAllocator.frozen == s.blockAllocator.frozen
  ensures s'.outstandingBlockWrites == s.outstandingBlockWrites
  ensures BlockAllocator.Inv(s'.blockAllocator)
  {
    var table := s.ephemeralIndirectionTable;
    if (ref in table.contents && table.contents[ref].0.None?) then (
      assume table.count as nat < 0x10000000000000000 / 8;
      var table' := MutableMapModel.Insert(table, ref, (Some(loc), table.contents[ref].1));
      var blockAllocator' := BlockAllocator.MarkUsedEphemeral(s.blockAllocator, loc.addr as int / BlockSize());
      var s' := s
        .(ephemeralIndirectionTable := table')
        .(blockAllocator := blockAllocator');
      s'
    ) else (
      s
    )
  }

  function {:opaque} AssignRefToLocFrozen(k: Constants, s: Variables, ref: BT.G.Reference, loc: BC.Location) : (s' : Variables)
  requires s.Ready?
  requires s.frozenIndirectionTable.Some? ==> MutableMapModel.Inv(s.frozenIndirectionTable.value)
  requires s.frozenIndirectionTable.Some? ==> s.blockAllocator.frozen.Some?
  requires BlockAllocator.Inv(s.blockAllocator)
  requires 0 <= loc.addr as int / BlockSize() < NumBlocks()
  ensures s'.Ready?
  ensures s'.outstandingBlockWrites == s.outstandingBlockWrites
  ensures BlockAllocator.Inv(s'.blockAllocator)
  {
    if s.frozenIndirectionTable.Some? then (
      var table := s.frozenIndirectionTable.value;
      if (ref in table.contents && table.contents[ref].0.None?) then (
        assume table.count as nat < 0x10000000000000000 / 8;
        var table' := MutableMapModel.Insert(table, ref, (Some(loc), table.contents[ref].1));
        var blockAllocator' := BlockAllocator.MarkUsedFrozen(s.blockAllocator, loc.addr as int / BlockSize());
        var s' := s
          .(frozenIndirectionTable := Some(table'))
          .(blockAllocator := blockAllocator');
        s'
      ) else (
        s
      )
    ) else (
      s
    )
  }

  function {:opaque} AssignIdRefLocOutstanding(k: Constants, s: Variables, id: D.ReqId, ref: BT.G.Reference, loc: BC.Location) : (s' : Variables)
  requires s.Ready?
  requires BlockAllocator.Inv(s.blockAllocator)
  requires 0 <= loc.addr as int / BlockSize() < NumBlocks()
  {
     s
      .(outstandingBlockWrites := s.outstandingBlockWrites[id := BC.OutstandingWrite(ref, loc)])
      .(blockAllocator := BlockAllocator.MarkUsedOutstanding(s.blockAllocator, loc.addr as int / BlockSize()))
  }

  lemma LemmaAssignIdRefLocOutstandingCorrect(k: Constants, s: Variables, id: D.ReqId, ref: BT.G.Reference, loc: BC.Location)
  requires s.Ready?
  requires (forall i: int :: IsLocAllocOutstanding(s.outstandingBlockWrites, i)
          <==> IsLocAllocBitmap(s.blockAllocator.outstanding, i))
  requires BlockAllocator.Inv(s.blockAllocator)
  requires BC.ValidLocationForNode(loc);
  requires 0 <= loc.addr as int / BlockSize() < NumBlocks()
  requires id !in s.outstandingBlockWrites
  ensures var s' := AssignIdRefLocOutstanding(k, s, id, ref, loc);
      && s'.Ready?
      && (forall i: int :: IsLocAllocOutstanding(s'.outstandingBlockWrites, i)
          <==> IsLocAllocBitmap(s'.blockAllocator.outstanding, i))
      && BlockAllocator.Inv(s'.blockAllocator)
  {
    reveal_AssignIdRefLocOutstanding();
    Bitmap.reveal_BitSet();
    Bitmap.reveal_IsSet();

    var s' := AssignIdRefLocOutstanding(k, s, id, ref, loc);

    var j := loc.addr as int / BlockSize();
    LBAType.reveal_ValidAddr();
    assert j != 0;
    assert j * BlockSize() == loc.addr as int;

    forall i: int
    | IsLocAllocOutstanding(s'.outstandingBlockWrites, i)
    ensures IsLocAllocBitmap(s'.blockAllocator.outstanding, i)
    {
      if i != j {
        assert IsLocAllocOutstanding(s.outstandingBlockWrites, i);
        assert IsLocAllocBitmap(s.blockAllocator.outstanding, i);
        assert IsLocAllocBitmap(s'.blockAllocator.outstanding, i);
      } else {
        assert IsLocAllocBitmap(s'.blockAllocator.outstanding, i);
      }
    }

    forall i: int
    | IsLocAllocBitmap(s'.blockAllocator.outstanding, i)
    ensures IsLocAllocOutstanding(s'.outstandingBlockWrites, i)
    {
      if i != j {
        assert IsLocAllocBitmap(s.blockAllocator.outstanding, i);
        assert IsLocAllocOutstanding(s.outstandingBlockWrites, i);
        var id0 :| id0 in s.outstandingBlockWrites
          && s.outstandingBlockWrites[id0].loc.addr as int == i * BlockSize() as int;
        assert id0 != id;
        assert id0 in s'.outstandingBlockWrites;
        assert s'.outstandingBlockWrites[id0].loc.addr as int == i * BlockSize() as int;
        assert IsLocAllocOutstanding(s'.outstandingBlockWrites, i);
      } else {
        assert id in s'.outstandingBlockWrites;
        assert s'.outstandingBlockWrites[id].loc.addr as int == i * BlockSize() as int;
        assert IsLocAllocOutstanding(s'.outstandingBlockWrites, i);
      }
    }
  }

  lemma LemmaAssignRefToLocBitmapConsistent(
      indirectionTable: IndirectionTable,
      bm: Bitmap.BitmapModel,
      indirectionTable': IndirectionTable,
      bm': Bitmap.BitmapModel,
      ref: BT.G.Reference,
      loc: BC.Location)
  requires MutableMapModel.Inv(indirectionTable)
  requires (forall i: int :: IsLocAllocIndirectionTable(indirectionTable, i)
          <==> IsLocAllocBitmap(bm, i))
  requires BC.ValidLocationForNode(loc);
  requires 0 <= loc.addr as int / BlockSize() < NumBlocks()
  requires indirectionTable.count as nat < 0x10000000000000000 / 8;
  requires ref in indirectionTable.contents
  requires indirectionTable.contents[ref].0.None?
  requires indirectionTable' == MutableMapModel.Insert(indirectionTable, ref, (Some(loc), indirectionTable.contents[ref].1));
  requires 0 <= loc.addr as int / BlockSize() < NumBlocks()
  requires Bitmap.Len(bm) == NumBlocks()
  requires bm' == Bitmap.BitSet(bm, loc.addr as int / BlockSize())
  ensures 
      && (forall i: int :: IsLocAllocIndirectionTable(indirectionTable', i)
          <==> IsLocAllocBitmap(bm', i))
  {
    Bitmap.reveal_BitSet();
    Bitmap.reveal_IsSet();

    assert indirectionTable'.contents == indirectionTable.contents[ref := (Some(loc), indirectionTable.contents[ref].1)];

    var j := loc.addr as int / BlockSize();
    LBAType.reveal_ValidAddr();
    assert j != 0;
    assert j * BlockSize() == loc.addr as int;

    forall i: int | IsLocAllocIndirectionTable(indirectionTable', i)
    ensures IsLocAllocBitmap(bm', i)
    {
      if i == j {
        assert IsLocAllocBitmap(bm', i);
      } else {
        assert IsLocAllocIndirectionTable(indirectionTable, i);
        assert IsLocAllocBitmap(bm', i);
      }
    }
    forall i: int | IsLocAllocBitmap(bm', i)
    ensures IsLocAllocIndirectionTable(indirectionTable', i)
    {
      if i == j {
        assert ref in indirectionTable'.contents;
        assert indirectionTable'.contents[ref].0.Some?;
        assert indirectionTable'.contents[ref].0.value.addr as int == i * BlockSize() as int;
        assert IsLocAllocIndirectionTable(indirectionTable', i);
      } else {
        if i == 0 {
          assert IsLocAllocIndirectionTable(indirectionTable', i);
        } else {
          assert IsLocAllocIndirectionTable(indirectionTable, i);
          var r :| r in indirectionTable.contents && indirectionTable.contents[r].0.Some? &&
            indirectionTable.contents[r].0.value.addr as int == i * BlockSize() as int;
          assert MapsAgreeOnKey(
            IIndirectionTable(indirectionTable).locs,
            IIndirectionTable(indirectionTable').locs, r);
          assert r in indirectionTable'.contents && indirectionTable'.contents[r].0.Some? &&
            indirectionTable'.contents[r].0.value.addr as int == i * BlockSize() as int;
          assert IsLocAllocIndirectionTable(indirectionTable', i);
        }
      }
    }
  }

  lemma LemmaAssignRefToLocEphemeralCorrect(k: Constants, s: Variables, ref: BT.G.Reference, loc: BC.Location)
  requires s.Ready?
  requires MutableMapModel.Inv(s.ephemeralIndirectionTable)
  requires (forall i: int :: IsLocAllocIndirectionTable(s.ephemeralIndirectionTable, i)
          <==> IsLocAllocBitmap(s.blockAllocator.ephemeral, i))
  requires BlockAllocator.Inv(s.blockAllocator)
  requires BC.ValidLocationForNode(loc);
  requires 0 <= loc.addr as int / BlockSize() < NumBlocks()
  ensures var s' := AssignRefToLocEphemeral(k, s, ref, loc);
      && s'.Ready?
      && (forall i: int :: IsLocAllocIndirectionTable(s'.ephemeralIndirectionTable, i)
          <==> IsLocAllocBitmap(s'.blockAllocator.ephemeral, i))
      && BlockAllocator.Inv(s'.blockAllocator)
  {
    reveal_AssignRefToLocEphemeral();
    reveal_ConsistentBitmap();
    Bitmap.reveal_BitSet();
    Bitmap.reveal_IsSet();

    var j := loc.addr as int / BlockSize();

    var table := s.ephemeralIndirectionTable;
    if (ref in table.contents && table.contents[ref].0.None?) {
      assume table.count as nat < 0x10000000000000000 / 8;
      var table' := MutableMapModel.Insert(table, ref, (Some(loc), table.contents[ref].1));
      var blockAllocator' := BlockAllocator.MarkUsedEphemeral(s.blockAllocator, loc.addr as int / BlockSize());
      var s' := s
      .(ephemeralIndirectionTable := table')
      .(blockAllocator := blockAllocator');

      forall i | 0 <= i < NumBlocks()
      ensures Bitmap.IsSet(s'.blockAllocator.full, i) == (
        || Bitmap.IsSet(s'.blockAllocator.ephemeral, i)
        || (s'.blockAllocator.frozen.Some? && Bitmap.IsSet(s'.blockAllocator.frozen.value, i))
        || Bitmap.IsSet(s'.blockAllocator.persistent, i)
        || Bitmap.IsSet(s'.blockAllocator.full, i)
      )
      {
        if i != j {
          assert Bitmap.IsSet(s'.blockAllocator.full, i) == Bitmap.IsSet(s.blockAllocator.full, i);
          assert Bitmap.IsSet(s'.blockAllocator.ephemeral, i) == Bitmap.IsSet(s.blockAllocator.ephemeral, i);
          assert s'.blockAllocator.frozen.Some? ==> Bitmap.IsSet(s'.blockAllocator.frozen.value, i) == Bitmap.IsSet(s.blockAllocator.frozen.value, i);
          assert Bitmap.IsSet(s'.blockAllocator.persistent, i) == Bitmap.IsSet(s.blockAllocator.persistent, i);
          assert Bitmap.IsSet(s'.blockAllocator.outstanding, i) == Bitmap.IsSet(s.blockAllocator.outstanding, i);
        }
      }

      LemmaAssignRefToLocBitmapConsistent(
          s.ephemeralIndirectionTable,
          s.blockAllocator.ephemeral,
          s'.ephemeralIndirectionTable, 
          s'.blockAllocator.ephemeral,
          ref,
          loc);
    } else {
    }
  }

  lemma LemmaAssignRefToLocFrozenCorrect(k: Constants, s: Variables, ref: BT.G.Reference, loc: BC.Location)
  requires s.Ready?
  requires s.frozenIndirectionTable.Some? ==> MutableMapModel.Inv(s.frozenIndirectionTable.value)
  requires s.frozenIndirectionTable.Some? ==> s.blockAllocator.frozen.Some?
  requires s.frozenIndirectionTable.Some? ==>
        (forall i: int :: IsLocAllocIndirectionTable(s.frozenIndirectionTable.value, i)
          <==> IsLocAllocBitmap(s.blockAllocator.frozen.value, i))
  requires BlockAllocator.Inv(s.blockAllocator)
  requires BC.ValidLocationForNode(loc);
  requires 0 <= loc.addr as int / BlockSize() < NumBlocks()
  ensures var s' := AssignRefToLocFrozen(k, s, ref, loc);
      && s'.Ready?
      && (s'.frozenIndirectionTable.Some? ==> s'.blockAllocator.frozen.Some?)
      && (s'.frozenIndirectionTable.Some? ==>
          (forall i: int :: IsLocAllocIndirectionTable(s'.frozenIndirectionTable.value, i)
          <==> IsLocAllocBitmap(s'.blockAllocator.frozen.value, i)))
      && BlockAllocator.Inv(s'.blockAllocator)
  {
    reveal_AssignRefToLocFrozen();

    if s.frozenIndirectionTable.None? {
      return;
    }

    reveal_ConsistentBitmap();
    Bitmap.reveal_BitSet();
    Bitmap.reveal_IsSet();

    var j := loc.addr as int / BlockSize();

    var table := s.frozenIndirectionTable.value;
    if (ref in table.contents && table.contents[ref].0.None?) {
      assume table.count as nat < 0x10000000000000000 / 8;
      var table' := MutableMapModel.Insert(table, ref, (Some(loc), table.contents[ref].1));
      var blockAllocator' := BlockAllocator.MarkUsedFrozen(s.blockAllocator, loc.addr as int / BlockSize());
      var s' := s
      .(frozenIndirectionTable := Some(table'))
      .(blockAllocator := blockAllocator');

      forall i | 0 <= i < NumBlocks()
      ensures Bitmap.IsSet(s'.blockAllocator.full, i) == (
        || Bitmap.IsSet(s'.blockAllocator.frozen.value, i)
        || (s'.blockAllocator.frozen.Some? && Bitmap.IsSet(s'.blockAllocator.frozen.value, i))
        || Bitmap.IsSet(s'.blockAllocator.persistent, i)
        || Bitmap.IsSet(s'.blockAllocator.full, i)
      )
      {
        if i != j {
          assert Bitmap.IsSet(s'.blockAllocator.full, i) == Bitmap.IsSet(s.blockAllocator.full, i);
          assert Bitmap.IsSet(s'.blockAllocator.ephemeral, i) == Bitmap.IsSet(s.blockAllocator.ephemeral, i);
          assert s'.blockAllocator.frozen.Some? ==> Bitmap.IsSet(s'.blockAllocator.frozen.value, i) == Bitmap.IsSet(s.blockAllocator.frozen.value, i);
          assert Bitmap.IsSet(s'.blockAllocator.persistent, i) == Bitmap.IsSet(s.blockAllocator.persistent, i);
          assert Bitmap.IsSet(s'.blockAllocator.outstanding, i) == Bitmap.IsSet(s.blockAllocator.outstanding, i);
        }
      }

      LemmaAssignRefToLocBitmapConsistent(
          s.frozenIndirectionTable.value,
          s.blockAllocator.frozen.value,
          s'.frozenIndirectionTable.value,
          s'.blockAllocator.frozen.value,
          ref,
          loc);
    } else {
    }
  }

  function {:opaque} FindRefInFrozenWithNoLoc(s: Variables) : (ref: Option<Reference>)
  requires WFVars(s)
  requires s.Ready?
  requires s.frozenIndirectionTable.Some?

  lemma FindRefInFrozenWithNoLocCorrect(s: Variables)
  requires WFVars(s)
  requires s.Ready?
  requires s.frozenIndirectionTable.Some?
  ensures var ref := FindRefInFrozenWithNoLoc(s);
    && (ref.Some? ==> ref.value in s.frozenIndirectionTable.value.contents)
    && (ref.Some? ==> s.frozenIndirectionTable.value.contents[ref.value].0.None?)
    && (ref.None? ==> forall r | r in s.frozenIndirectionTable.value.contents
        :: s.frozenIndirectionTable.value.contents[r].0.Some?)

  function {:fuel BC.GraphClosed,0} {:fuel BC.CacheConsistentWithSuccessors,0}
  syncNotFrozen(k: Constants, s: Variables, io: IO)
  : (res: (Variables, IO))
  requires io.IOInit?
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable.None?
  {
    var ephemeralTable := s.ephemeralIndirectionTable.contents;
    var ephemeralGraph := map k | k in ephemeralTable :: ephemeralTable[k].1;

    var foundDeallocable := FindDeallocable(s);
    FindDeallocableCorrect(s);

    if foundDeallocable.Some? then (
      Dealloc(k, s, io, foundDeallocable.value)
    ) else (
      var s' := s
          .(frozenIndirectionTable := Some(s.ephemeralIndirectionTable))
          .(syncReqs := BC.syncReqs3to2(s.syncReqs))
          .(blockAllocator := BlockAllocator.CopyEphemeralToFrozen(s.blockAllocator));
      (s', io)
    )
  }

  lemma {:fuel BC.GraphClosed,0} {:fuel BC.CacheConsistentWithSuccessors,0}
  syncNotFrozenCorrect(k: Constants, s: Variables, io: IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable.None?

  ensures var (s', io') := syncNotFrozen(k, s, io);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    var (s', io') := syncNotFrozen(k, s, io);

    var ephemeralTable := s.ephemeralIndirectionTable.contents;
    var ephemeralGraph := map k | k in ephemeralTable :: ephemeralTable[k].1;

    var foundDeallocable := FindDeallocable(s);
    FindDeallocableCorrect(s);

    if foundDeallocable.Some? {
      DeallocCorrect(k, s, io, foundDeallocable.value);
      return;
    }

    reveal_ConsistentBitmap();
    assert WFVars(s');

    assert BC.Freeze(Ik(k), IVars(s), IVars(s'), M.IDiskOp(diskOp(io')));
    assert BBC.BlockCacheMove(Ik(k), IVars(s), IVars(s'), UI.NoOp, M.IDiskOp(diskOp(io')), BC.FreezeStep);
    assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io, BC.FreezeStep);
    return;
  }

  predicate WriteBlockUpdateState(k: Constants, s: Variables, ref: BT.G.Reference,
      id: Option<D.ReqId>, loc: Option<LBAType.Location>, s': Variables)
  requires s.Ready?
  requires Inv(k, s)
  requires loc.Some? ==> 0 <= loc.value.addr as int / BlockSize() < NumBlocks()
  requires ref in s.cache
  {
    reveal_ConsistentBitmap();

    if id.Some? then (
      && loc.Some?
      && var s0 := AssignRefToLocEphemeral(k, s, ref, loc.value);
      && var s1 := AssignRefToLocFrozen(k, s0, ref, loc.value);
      && s' == AssignIdRefLocOutstanding(k, s1, id.value, ref, loc.value)
    ) else (
      && s' == s
    )
  }

  predicate TryToWriteBlock(k: Constants, s: Variables, io: IO, ref: BT.G.Reference,
      s': Variables, io': IO)
  requires s.Ready?
  requires Inv(k, s)
  requires io.IOInit?
  requires ref in s.cache
  {
    exists id, loc ::
      && FindLocationAndRequestWrite(io, s, SectorBlock(s.cache[ref]), id, loc, io')
      && WriteBlockUpdateState(k, s, ref, id, loc, s')
  }

  lemma TryToWriteBlockCorrect(k: Constants, s: Variables, io: IO, ref: BT.G.Reference,
      s': Variables, io': IO)
  requires io.IOInit?
  requires TryToWriteBlock.requires(k, s, io, ref, s', io')
  requires TryToWriteBlock(k, s, io, ref, s', io')
  requires s.outstandingIndirectionTableWrite.None?
  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    var id, loc :| 
      && FindLocationAndRequestWrite(io, s, SectorBlock(s.cache[ref]), id, loc, io')
      && WriteBlockUpdateState(k, s, ref, id, loc, s');

    FindLocationAndRequestWriteCorrect(io, s, SectorBlock(s.cache[ref]), id, loc, io');

    if id.Some? {
      reveal_ConsistentBitmap();
      reveal_AssignRefToLocEphemeral();
      reveal_AssignRefToLocFrozen();
      reveal_AssignIdRefLocOutstanding();

      var s0 := AssignRefToLocEphemeral(k, s, ref, loc.value);
      var s1 := AssignRefToLocFrozen(k, s0, ref, loc.value);

      LemmaAssignRefToLocEphemeralCorrect(k, s, ref, loc.value);
      LemmaAssignRefToLocFrozenCorrect(k, s0, ref, loc.value);
      LemmaAssignIdRefLocOutstandingCorrect(k, s1, id.value, ref, loc.value);

      assert BC.ValidLocationForNode(M.IDiskOp(diskOp(io')).reqWrite.loc);
      assert BC.WriteBackReq(Ik(k), IVars(s), IVars(s'), M.IDiskOp(diskOp(io')), ref);
      assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io', BC.WriteBackReqStep(ref));
    } else {
      assert io == io';
      assert noop(k, IVars(s), IVars(s));
    }
  }

  predicate {:fuel BC.GraphClosed,0} syncFoundInFrozen(k: Constants, s: Variables, io: IO, ref: Reference,
      s': Variables, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable.Some?
  requires ref in s.frozenIndirectionTable.value.contents
  requires s.frozenIndirectionTable.value.contents[ref].0.None?
  {
    assert ref in IIndirectionTable(s.frozenIndirectionTable.value).graph;
    assert ref !in IIndirectionTable(s.frozenIndirectionTable.value).locs;

    if ref in s.ephemeralIndirectionTable.contents && s.ephemeralIndirectionTable.contents[ref].0.Some? then (
      // TODO we should be able to prove this is impossible as well
      && s' == s
      && io' == io
    ) else (
      TryToWriteBlock(k, s, io, ref, s', io')
    )
  }

  lemma {:fuel BC.GraphClosed,0} syncFoundInFrozenCorrect(k: Constants, s: Variables, io: IO, ref: Reference,
      s': Variables, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires s.Ready?
  requires s.outstandingIndirectionTableWrite.None?
  requires s.frozenIndirectionTable.Some?
  requires ref in s.frozenIndirectionTable.value.contents
  requires s.frozenIndirectionTable.value.contents[ref].0.None?

  requires syncFoundInFrozen(k, s, io, ref, s', io')

  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    assert ref in IIndirectionTable(s.frozenIndirectionTable.value).graph;
    assert ref !in IIndirectionTable(s.frozenIndirectionTable.value).locs;

    if ref in s.ephemeralIndirectionTable.contents && s.ephemeralIndirectionTable.contents[ref].0.Some? {
      assert ref in IIndirectionTable(s.ephemeralIndirectionTable).locs;
      assert noop(k, IVars(s), IVars(s));
    } else {
      TryToWriteBlockCorrect(k, s, io, ref, s', io');
    }
  }

  predicate {:opaque} {:fuel BC.GraphClosed,0} sync(k: Constants, s: Variables, io: IO,
      s': Variables, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  {
    if (s.Unready?) then (
      // TODO we could just do nothing here instead
      (s', io') == PageInIndirectionTableReq(k, s, io)
    ) else (
      if (s.outstandingIndirectionTableWrite.Some?) then (
        && s' == s
        && io' == io
      ) else (
        // Plan:
        // - If the indirection table is not frozen then:
        //    - If anything can be unalloc'ed, do it
        // - Otherwise:
        //    - If any block in the frozen table doesn't have an LBA, Write it to disk
        //    - Write the frozenIndirectionTable to disk

        if (s.frozenIndirectionTable.None?) then (
          (s', io') == syncNotFrozen(k, s, io)
        ) else (
          var foundInFrozen := FindRefInFrozenWithNoLoc(s);
          FindRefInFrozenWithNoLocCorrect(s);
          if foundInFrozen.Some? then (
            syncFoundInFrozen(k, s, io, foundInFrozen.value, s', io')
          ) else if (s.outstandingBlockWrites != map[]) then (
            && s' == s
            && io' == io
          ) else (
            if (diskOp(io').ReqWriteOp?) then (
              var id := Some(diskOp(io').id);
              && RequestWrite(io, BC.IndirectionTableLocation(), SectorIndirectionTable(s.frozenIndirectionTable.value), id, io')
              && s' == s.(outstandingIndirectionTableWrite := id)
            ) else (
              && s' == s
              && io' == io
            )
          )
        )
      )
    )
  }

  lemma {:fuel BC.GraphClosed,0} syncCorrect(k: Constants, s: Variables, io: IO,
      s': Variables, io': IO)
  requires io.IOInit?
  requires Inv(k, s)

  requires sync(k, s, io, s', io')

  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    reveal_sync();
    if (s.Unready?) {
      PageInIndirectionTableReqCorrect(k, s, io);
    } else {
      if (s.outstandingIndirectionTableWrite.Some?) {
        assert noop(k, IVars(s), IVars(s));
      } else {
        if (s.frozenIndirectionTable.None?) {
          syncNotFrozenCorrect(k, s, io);
        } else {
          var foundInFrozen := FindRefInFrozenWithNoLoc(s);
          FindRefInFrozenWithNoLocCorrect(s);
          if foundInFrozen.Some? {
            syncFoundInFrozenCorrect(k, s, io, foundInFrozen.value, s', io');
          } else if (s.outstandingBlockWrites != map[]) {
            assert noop(k, IVars(s), IVars(s));
          } else {
            if (diskOp(io').ReqWriteOp?) {
              var id := Some(diskOp(io').id);
              LBAType.reveal_ValidAddr();
              RequestWriteCorrect(io, BC.IndirectionTableLocation(), SectorIndirectionTable(s.frozenIndirectionTable.value), id, io');
              assert BC.WriteBackIndirectionTableReq(Ik(k), IVars(s), IVars(s'), M.IDiskOp(diskOp(io')));
              assert stepsBC(k, IVars(s), IVars(s'), UI.NoOp, io', BC.WriteBackIndirectionTableReqStep);
            } else {
              assert noop(k, IVars(s), IVars(s));
            }
          }
        }
      }
    }
  }

  // == pushSync ==

  function {:opaque} freeId<A>(syncReqs: map<uint64, A>) : (id: uint64)
  ensures id != 0 ==> id !in syncReqs
  {
    var s := syncReqs.Keys;
    if (|s| == 0) then (
      1
    ) else (
      var maxId := maximumInt(syncReqs.Keys);
      maximumIntCorrect(syncReqs.Keys);
      if maxId == 0xffff_ffff_ffff_ffff then (
        0
      ) else (
        maxId + 1
      )
    )
  }

  function pushSync(k: Constants, s: Variables)
  : (Variables, uint64)
  requires Inv(k,s )
  {
    var id := freeId(s.syncReqs);
    if id == 0 then (
      (s, id)
    ) else (
      var s' := s.(syncReqs := s.syncReqs[id := BC.State3]);
      (s', id)
    )
  }

  lemma pushSyncCorrect(k: Constants, s: Variables)
  requires Inv(k, s)
  ensures var (s', id) := pushSync(k, s);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'),
        if id == 0 then UI.NoOp else UI.PushSyncOp(id as int),
        D.NoDiskOp)
  {
    var (s', id) := pushSync(k, s);
    if id == 0 {
      assert noop(k, IVars(s), IVars(s'));
    } else {
      assert M.NextStep(Ik(k), IVars(s), IVars(s'), UI.PushSyncOp(id as int), D.NoDiskOp, M.Step(BBC.BlockCacheMoveStep(BC.PushSyncReqStep(id))));
    }
  }

  // == popSync ==

  predicate popSync(k: Constants, s: Variables, io: IO, id: uint64,
      s': Variables, success: bool, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  {
    if (id in s.syncReqs && s.syncReqs[id] == BC.State1) then (
      && success == true
      && s' == s.(syncReqs := MapRemove1(s.syncReqs, id))
      && io' == io
    ) else (
      && success == false
      && sync(k, s, io, s', io')
    )
  }

  lemma popSyncCorrect(k: Constants, s: Variables, io: IO, id: uint64,
      s': Variables, success: bool, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires popSync(k, s, io, id, s', success, io')
  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'), if success then UI.PopSyncOp(id as int) else UI.NoOp, diskOp(io'))
  {
    if (id in s.syncReqs && s.syncReqs[id] == BC.State1) {
      assert stepsBC(k, IVars(s), IVars(s'), UI.PopSyncOp(id as int), io', BC.PopSyncReqStep(id));
    } else {
      syncCorrect(k, s, io, s', io');
    }
  }
}
