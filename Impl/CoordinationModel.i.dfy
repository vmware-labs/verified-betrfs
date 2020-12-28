include "SyncModel.i.dfy"
include "QueryModel.i.dfy"
include "SuccModel.i.dfy"
include "InsertModel.i.dfy"

module CoordinationModel {
  import opened StateModel
  import opened StateBCModel
  import opened StateSectorModel
  import opened Options
  import IOModel
  import SyncModel

  import QueryModel
  import SuccModel
  import InsertModel
  import Journal
  import opened InterpretationDiskOps
  import opened ViewOp
  import opened NativeTypes
  import DiskLayout
  import opened KeyType
  import opened ValueType
  import opened DiskOpModel

  import M = ByteCache

  lemma jcNoOp(s: Variables, s': Variables, vop: VOp)
  requires s.jc.WF()
  requires s.jc == s'.jc
  requires vop.StatesInternalOp? || vop.JournalInternalOp?
      || (vop.AdvanceOp?
        && vop.uiop.NoOp?
        && s.jc.status.StatusReady?
        && vop.replay
      )
  ensures JC.Next(s.jc.I(), s'.jc.I(),
      JournalDisk.NoDiskOp, vop);
  {
    if vop.AdvanceOp? {
      //if vop.replay {
        assert JC.Replay(s.jc.I(), s'.jc.I(),
            JournalDisk.NoDiskOp, vop);
        assert JC.NextStep(s.jc.I(), s'.jc.I(),
          JournalDisk.NoDiskOp, vop, JC.ReplayStep);
      /*} else {
        assert JC.Advance(s.jc.I(), s'.jc.I(),
            JournalDisk.NoDiskOp, vop);
        assert JC.NextStep(s.jc.I(), s'.jc.I(),
          JournalDisk.NoDiskOp, vop, JC.AdvanceStep);
      }*/
    } else {
      assert JC.NoOp(s.jc.I(), s'.jc.I(),
          JournalDisk.NoDiskOp, vop);
      assert JC.NextStep(s.jc.I(), s'.jc.I(),
          JournalDisk.NoDiskOp, vop, JC.NoOpStep);
    }
  }

  lemma bcNoOp(s: Variables, s': Variables, vop: VOp)
  requires WFBCVars(s.bc)
  requires s.bc == s'.bc
  requires vop.StatesInternalOp? || vop.JournalInternalOp?
      || vop.PushSyncOp? || vop.PopSyncOp?
  ensures BBC.Next(IBlockCache(s.bc), IBlockCache(s'.bc),
      BlockDisk.NoDiskOp, vop);
  {
    assert BC.NoOp(IBlockCache(s.bc), IBlockCache(s'.bc),
        BlockDisk.NoDiskOp, vop);
    assert BC.NextStep(IBlockCache(s.bc), IBlockCache(s'.bc),
        BlockDisk.NoDiskOp, vop, BC.NoOpStep);
    assert BBC.NextStep(IBlockCache(s.bc), IBlockCache(s'.bc),
        BlockDisk.NoDiskOp, vop, BBC.BlockCacheMoveStep(BC.NoOpStep));
  }

  lemma noop(s: Variables)
  requires WFVars(s)
  ensures M.Next(IVars(s), IVars(s), UI.NoOp, D.NoDiskOp)
  {
    jcNoOp(s, s, StatesInternalOp);
    bcNoOp(s, s, StatesInternalOp);
    assert BJC.NextStep(IVars(s), IVars(s), UI.NoOp, IDiskOp(D.NoDiskOp), StatesInternalOp);
  }

  function {:opaque} pushSync(s: Variables) : (Variables, uint64)
  // [yizhou7] strengthened pre-condition
  requires Inv(s)
  {
    var (jc', id) := s.jc.PushSync();
    var s' := s.(jc := jc');
    (s', id)
  }

  lemma pushSyncCorrect(s: Variables)
  requires Inv(s)
  ensures var (s', id) := pushSync(s);
    && WFVars(s')
    && M.Next(IVars(s), IVars(s'),
       if id == 0 then UI.NoOp else UI.PushSyncOp(id as int),
       D.NoDiskOp)
  {
    reveal_pushSync();
    var (s', id) := pushSync(s);

    var uiop := if id == 0 then UI.NoOp else UI.PushSyncOp(id as int);
    var vop := if id == 0 then JournalInternalOp else PushSyncOp(id as int);
    bcNoOp(s, s', vop);
    assert BJC.NextStep(IVars(s), IVars(s'), uiop,
       BJD.DiskOp(BlockDisk.NoDiskOp, JournalDisk.NoDiskOp),
       vop);
    assert BJC.Next(IVars(s), IVars(s'), uiop,
       BJD.DiskOp(BlockDisk.NoDiskOp, JournalDisk.NoDiskOp));
    assert M.Next(IVars(s), IVars(s'),
       if id == 0 then UI.NoOp else UI.PushSyncOp(id as int),
       D.NoDiskOp);
  }

  function {:opaque} receiveLoc(s: BCVariables, loc: DiskLayout.Location) : (s': BCVariables)
  {
    LoadingIndirectionTable(loc, None)
  }

  lemma receiveLocCorrect(s: BCVariables, loc: DiskLayout.Location)
  requires BCInv(s)
  requires DiskLayout.ValidIndirectionTableLocation(loc)
  requires s.Unready?
  ensures var s' := receiveLoc(s, loc);
    && WFBCVars(s')
    && BBC.Next(IBlockCache(s), IBlockCache(s'), BlockDisk.NoDiskOp, SendPersistentLocOp(loc))
  {
    reveal_receiveLoc();
    var s' := receiveLoc(s, loc);
    assert BC.ReceiveLoc(IBlockCache(s), IBlockCache(s'), BlockDisk.NoDiskOp, SendPersistentLocOp(loc));
    assert BC.NextStep(IBlockCache(s), IBlockCache(s'), BlockDisk.NoDiskOp, SendPersistentLocOp(loc), BC.ReceiveLocStep);
    assert BBC.NextStep(IBlockCache(s), IBlockCache(s'), BlockDisk.NoDiskOp, SendPersistentLocOp(loc), BBC.BlockCacheMoveStep(BC.ReceiveLocStep));
  }

  predicate {:opaque} initialization(s: Variables, io: IO,
      s': Variables, io': IO)
  requires Inv(s)
  requires io.IOInit?
  {
    if s.jc.status.StatusLoadingSuperblock? then (
      if s.jc.superblock1.SuperblockSuccess?
          && s.jc.superblock2.SuperblockSuccess? then (
        var cm' := s.jc.FinishLoadingSuperblockPhase();
        var bc' := receiveLoc(
            s.bc, cm'.superblock.indirectionTableLoc);
        && s' == s.(jc := cm').(bc := bc')
        && io' == io
      ) else if s.jc.superblock1Read.None?
          && s.jc.superblock1.SuperblockUnfinished? then (
        && (s'.jc, io') == s.jc.PageInSuperblockReq(io, 0)
        && s'.bc == s.bc
      ) else if s.jc.superblock2Read.None?
          && s.jc.superblock2.SuperblockUnfinished? then (
        && (s'.jc, io') == s.jc.PageInSuperblockReq(io, 1)
        && s'.bc == s.bc
      ) else (
        && s' == s
        && io' == io
      )
    ) else if s.jc.status.StatusLoadingOther? then (
      && (s'.jc, io') == s.jc.TryFinishLoadingOtherPhase(io)
      && s'.bc == s.bc
    ) else if s.bc.LoadingIndirectionTable? &&
        s.bc.indirectionTableRead.None? then (
      && (s'.bc, io') == IOModel.PageInIndirectionTableReq(s.bc, io)
      && s'.jc == s.jc
    ) else if s.bc.Ready? && !s.jc.isReplayEmpty() then (
      var je := s.jc.journalist.replayJournalTop();
      && ((
        && InsertModel.insert(s.bc, io, je.key, je.value, s'.bc, false, io')
        && s'.jc == s.jc
      ) || (
        && InsertModel.insert(s.bc, io, je.key, je.value, s'.bc, true, io')
        && s'.jc == s.jc.JournalReplayOne(s.jc.I().replayJournal[0])
      ))
    ) else (
      && s' == s
      && io' == io
    )
  }

  lemma initializationCorrect(s: Variables, io: IO,
      s': Variables, io': IO)
  requires Inv(s)
  requires io.IOInit?
  requires initialization(s, io, s', io')
  ensures WFVars(s')
  ensures M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    reveal_initialization();
    if s.jc.status.StatusLoadingSuperblock? {
      if s.jc.superblock1.SuperblockSuccess?  && s.jc.superblock2.SuperblockSuccess? {
        // CommitterInitModel.FinishLoadingSuperblockPhaseCorrect(s.jc);
        var cm' := s.jc.FinishLoadingSuperblockPhase();
        receiveLocCorrect(s.bc, cm'.superblock.indirectionTableLoc);
        var bc' := receiveLoc(
            s.bc, cm'.superblock.indirectionTableLoc);
        var s' := s.(jc := cm').(bc := bc');
        assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), SendPersistentLocOp(cm'.superblock.indirectionTableLoc));
        assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
        assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
      } else if s.jc.superblock1Read.None?  && s.jc.superblock1.SuperblockUnfinished? {
        // CommitterInitModel.PageInSuperblockReqCorrect(s.jc, io, 0);
        bcNoOp(s, s', JournalInternalOp);
        assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), JournalInternalOp);
        assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
        assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
      } else if s.jc.superblock2Read.None?  && s.jc.superblock2.SuperblockUnfinished? {
        // CommitterInitModel.PageInSuperblockReqCorrect(s.jc, io, 1);
        bcNoOp(s, s', JournalInternalOp);
        assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), JournalInternalOp);
        assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
        assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
      } else {
        noop(s);
      }
    } else if s.jc.status.StatusLoadingOther? {
      // CommitterInitModel.tryFinishLoadingOtherPhaseCorrect(s.jc, io);
      bcNoOp(s, s', JournalInternalOp);
      assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), JournalInternalOp);
      assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
      assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
    } else if s.bc.LoadingIndirectionTable? &&
        s.bc.indirectionTableRead.None? {
      IOModel.PageInIndirectionTableReqCorrect(s.bc, io);
      jcNoOp(s, s', StatesInternalOp);
      assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), StatesInternalOp);
      assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
      assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
    } else if s.bc.Ready? &&
          !s.jc.isReplayEmpty() {
      var je := s.jc.journalist.replayJournalTop();
      if InsertModel.insert(s.bc, io, je.key, je.value, s'.bc, false, io') && s'.jc == s.jc {
        InsertModel.insertCorrect(s.bc, io, je.key, je.value, s'.bc, false, io', true);
        var vop;
        if BBC.Next(IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, StatesInternalOp) {
          vop := StatesInternalOp;
        } else {
          vop := AdvanceOp(UI.NoOp, true);
        }
        jcNoOp(s, s', vop);
        assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), vop);
        assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
        assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
      } else {
        assert InsertModel.insert(s.bc, io, je.key, je.value, s'.bc, true, io');
        InsertModel.insertCorrect(s.bc, io, je.key, je.value, s'.bc, true, io', true);
        // CommitterReplayModel.JournalReplayOneCorrect(s.jc, je);
        var vop := AdvanceOp(UI.PutOp(je.key, je.value), true);
        assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), vop);
        assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
        assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
      }
    } else {
      noop(s);
    }
  }

  predicate doSync(
      s: Variables, io: IO, graphSync: bool,
      s': Variables, io': IO)
  requires Inv(s)
  requires io.IOInit?
  requires s.bc.Ready?
  requires s.jc.status.StatusReady?
  // [yizhou7] this additional precondition is added
  requires s.jc.journalist.I().replayJournal == []
  {
    if s.jc.isFrozen then (
      if s.jc.frozenLoc.Some? then (
        && s.jc.TryAdvanceLocation(io) == (s'.jc, io')
        && s.bc == s'.bc
      ) else (
        && (
          || SyncModel.sync(s.bc, io, s'.bc, io', true /* froze */)
          || SyncModel.sync(s.bc, io, s'.bc, io', false /* froze */)
        )
        && s.jc == s'.jc
      )
    ) else if s.jc.superblockWrite.Some? then (
      && s' == s
      && io' == io
    ) else (
      if graphSync then (
        || (
          && SyncModel.sync(s.bc, io, s'.bc, io', true /* froze */)
          && (s'.jc == s.jc.Freeze())
        )
        || (
          && SyncModel.sync(s.bc, io, s'.bc, io', false /* froze */)
          && (s'.jc == s.jc)
        )
      ) else (
        && s.jc.TryAdvanceLog(io) == (s'.jc, io')
        && s.bc == s'.bc
      )
    )
  }

  lemma doSyncCorrect(
      s: Variables, io: IO, graphSync: bool,
      s': Variables, io': IO)
  requires Inv(s)
  requires io.IOInit?
  requires s.bc.Ready?
  requires s.jc.status.StatusReady?
  requires s.jc.journalist.I().replayJournal == []
  requires doSync(s, io, graphSync, s', io')
  ensures WFVars(s')
  ensures M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    if s.jc.isFrozen {
      if s.jc.frozenLoc.Some? {
        // CommitterCommitModel.tryAdvanceLocationCorrect(s.jc, io, s'.jc, io');

        var uiop := UI.NoOp;
        var vop := JournalInternalOp;
        bcNoOp(s, s', vop);
        assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
        assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        assert M.Next(IVars(s), IVars(s'), uiop, diskOp(io'));
      } else {
        var froze :|
          && SyncModel.sync(s.bc, io, s'.bc, io', froze)
          && s.jc == s'.jc;
        SyncModel.syncCorrect(s.bc, io, s'.bc, io', froze);

        assert !froze;

        var uiop := UI.NoOp;
        if BBC.Next(IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, StatesInternalOp) {
          var vop := StatesInternalOp;
          jcNoOp(s, s', vop);
          assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
          assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
        } else {
          var vop := AdvanceOp(UI.NoOp, true);
          assert BBC.Next(IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, vop);
          jcNoOp(s, s', vop);
          assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
          assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
        }
      }
    } else if s.jc.superblockWrite.Some? {
      noop(s);
    } else {
      if graphSync {
        var froze :|
          && SyncModel.sync(s.bc, io, s'.bc, io', froze)
          && (froze ==> s'.jc == s.jc.Freeze())
          && (!froze ==> s'.jc == s.jc);

          SyncModel.syncCorrect(s.bc, io, s'.bc, io', froze);
          if froze {
            // CommitterCommitModel.freezeCorrect(s.jc);
            assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), FreezeOp);
            assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
            assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
          } else {
            var uiop := UI.NoOp;
            if BBC.Next(IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, StatesInternalOp) {
              var vop := StatesInternalOp;
              jcNoOp(s, s', vop);
              assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
              assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
              assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
            } else {
              var vop := AdvanceOp(UI.NoOp, true);
              assert BBC.Next(IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, vop);
              jcNoOp(s, s', vop);
              assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
              assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
              assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
            }

            assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
          }
      } else {
        // CommitterCommitModel.tryAdvanceLogCorrect(s.jc, io, s'.jc, io');

        var uiop := UI.NoOp;
        var vop := JournalInternalOp;
        bcNoOp(s, s', vop);
        assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
        assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
      }
    }
  }

  predicate isInitialized(s: Variables)
  {
    && s.bc.Ready?
    && s.jc.status.StatusReady?
    && s.jc.journalist.Inv()
    && s.jc.isReplayEmpty()
  }

  predicate {:opaque} popSync(
      s: Variables, io: IO, id: uint64, graphSync: bool,
      s': Variables, io': IO, success: bool)
  requires Inv(s)
  requires io.IOInit?
  {
    if id in s.jc.syncReqs.contents && s.jc.syncReqs.contents[id] == JC.State1 then (
      var jc' := s.jc.PopSync(id);
      && s' == s.(jc := jc')
      && io' == io
      && success == true
    ) else if !isInitialized(s) then (
      && initialization(s, io, s', io')
      && success == false
    ) else (
      doSync(s, io, graphSync, s', io')
      && success == false
    )
  }

  lemma popSyncCorrect(
      s: Variables, io: IO, id: uint64, graphSync: bool,
      s': Variables, io': IO, success: bool)
  requires Inv(s)
  requires io.IOInit?
  requires popSync(s, io, id, graphSync, s', io', success)

  ensures WFVars(s')
  ensures M.Next(IVars(s), IVars(s'),
        if success then UI.PopSyncOp(id as int) else UI.NoOp,
        diskOp(io'))
  {
    reveal_popSync();
    if id in s.jc.syncReqs.contents && s.jc.syncReqs.contents[id] == JC.State1 {
      // CommitterCommitModel.popSyncCorrect(s.jc, id);

      var uiop := if success then UI.PopSyncOp(id as int) else UI.NoOp;
      var vop := if success then PopSyncOp(id as int) else JournalInternalOp;
      bcNoOp(s, s', vop);
      assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
      assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
      assert M.Next(IVars(s), IVars(s'), uiop, diskOp(io'));

    } else if !isInitialized(s) {
      initializationCorrect(s, io, s', io');
      assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
    } else {
      doSyncCorrect(s, io, graphSync, s', io');
    }
  }

  predicate {:opaque} query(
      s: Variables, io: IO, key: Key,
      s': Variables, result: Option<Value>, io': IO)
  requires io.IOInit?
  requires Inv(s)
  {
    if !isInitialized(s) then (
      && initialization(s, io, s', io')
      && result == None
    ) else (
      && QueryModel.query(s.bc, io, key, s'.bc, result, io')
      && s.jc == s'.jc
    )
  }

  lemma queryCorrect(s: Variables, io: IO, key: Key,
      s': Variables, result: Option<Value>, io': IO)
  requires io.IOInit?
  requires Inv(s)
  requires query(s, io, key, s', result, io')
  ensures WFVars(s')
  ensures M.Next(IVars(s), IVars(s'),
          if result.Some? then UI.GetOp(key, result.value) else UI.NoOp,
          diskOp(io'))
  {
    reveal_query();
    if !isInitialized(s) {
      initializationCorrect(s, io, s', io');
    } else {
      QueryModel.queryCorrect(s.bc, io, key, s'.bc, result, io');
      if result.Some? {
        var uiop := UI.GetOp(key, result.value);
        var vop := AdvanceOp(uiop, false);

        assert JC.Advance(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);
        assert JC.NextStep(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop, JC.AdvanceStep);
        assert JC.Next(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);

        assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
        assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
      } else {
        var uiop := UI.NoOp;
        if BBC.Next(IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, StatesInternalOp) {
          var vop := StatesInternalOp;
          assert JC.NoOp(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop, JC.NoOpStep);
          assert JC.Next(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        } else {
          var vop := AdvanceOp(uiop, true);
          // Not a true replay (empty journal entry list).
          assert JC.Replay(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop, JC.ReplayStep);
          assert JC.Next(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        }
      }
    }
  }

  predicate {:opaque} succ(
      s: Variables, io: IO, start: UI.RangeStart, maxToFind: int,
      s': Variables, result: Option<UI.SuccResultList>, io': IO)
  requires io.IOInit?
  requires Inv(s)
  requires maxToFind >= 1
  {
    if !isInitialized(s) then (
      && initialization(s, io, s', io')
      && result == None
    ) else (
      && (s'.bc, io', result) == SuccModel.doSucc(s.bc, io, start, maxToFind)
      && s.jc == s'.jc
    )
  }

  lemma succCorrect(s: Variables, io: IO, start: UI.RangeStart, maxToFind: int,
      s': Variables, result: Option<UI.SuccResultList>, io': IO)
  requires io.IOInit?
  requires Inv(s)
  requires maxToFind >= 1
  requires succ(s, io, start, maxToFind, s', result, io')
  ensures WFVars(s')
  ensures M.Next(IVars(s), IVars(s'),
          if result.Some? then UI.SuccOp(start, result.value.results, result.value.end) else UI.NoOp,
          diskOp(io'))
  {
    reveal_succ();
    if !isInitialized(s) {
      initializationCorrect(s, io, s', io');
    } else {
      SuccModel.doSuccCorrect(s.bc, io, start, maxToFind);
      if result.Some? {
        var uiop := UI.SuccOp(start, result.value.results, result.value.end);
        var vop := AdvanceOp(uiop, false);

        assert JC.Advance(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);
        assert JC.NextStep(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop, JC.AdvanceStep);
        assert JC.Next(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);

        assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
        assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
      } else {
        var uiop := UI.NoOp;
        if BBC.Next(IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, StatesInternalOp) {
          var vop := StatesInternalOp;
          assert JC.NoOp(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop, JC.NoOpStep);
          assert JC.Next(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        } else {
          var vop := AdvanceOp(uiop, true);
          // Not a true replay (empty journal entry list).
          assert JC.Replay(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop, JC.ReplayStep);
          assert JC.Next(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        }
      }
    }
  }

  predicate {:opaque} insert(
      s: Variables, io: IO, key: Key, value: Value,
      s': Variables, success: bool, io': IO)
  requires io.IOInit?
  requires Inv(s)
  {
    if !isInitialized(s) then (
      && initialization(s, io, s', io')
      && success == false
    ) else if s.jc.journalist.canAppend(Journal.JournalInsert(key, value))
    then (
      && InsertModel.insert(s.bc, io, key, value,
              s'.bc, success, io')
      && (!success ==> s.jc == s'.jc)
      && (success ==>
          s'.jc == s.jc.JournalAppend(key, value)
      )
    ) else (
      && doSync(s, io, true /* graphSync */, s', io')
      && success == false
    )
  }

  lemma insertCorrect(s: Variables, io: IO, key: Key, value: Value,
      s': Variables, success: bool, io': IO)
  requires io.IOInit?
  requires Inv(s)
  requires insert(s, io, key, value, s', success, io')
  ensures WFVars(s')
  ensures M.Next(IVars(s), IVars(s'),
          if success then UI.PutOp(key, value) else UI.NoOp,
          diskOp(io'))
  {
    reveal_insert();
    if !isInitialized(s) {
      initializationCorrect(s, io, s', io');
    } else if s.jc.journalist.canAppend(Journal.JournalInsert(key, value)) {
      InsertModel.insertCorrect(s.bc, io, key, value, s'.bc, success, io', false /* replay */);
      if success {
        var uiop := UI.PutOp(key, value);
        var vop := AdvanceOp(uiop, false);

        //  CommitterAppendModel.JournalAppendCorrect(s.jc, key, value);

        assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
        assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
      } else {
        var uiop := UI.NoOp;
        if BBC.Next(IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, StatesInternalOp) {
          var vop := StatesInternalOp;
          assert JC.NoOp(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop, JC.NoOpStep);
          assert JC.Next(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        } else {
          var vop := AdvanceOp(uiop, true);
          // Not a true replay (empty journal entry list).
          assert JC.Replay(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop, JC.ReplayStep);
          assert JC.Next(s.jc.I(), s'.jc.I(), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        }
      }
    } else {
      doSyncCorrect(s, io, true, s', io');
    }
  }
}
