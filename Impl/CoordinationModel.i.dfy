include "SyncModel.i.dfy"
include "CommitterCommitModel.i.dfy"
include "CommitterInitModel.i.dfy"
include "CommitterAppendModel.i.dfy"
include "CommitterReplayModel.i.dfy"
include "QueryModel.i.dfy"
include "SuccModel.i.dfy"
include "InsertModel.i.dfy"

module CoordinationModel {
  import opened StateModel
  import opened Options
  import CommitterModel
  import IOModel
  import SyncModel
  import CommitterCommitModel
  import CommitterInitModel
  import CommitterAppendModel
  import CommitterReplayModel
  import QueryModel
  import SuccModel
  import InsertModel
  import JournalistModel
  import Journal
  import opened InterpretationDiskOps
  import opened ViewOp
  import opened NativeTypes
  import DiskLayout
  import opened KeyType
  import opened ValueType
  import opened DiskOpModel

  lemma jcNoOp(k: Constants, s: Variables, s': Variables, vop: VOp)
  requires CommitterModel.WF(s.jc)
  requires s.jc == s'.jc
  requires vop.StatesInternalOp? || vop.JournalInternalOp?
      || (vop.AdvanceOp?
        && vop.uiop.NoOp?
        && s.jc.status.StatusReady?
        && vop.replay
      )
  ensures JC.Next(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc),
      JournalDisk.NoDiskOp, vop);
  {
    if vop.AdvanceOp? {
      //if vop.replay {
        assert JC.Replay(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc),
            JournalDisk.NoDiskOp, vop);
        assert JC.NextStep(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc),
          JournalDisk.NoDiskOp, vop, JC.ReplayStep);
      /*} else {
        assert JC.Advance(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc),
            JournalDisk.NoDiskOp, vop);
        assert JC.NextStep(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc),
          JournalDisk.NoDiskOp, vop, JC.AdvanceStep);
      }*/
    } else {
      assert JC.NoOp(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc),
          JournalDisk.NoDiskOp, vop);
      assert JC.NextStep(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc),
          JournalDisk.NoDiskOp, vop, JC.NoOpStep);
    }
  }

  lemma bcNoOp(k: Constants, s: Variables, s': Variables, vop: VOp)
  requires WFBCVars(s.bc)
  requires s.bc == s'.bc
  requires vop.StatesInternalOp? || vop.JournalInternalOp?
      || vop.PushSyncOp? || vop.PopSyncOp?
  ensures BBC.Next(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc),
      BlockDisk.NoDiskOp, vop);
  {
    assert BC.NoOp(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc),
        BlockDisk.NoDiskOp, vop);
    assert BC.NextStep(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc),
        BlockDisk.NoDiskOp, vop, BC.NoOpStep);
    assert BBC.NextStep(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc),
        BlockDisk.NoDiskOp, vop, BBC.BlockCacheMoveStep(BC.NoOpStep));
  }

  lemma noop(k: Constants, s: Variables)
  requires WFVars(s)
  ensures M.Next(Ik(k), IVars(s), IVars(s), UI.NoOp, D.NoDiskOp)
  {
    jcNoOp(k, s, s, StatesInternalOp);
    bcNoOp(k, s, s, StatesInternalOp);
    assert BJC.NextStep(Ik(k), IVars(s), IVars(s), UI.NoOp, IDiskOp(D.NoDiskOp), StatesInternalOp);
  }

  function {:opaque} pushSync(k: Constants, s: Variables)
      : (Variables, uint64)
  requires WFVars(s)
  {
    var (jc', id) := CommitterCommitModel.pushSync(k, s.jc);
    var s' := s.(jc := jc');
    (s', id)
  }

  lemma pushSyncCorrect(k: Constants, s: Variables)
  requires Inv(k, s)
  ensures var (s', id) := pushSync(k, s);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'),
       if id == 0 then UI.NoOp else UI.PushSyncOp(id as int),
       D.NoDiskOp)
  {
    reveal_pushSync();
    var (s', id) := pushSync(k, s);
    CommitterCommitModel.pushSyncCorrect(k, s.jc);

    var uiop := if id == 0 then UI.NoOp else UI.PushSyncOp(id as int);
    var vop := if id == 0 then JournalInternalOp else PushSyncOp(id as int);
    bcNoOp(k, s, s', vop);
    assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop,
       BJD.DiskOp(BlockDisk.NoDiskOp, JournalDisk.NoDiskOp),
       vop);
    assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop,
       BJD.DiskOp(BlockDisk.NoDiskOp, JournalDisk.NoDiskOp));
    assert M.Next(Ik(k), IVars(s), IVars(s'),
       if id == 0 then UI.NoOp else UI.PushSyncOp(id as int),
       D.NoDiskOp);
  }

  function {:opaque} receiveLoc(k: Constants, s: BCVariables, loc: DiskLayout.Location) : (s': BCVariables)
  {
    LoadingIndirectionTable(loc, None)
  }

  lemma receiveLocCorrect(k: Constants, s: BCVariables, loc: DiskLayout.Location)
  requires BCInv(k, s)
  requires DiskLayout.ValidIndirectionTableLocation(loc)
  requires s.Unready?
  ensures var s' := receiveLoc(k, s, loc);
    && WFBCVars(s')
    && BBC.Next(Ik(k).bc, IBlockCache(s), IBlockCache(s'), BlockDisk.NoDiskOp, SendPersistentLocOp(loc))
  {
    reveal_receiveLoc();
    var s' := receiveLoc(k, s, loc);
    assert BC.ReceiveLoc(Ik(k).bc, IBlockCache(s), IBlockCache(s'), BlockDisk.NoDiskOp, SendPersistentLocOp(loc));
    assert BC.NextStep(Ik(k).bc, IBlockCache(s), IBlockCache(s'), BlockDisk.NoDiskOp, SendPersistentLocOp(loc), BC.ReceiveLocStep);
    assert BBC.NextStep(Ik(k).bc, IBlockCache(s), IBlockCache(s'), BlockDisk.NoDiskOp, SendPersistentLocOp(loc), BBC.BlockCacheMoveStep(BC.ReceiveLocStep));
  }

  predicate {:opaque} initialization(k: Constants, s: Variables, io: IO,
      s': Variables, io': IO)
  requires Inv(k, s)
  requires io.IOInit?
  {
    if s.jc.status.StatusLoadingSuperblock? then (
      if s.jc.superblock1.SuperblockSuccess?
          && s.jc.superblock2.SuperblockSuccess? then (
        var cm' := CommitterInitModel.FinishLoadingSuperblockPhase(k, s.jc);
        var bc' := receiveLoc(
            k, s.bc, cm'.superblock.indirectionTableLoc);
        && s' == s.(jc := cm').(bc := bc')
        && io' == io
      ) else if s.jc.superblock1Read.None?
          && s.jc.superblock1.SuperblockUnfinished? then (
        && (s'.jc, io') == CommitterInitModel.PageInSuperblockReq(k, s.jc, io, 0)
        && s'.bc == s.bc
      ) else if s.jc.superblock2Read.None?
          && s.jc.superblock2.SuperblockUnfinished? then (
        && (s'.jc, io') == CommitterInitModel.PageInSuperblockReq(k, s.jc, io, 1)
        && s'.bc == s.bc
      ) else (
        && s' == s
        && io' == io
      )
    ) else if s.jc.status.StatusLoadingOther? then (
      && (s'.jc, io') == CommitterInitModel.tryFinishLoadingOtherPhase(k, s.jc, io)
      && s'.bc == s.bc
    ) else if s.bc.LoadingIndirectionTable? &&
        s.bc.indirectionTableRead.None? then (
      && (s'.bc, io') == IOModel.PageInIndirectionTableReq(k, s.bc, io)
      && s'.jc == s.jc
    ) else if s.bc.Ready? &&
          !CommitterInitModel.isReplayEmpty(s.jc) then (
      var je := JournalistModel.replayJournalTop(s.jc.journalist);
      && ((
        && InsertModel.insert(k, s.bc, io, je.key, je.value, s'.bc, false, io')
        && s'.jc == s.jc
      ) || (
        && InsertModel.insert(k, s.bc, io, je.key, je.value, s'.bc, true, io')
        && s'.jc ==
            CommitterReplayModel.JournalReplayOne(k, s.jc)
      ))
    ) else (
      && s' == s
      && io' == io
    )
  }

  lemma initializationCorrect(k: Constants, s: Variables, io: IO,
      s': Variables, io': IO)
  requires Inv(k, s)
  requires io.IOInit?
  requires initialization(k, s, io, s', io')
  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'))
  {
    reveal_initialization();
    if s.jc.status.StatusLoadingSuperblock? {
      if s.jc.superblock1.SuperblockSuccess?  && s.jc.superblock2.SuperblockSuccess? {
        CommitterInitModel.FinishLoadingSuperblockPhaseCorrect(k, s.jc);
        var cm' := CommitterInitModel.FinishLoadingSuperblockPhase(k, s.jc);
        receiveLocCorrect(k, s.bc, cm'.superblock.indirectionTableLoc);
        var bc' := receiveLoc(
            k, s.bc, cm'.superblock.indirectionTableLoc);
        var s' := s.(jc := cm').(bc := bc');
        assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), SendPersistentLocOp(cm'.superblock.indirectionTableLoc));
        assert BJC.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
        assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
      } else if s.jc.superblock1Read.None?  && s.jc.superblock1.SuperblockUnfinished? {
        CommitterInitModel.PageInSuperblockReqCorrect(k, s.jc, io, 0);
        bcNoOp(k, s, s', JournalInternalOp);
        assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), JournalInternalOp);
        assert BJC.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
        assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
      } else if s.jc.superblock2Read.None?  && s.jc.superblock2.SuperblockUnfinished? {
        CommitterInitModel.PageInSuperblockReqCorrect(k, s.jc, io, 1);
        bcNoOp(k, s, s', JournalInternalOp);
        assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), JournalInternalOp);
        assert BJC.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
        assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
      } else {
        noop(k, s);
      }
    } else if s.jc.status.StatusLoadingOther? {
      CommitterInitModel.tryFinishLoadingOtherPhaseCorrect(k, s.jc, io);
      bcNoOp(k, s, s', JournalInternalOp);
      assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), JournalInternalOp);
      assert BJC.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
      assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
    } else if s.bc.LoadingIndirectionTable? &&
        s.bc.indirectionTableRead.None? {
      IOModel.PageInIndirectionTableReqCorrect(k, s.bc, io);
      jcNoOp(k, s, s', StatesInternalOp);
      assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), StatesInternalOp);
      assert BJC.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
      assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
    } else if s.bc.Ready? &&
          !CommitterInitModel.isReplayEmpty(s.jc) {
      var je := JournalistModel.replayJournalTop(s.jc.journalist);
      if InsertModel.insert(k, s.bc, io, je.key, je.value, s'.bc, false, io') && s'.jc == s.jc {
        InsertModel.insertCorrect(k, s.bc, io, je.key, je.value, s'.bc, false, io', true);
        var vop;
        if BBC.Next(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, StatesInternalOp) {
          vop := StatesInternalOp;
        } else {
          vop := AdvanceOp(UI.NoOp, true);
        }
        jcNoOp(k, s, s', vop);
        assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), vop);
        assert BJC.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
        assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
      } else {
        assert InsertModel.insert(k, s.bc, io, je.key, je.value, s'.bc, true, io');
        InsertModel.insertCorrect(k, s.bc, io, je.key, je.value, s'.bc, true, io', true);
        CommitterReplayModel.JournalReplayOneCorrect(k, s.jc, je);
        var vop := AdvanceOp(UI.PutOp(je.key, je.value), true);
        assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), vop);
        assert BJC.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
        assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
      }
    } else {
      noop(k, s);
    }
  }

  predicate doSync(
      k: Constants, s: Variables, io: IO, graphSync: bool,
      s': Variables, io': IO)
  requires Inv(k, s)
  requires io.IOInit?
  requires s.bc.Ready?
  requires s.jc.status.StatusReady?
  {
    if s.jc.isFrozen then (
      if s.jc.frozenLoc.Some? then (
        && CommitterCommitModel.tryAdvanceLocation(k, s.jc, io, s'.jc, io')
        && s.bc == s'.bc
      ) else (
        && (
          || SyncModel.sync(k, s.bc, io, s'.bc, io', true /* froze */)
          || SyncModel.sync(k, s.bc, io, s'.bc, io', false /* froze */)
        )
        && s.jc == s'.jc
      )
    ) else if s.jc.superblockWrite.Some? then (
      && s' == s
      && io' == io
    ) else (
      if graphSync then (
        || (
          && SyncModel.sync(k, s.bc, io, s'.bc, io', true /* froze */)
          && (s'.jc == CommitterCommitModel.freeze(k, s.jc))
        )
        || (
          && SyncModel.sync(k, s.bc, io, s'.bc, io', false /* froze */)
          && (s'.jc == s.jc)
        )
      ) else (
        && CommitterCommitModel.tryAdvanceLog(k, s.jc, io, s'.jc, io')
        && s.bc == s'.bc
      )
    )
  }

  lemma doSyncCorrect(
      k: Constants, s: Variables, io: IO, graphSync: bool,
      s': Variables, io': IO)
  requires Inv(k, s)
  requires io.IOInit?
  requires s.bc.Ready?
  requires s.jc.status.StatusReady?
  requires JournalistModel.I(s.jc.journalist).replayJournal == []
  requires doSync(k, s, io, graphSync, s', io')
  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'),
        UI.NoOp, diskOp(io'))
  {
    //reveal_doSync();
    if s.jc.isFrozen {
      if s.jc.frozenLoc.Some? {
        CommitterCommitModel.tryAdvanceLocationCorrect(k, s.jc, io, s'.jc, io');

        var uiop := UI.NoOp;
        var vop := JournalInternalOp;
        bcNoOp(k, s, s', vop);
        assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
        assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        assert M.Next(Ik(k), IVars(s), IVars(s'), uiop, diskOp(io'));
      } else {
        var froze :|
          && SyncModel.sync(k, s.bc, io, s'.bc, io', froze)
          && s.jc == s'.jc;
        SyncModel.syncCorrect(k, s.bc, io, s'.bc, io', froze);

        assert !froze;

        var uiop := UI.NoOp;
        if BBC.Next(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, StatesInternalOp) {
          var vop := StatesInternalOp;
          jcNoOp(k, s, s', vop);
          assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
          assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
        } else {
          var vop := AdvanceOp(UI.NoOp, true);
          assert BBC.Next(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, vop);
          jcNoOp(k, s, s', vop);
          assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
          assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
        }
      }
    } else if s.jc.superblockWrite.Some? {
      noop(k, s);
    } else {
      if graphSync {
        var froze :|
          && SyncModel.sync(k, s.bc, io, s'.bc, io', froze)
          && (froze ==> s'.jc == CommitterCommitModel.freeze(k, s.jc))
          && (!froze ==> s'.jc == s.jc);

          SyncModel.syncCorrect(k, s.bc, io, s'.bc, io', froze);
          if froze {
            CommitterCommitModel.freezeCorrect(k, s.jc);
            assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')), FreezeOp);
            assert BJC.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io')));
            assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
          } else {
            var uiop := UI.NoOp;
            if BBC.Next(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, StatesInternalOp) {
              var vop := StatesInternalOp;
              jcNoOp(k, s, s', vop);
              assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
              assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
              assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
            } else {
              var vop := AdvanceOp(UI.NoOp, true);
              assert BBC.Next(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, vop);
              jcNoOp(k, s, s', vop);
              assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
              assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
              assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
            }

            assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
          }
      } else {
        CommitterCommitModel.tryAdvanceLogCorrect(k, s.jc, io, s'.jc, io');

        var uiop := UI.NoOp;
        var vop := JournalInternalOp;
        bcNoOp(k, s, s', vop);
        assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
        assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
      }
    }
  }

  predicate isInitialized(s: Variables)
  {
    && s.bc.Ready?
    && s.jc.status.StatusReady?
    && JournalistModel.Inv(s.jc.journalist)
    && CommitterInitModel.isReplayEmpty(s.jc)
  }

  predicate {:opaque} popSync(
      k: Constants, s: Variables, io: IO, id: uint64, graphSync: bool,
      s': Variables, io': IO, success: bool)
  requires Inv(k, s)
  requires io.IOInit?
  {
    if id in s.jc.syncReqs.contents && s.jc.syncReqs.contents[id] == JC.State1 then (
      var jc' := CommitterCommitModel.popSync(k, s.jc, id);
      && s' == s.(jc := jc')
      && io' == io
      && success == true
    ) else if !isInitialized(s) then (
      && initialization(k, s, io, s', io')
      && success == false
    ) else (
      doSync(k, s, io, graphSync, s', io')
      && success == false
    )
  }

  lemma popSyncCorrect(
      k: Constants, s: Variables, io: IO, id: uint64, graphSync: bool,
      s': Variables, io': IO, success: bool)
  requires Inv(k, s)
  requires io.IOInit?
  requires popSync(k, s, io, id, graphSync, s', io', success)

  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'),
        if success then UI.PopSyncOp(id as int) else UI.NoOp,
        diskOp(io'))
  {
    reveal_popSync();
    //CommitterInitModel.reveal_isReplayEmpty();
    if id in s.jc.syncReqs.contents && s.jc.syncReqs.contents[id] == JC.State1 {
      CommitterCommitModel.popSyncCorrect(k, s.jc, id);

      var uiop := if success then UI.PopSyncOp(id as int) else UI.NoOp;
      var vop := if success then PopSyncOp(id as int) else JournalInternalOp;
      bcNoOp(k, s, s', vop);
      assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
      assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
      assert M.Next(Ik(k), IVars(s), IVars(s'), uiop, diskOp(io'));

    } else if !isInitialized(s) {
      initializationCorrect(k, s, io, s', io');
      assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io'));
    } else {
      doSyncCorrect(k, s, io, graphSync, s', io');
    }
  }

  predicate {:opaque} query(
      k: Constants, s: Variables, io: IO, key: Key,
      s': Variables, result: Option<Value>, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  {
    if !isInitialized(s) then (
      && initialization(k, s, io, s', io')
      && result == None
    ) else (
      && QueryModel.query(k, s.bc, io, key, s'.bc, result, io')
      && s.jc == s'.jc
    )
  }

  lemma queryCorrect(k: Constants, s: Variables, io: IO, key: Key,
      s': Variables, result: Option<Value>, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires query(k, s, io, key, s', result, io')
  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'),
          if result.Some? then UI.GetOp(key, result.value) else UI.NoOp,
          diskOp(io'))
  {
    reveal_query();
    //CommitterInitModel.reveal_isReplayEmpty();
    if !isInitialized(s) {
      initializationCorrect(k, s, io, s', io');
    } else {
      QueryModel.queryCorrect(k, s.bc, io, key, s'.bc, result, io');
      if result.Some? {
        var uiop := UI.GetOp(key, result.value);
        var vop := AdvanceOp(uiop, false);

        assert JC.Advance(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);
        assert JC.NextStep(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop, JC.AdvanceStep);
        assert JC.Next(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);

        assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
        assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
      } else {
        var uiop := UI.NoOp;
        if BBC.Next(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, StatesInternalOp) {
          var vop := StatesInternalOp;
          assert JC.NoOp(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop, JC.NoOpStep);
          assert JC.Next(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        } else {
          var vop := AdvanceOp(uiop, true);
          // Not a true replay (empty journal entry list).
          assert JC.Replay(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop, JC.ReplayStep);
          assert JC.Next(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        }
      }
    }
  }

  predicate {:opaque} succ(
      k: Constants, s: Variables, io: IO, start: UI.RangeStart, maxToFind: int,
      s': Variables, result: Option<UI.SuccResultList>, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires maxToFind >= 1
  {
    if !isInitialized(s) then (
      && initialization(k, s, io, s', io')
      && result == None
    ) else (
      && (s'.bc, io', result) == SuccModel.doSucc(k, s.bc, io, start, maxToFind)
      && s.jc == s'.jc
    )
  }

  lemma succCorrect(k: Constants, s: Variables, io: IO, start: UI.RangeStart, maxToFind: int,
      s': Variables, result: Option<UI.SuccResultList>, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires maxToFind >= 1
  requires succ(k, s, io, start, maxToFind, s', result, io')
  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'),
          if result.Some? then UI.SuccOp(start, result.value.results, result.value.end) else UI.NoOp,
          diskOp(io'))
  {
    reveal_succ();
    //CommitterInitModel.reveal_isReplayEmpty();
    if !isInitialized(s) {
      initializationCorrect(k, s, io, s', io');
    } else {
      SuccModel.doSuccCorrect(k, s.bc, io, start, maxToFind);
      if result.Some? {
        var uiop := UI.SuccOp(start, result.value.results, result.value.end);
        var vop := AdvanceOp(uiop, false);

        assert JC.Advance(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);
        assert JC.NextStep(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop, JC.AdvanceStep);
        assert JC.Next(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);

        assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
        assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
      } else {
        var uiop := UI.NoOp;
        if BBC.Next(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, StatesInternalOp) {
          var vop := StatesInternalOp;
          assert JC.NoOp(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop, JC.NoOpStep);
          assert JC.Next(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        } else {
          var vop := AdvanceOp(uiop, true);
          // Not a true replay (empty journal entry list).
          assert JC.Replay(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop, JC.ReplayStep);
          assert JC.Next(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        }
      }
    }
  }

  predicate {:opaque} insert(
      k: Constants, s: Variables, io: IO, key: Key, value: Value,
      s': Variables, success: bool, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  {
    if !isInitialized(s) then (
      && initialization(k, s, io, s', io')
      && success == false
    ) else if JournalistModel.canAppend(s.jc.journalist,
        Journal.JournalInsert(key, value))
    then (
      && InsertModel.insert(k, s.bc, io, key, value,
              s'.bc, success, io')
      && (!success ==> s.jc == s'.jc)
      && (success ==>
          s'.jc == CommitterAppendModel.JournalAppend(
              k, s.jc, key, value)
      )
    ) else (
      && doSync(k, s, io, true /* graphSync */, s', io')
      && success == false
    )
  }

  lemma insertCorrect(k: Constants, s: Variables, io: IO, key: Key, value: Value,
      s': Variables, success: bool, io': IO)
  requires io.IOInit?
  requires Inv(k, s)
  requires insert(k, s, io, key, value, s', success, io')
  ensures WFVars(s')
  ensures M.Next(Ik(k), IVars(s), IVars(s'),
          if success then UI.PutOp(key, value) else UI.NoOp,
          diskOp(io'))
  {
    reveal_insert();
    //CommitterInitModel.reveal_isReplayEmpty();
    if !isInitialized(s) {
      initializationCorrect(k, s, io, s', io');
    } else if JournalistModel.canAppend(s.jc.journalist, Journal.JournalInsert(key, value)) {
      InsertModel.insertCorrect(k, s.bc, io, key, value, s'.bc, success, io', false /* replay */);
      if success {
        var uiop := UI.PutOp(key, value);
        var vop := AdvanceOp(uiop, false);

         CommitterAppendModel.JournalAppendCorrect(k, s.jc, key, value);

        assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
        assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
      } else {
        var uiop := UI.NoOp;
        if BBC.Next(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io')).bdop, StatesInternalOp) {
          var vop := StatesInternalOp;
          assert JC.NoOp(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop, JC.NoOpStep);
          assert JC.Next(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        } else {
          var vop := AdvanceOp(uiop, true);
          // Not a true replay (empty journal entry list).
          assert JC.Replay(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop, JC.ReplayStep);
          assert JC.Next(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')), vop);
          assert BJC.Next(Ik(k), IVars(s), IVars(s'), uiop, IDiskOp(diskOp(io')));
        }
      }
    } else {
      doSyncCorrect(k, s, io, true, s', io');
    }
  }
}
