// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "FullImpl.i.dfy"
include "QueryImpl.i.dfy"
include "InsertImpl.i.dfy"
include "SuccImpl.i.dfy"

module CoordinationImpl {
  import opened StateBCImpl
  import opened Options
  import QueryImpl
  import SuccImpl
  import InsertImpl
  import SyncImpl
  import IOImpl
  import Journal
  import opened InterpretationDiskOps
  import opened ViewOp
  import opened NativeTypes
  import DiskLayout
  import opened KeyType
  import opened ValueType
  import opened FullImpl
  import opened DiskOpImpl
  import opened MainDiskIOHandler
  import opened LinearMutableMap
  import opened DiskOpModel

  import M = ByteCache

  lemma jcNoOp(s: Full, s': Full, vop: VOp)
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

  lemma bcNoOp(s: Full, s': Full, vop: VOp)
  requires s.bc.W()
  requires s.bc == s'.bc
  requires vop.StatesInternalOp? || vop.JournalInternalOp?
      || vop.PushSyncOp? || vop.PopSyncOp?
  ensures BBC.Next(s.bc.I(), s'.bc.I(),
      BlockDisk.NoDiskOp, vop);
  {
    assert BC.NoOp(s.bc.I(), s'.bc.I(),
        BlockDisk.NoDiskOp, vop);
    assert BC.NextStep(s.bc.I(), s'.bc.I(),
        BlockDisk.NoDiskOp, vop, BC.NoOpStep);
    assert BBC.NextStep(s.bc.I(), s'.bc.I(),
        BlockDisk.NoDiskOp, vop, BBC.BlockCacheMoveStep(BC.NoOpStep));
  }

  lemma noop(s: Full)
  requires s.W()
  ensures M.Next(s.I(), s.I(), UI.NoOp, D.NoDiskOp)
  {
    jcNoOp(s, s, StatesInternalOp);
    bcNoOp(s, s, StatesInternalOp);
    assert BJC.NextStep(s.I(), s.I(), UI.NoOp, IDiskOp(D.NoDiskOp), StatesInternalOp);
  }

  method pushSync(linear inout s: Full)
  returns (id: uint64)
  requires old_s.Inv()
  ensures s.WF()
  ensures M.Next(old_s.I(), s.I(),
       if id == 0 then UI.NoOp else UI.PushSyncOp(id as int),
       D.NoDiskOp)
  {
    // CoordinationModel.reveal_pushSync();
    id := inout s.jc.pushSync();

    ghost var uiop := if id == 0 then UI.NoOp else UI.PushSyncOp(id as int);
    ghost var vop := if id == 0 then JournalInternalOp else PushSyncOp(id as int);
    bcNoOp(old_s, s, vop);
    assert BJC.NextStep(old_s.I(), s.I(), uiop,
       BJD.DiskOp(BlockDisk.NoDiskOp, JournalDisk.NoDiskOp),
       vop);
    assert BJC.Next(old_s.I(), s.I(), uiop,
       BJD.DiskOp(BlockDisk.NoDiskOp, JournalDisk.NoDiskOp));
    assert M.Next(old_s.I(), s.I(),
       if id == 0 then UI.NoOp else UI.PushSyncOp(id as int),
       D.NoDiskOp);
  }

  method receiveLoc(linear inout s: Variables, loc: DiskLayout.Location)
  requires old_s.WFBCVars()
  requires DiskLayout.ValidIndirectionTableLocation(loc)
  requires old_s.Unready?
  ensures s.WFBCVars()
  ensures BBC.Next(old_s.I(), s.I(), BlockDisk.NoDiskOp, SendPersistentLocOp(loc))
  {
    linear var Unready() := s;
    s := Variables.Loading(loc, None);

    assert BC.ReceiveLoc(old_s.I(), s.I(), BlockDisk.NoDiskOp, SendPersistentLocOp(loc));
    assert BC.NextStep(old_s.I(), s.I(), BlockDisk.NoDiskOp, SendPersistentLocOp(loc), BC.ReceiveLocStep);
    assert BBC.NextStep(old_s.I(), s.I(), BlockDisk.NoDiskOp, SendPersistentLocOp(loc), BBC.BlockCacheMoveStep(BC.ReceiveLocStep));
  }

  method initialization(linear inout s: Full, io: DiskIOHandler)
  requires old_s.Inv()
  requires io.initialized()
  modifies io
  ensures s.WF()
  ensures M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)))
  {
    if s.jc.status.StatusLoadingSuperblock? {
      if s.jc.superblock1.SuperblockSuccess?
          && s.jc.superblock2.SuperblockSuccess? {
        inout s.jc.finishLoadingSuperblockPhase();
        var loc := s.jc.superblock.indirectionTableLoc;
        receiveLoc(inout s.bc, loc);

        assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), SendPersistentLocOp(loc));
        assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
        assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
      } else if s.jc.superblock1Read.None?
          && s.jc.superblock1.SuperblockUnfinished? {
        inout s.jc.pageInSuperblockReq(io, 0);
        bcNoOp(old_s, s, JournalInternalOp);
        assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), JournalInternalOp);
        assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
        assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
      } else if s.jc.superblock2Read.None?
          && s.jc.superblock2.SuperblockUnfinished? {
        inout s.jc.pageInSuperblockReq(io, 1);
        bcNoOp(old_s, s, JournalInternalOp);
        assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), JournalInternalOp);
        assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
        assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
      } else {
        print "initialization: doing nothing, superblock reads out\n";
        noop(s);
      }
    } else if s.jc.status.StatusLoadingOther? {
      inout s.jc.tryFinishLoadingOtherPhase(io);

      bcNoOp(old_s, s, JournalInternalOp);
      assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), JournalInternalOp);
      assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
      assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
    } else if s.bc.Loading?
        && s.bc.indirectionTableRead.None? {
      IOImpl.PageInIndirectionTableReq(inout s.bc, io);

      jcNoOp(old_s, s, StatesInternalOp);
      assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), StatesInternalOp);
      assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
      assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
    } else if s.bc.Ready? {
      var isEmpty := s.jc.isReplayEmpty();
      if !isEmpty {
        var je := s.jc.journalist.replayJournalTop();
        var success := InsertImpl.insert(inout s.bc, io, je.key, je.value, true);
        if success {
          inout s.jc.journalReplayOne(je);
        }

        ghost var g := true;
        if g && !success && old_s.jc == s.jc {
          ghost var vop;
          if BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp) {
            vop := StatesInternalOp;
          } else {
            vop := AdvanceOp(UI.NoOp, true);
          }
          jcNoOp(old_s, s, vop);
          assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), vop);
          assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
          assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));        
        } else {
          ghost var vop := AdvanceOp(UI.PutOp(je.key, je.value), true);
          assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), vop);
          assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
          assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
        }
      } else {
        print "initialization: doing nothing, no replay journal\n";
        noop(s);
      }
    } else {
      print "initialization: doing nothing\n";
      noop(s);
    }
  }

  method doSync(
      linear inout s: Full, io: DiskIOHandler, graphSync: bool)
  returns (wait: bool)
  requires old_s.Inv()
  requires io.initialized()
  requires old_s.bc.Ready?
  requires old_s.jc.Inv() // [yizhou7][NOTE]: this is implied by s.Inv(), but opaqued
  requires old_s.jc.status.StatusReady?

  // [yizhou7] this additional precondition is added
  requires old_s.jc.journalist.I().replayJournal == []

  modifies io
  ensures s.WF()
  ensures M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)))
  {
    wait := false;

    if s.jc.isFrozen {
      if s.jc.frozenLoc.Some? {
        wait := inout s.jc.tryAdvanceLocation(io);

        ghost var uiop := UI.NoOp;
        ghost var vop := JournalInternalOp;
        bcNoOp(old_s, s, vop);
        assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
        assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
        assert M.Next(old_s.I(), s.I(), uiop, diskOp(IIO(io)));
      } else {
        var froze, wait0 := SyncImpl.sync(inout s.bc, io);
        wait := wait0;
        // assert s.bc.frozenIndirectionTable.lSome?;
        assert froze == false; // && old_s.jc == s.jc;
        
        ghost var uiop := UI.NoOp;

        assert BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp) || BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, AdvanceOp(UI.NoOp, true));
        if BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp) {
          ghost var vop := StatesInternalOp;
          jcNoOp(old_s, s, vop);
          assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
          assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
          assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
        } else {
          var vop := AdvanceOp(UI.NoOp, true);
          assert BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, vop);
          jcNoOp(old_s, s, vop);
          assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
          assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
          assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
        }
      }
    } else if s.jc.superblockWrite.Some? {
      wait := true;
      noop(s);
    } else {
      if graphSync {
        var froze, wait0 := SyncImpl.sync(inout s.bc, io);
        wait := wait0;
        if froze {
          inout s.jc.freeze();
          assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), FreezeOp);
          assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
          assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
        } else {
            ghost var uiop := UI.NoOp;
            if BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp) {
              var vop := StatesInternalOp;
              jcNoOp(old_s, s, vop);
              assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
              assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
              assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
            } else {
              var vop := AdvanceOp(UI.NoOp, true);
              assert BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, vop);
              jcNoOp(old_s, s, vop);
              assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
              assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
              assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
            }

            assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
        }
      } else {
        wait := inout s.jc.tryAdvanceLog(io);

        ghost var uiop := UI.NoOp;
        ghost var vop := JournalInternalOp;
        bcNoOp(old_s, s, vop);
        assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
        assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
        assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
      }
    }
  }

  method getCommitterSyncState(shared s: Full, id: uint64) returns (res: Option<JC.SyncReqStatus>)
  requires s.Inv()
  ensures var contents := s.jc.syncReqs.contents;
    && (if id in contents then res == Some(contents[id]) else res.None?)
    && (res.Some? <==> id in s.jc.syncReqs.contents)
  {
    res := LinearMutableMap.Get(s.jc.syncReqs, id);
  }

  function method isCommitterStatusReady(shared s: Full) : bool
  requires s.WF()
  {
    s.jc.status.StatusReady?
  }

  function method isInitialized(shared s: Full) : (b: bool)
  requires s.Inv()
  {
    if (
      && s.bc.Ready?
      && isCommitterStatusReady(s)
    ) then
      s.jc.isReplayEmpty()
    else
      false
  }

  method popSync(
      linear inout s: Full, io: DiskIOHandler, id: uint64, graphSync: bool)
  returns (success: bool, wait: bool)
  requires old_s.Inv()
  requires io.initialized()
  modifies io
  ensures s.WF()
  ensures M.Next(old_s.I(), s.I(),
        if success then UI.PopSyncOp(id as int) else UI.NoOp,
        diskOp(IIO(io)))
  {
    wait := false;

    var committerSyncState := getCommitterSyncState(s, id);
    assert committerSyncState.Some? <==> id in s.jc.syncReqs.contents;

    if committerSyncState == Some(JC.State1) {
      inout s.jc.popSync(id);
      success := true;

      ghost var uiop := if success then UI.PopSyncOp(id as int) else UI.NoOp;
      ghost var vop := if success then PopSyncOp(id as int) else JournalInternalOp;
      bcNoOp(old_s, s, vop);
      assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
      assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
      assert M.Next(old_s.I(), s.I(), uiop, diskOp(IIO(io)));
    } else {
      var isInit := isInitialized(s);
      if !isInit {
        initialization(inout s, io);
        success := false;
        assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
      } else {
        wait := doSync(inout s, io, graphSync);
        success := false;
      }
    }
  }

  method query(linear inout s: Full, io: DiskIOHandler, key: Key)
  returns (result: Option<Value>) 
  requires old_s.Inv() 
  requires io.initialized()
  modifies io
  ensures s.WF()
  ensures M.Next(old_s.I(), s.I(),
          if result.Some? then UI.GetOp(key, result.value) else UI.NoOp,
          diskOp(IIO(io)))
  {
    var is_init := isInitialized(s);
    if !is_init {
      initialization(inout s, io);
      result := None;
    } else {
      result := QueryImpl.query(inout s.bc, io, key);
      
      if result.Some? {
        ghost var uiop := UI.GetOp(key, result.value);
        ghost var vop := AdvanceOp(uiop, false);

        assert JC.Advance(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);
        assert JC.NextStep(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop, JC.AdvanceStep);
        assert JC.Next(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);

        assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
        assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
      } else {
        ghost var uiop := UI.NoOp;
        if BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp) {
          ghost var vop := StatesInternalOp;
          assert JC.NoOp(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop, JC.NoOpStep);
          assert JC.Next(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
          assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
        } else {
          ghost var vop := AdvanceOp(uiop, true);
          // Not a true replay (empty journal entry list).
          assert JC.Replay(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop, JC.ReplayStep);
          assert JC.Next(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
          assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
        }
      }
    }
  }

  method succ(
      linear inout s: Full, io: DiskIOHandler, start: UI.RangeStart, maxToFind: uint64)
  returns (result: Option<UI.SuccResultList>)
  requires maxToFind >= 1
  requires old_s.Inv() 
  requires io.initialized()
  modifies io
  ensures s.WF()
  ensures M.Next(old_s.I(), s.I(),
          if result.Some? then UI.SuccOp(start, result.value.results, result.value.end) else UI.NoOp,
          diskOp(IIO(io)))
  {
    var is_init := isInitialized(s);
    if !is_init {
      initialization(inout s, io);
      result := None;
    } else {
      result := SuccImpl.doSucc(inout s.bc, io, start, maxToFind);

      if result.Some? {
        ghost var uiop := UI.SuccOp(start, result.value.results, result.value.end);
        ghost var vop := AdvanceOp(uiop, false);

        assert JC.Advance(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);
        assert JC.NextStep(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop, JC.AdvanceStep);
        assert JC.Next(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);

        assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
        assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
      } else {
        ghost var uiop := UI.NoOp;
        if BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp) {
          ghost var vop := StatesInternalOp;
          assert JC.NoOp(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop, JC.NoOpStep);
          assert JC.Next(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
          assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
        } else {
          ghost var vop := AdvanceOp(uiop, true);
          // Not a true replay (empty journal entry list).
          assert JC.Replay(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);
          assert JC.NextStep(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop, JC.ReplayStep);
          assert JC.Next(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);
          assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
          assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
        }
      }
    }
  }

  function method canJournalistAppend(shared s: Full, key: Key, value: Value) : (b: bool)
  requires s.WF()
  {
    s.jc.journalist.canAppend(Journal.JournalInsert(key, value))
  }

  method insert(
      linear inout s: Full, io: DiskIOHandler, key: Key, value: Value)
  returns (success: bool)
  requires old_s.Inv() 
  requires io.initialized()
  modifies io
  ensures s.WF()
  ensures M.Next(old_s.I(), s.I(),
          if success then UI.PutOp(key, value) else UI.NoOp,
          diskOp(IIO(io)))
  {
    var is_init := isInitialized(s);
    if !is_init {
      initialization(inout s, io);
      success := false;
    } else {
      var can_append := canJournalistAppend(s, key, value);
      if can_append {
        success := InsertImpl.insert(inout s.bc, io, key, value, false);
        if success {
          inout s.jc.journalAppend(key, value);
          ghost var uiop := UI.PutOp(key, value);
          ghost var vop := AdvanceOp(uiop, false);

          assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
          assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
        } else {
          ghost var uiop := UI.NoOp;
          if BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, StatesInternalOp) {
            ghost var vop := StatesInternalOp;
            assert JC.NoOp(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);
            assert JC.NextStep(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop, JC.NoOpStep);
            assert JC.Next(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);
            assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
            assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
          } else {
            ghost var vop := AdvanceOp(uiop, true);
            // Not a true replay (empty journal entry list).
            assert JC.Replay(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);
            assert JC.NextStep(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop, JC.ReplayStep);
            assert JC.Next(old_s.jc.I(), s.jc.I(), JournalDisk.NoDiskOp, vop);
            assert BJC.NextStep(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))), vop);
            assert BJC.Next(old_s.I(), s.I(), uiop, IDiskOp(diskOp(IIO(io))));
          }
        }
      } else {
        var wait := doSync(inout s, io, true /* graphSync */);
        success := false;
      }
    }
  }
}
