include "CoordinationModel.i.dfy"
include "FullImpl.i.dfy"
// include "CommitterCommitImpl.i.dfy"
// include "CommitterInitImpl.i.dfy"
// include "CommitterAppendImpl.i.dfy"
// include "CommitterReplayImpl.i.dfy"
include "QueryImpl.i.dfy"
include "InsertImpl.i.dfy"
include "SuccImpl.i.dfy"

module CoordinationImpl {
  import opened StateBCImpl
  import opened Options
  // import CommitterCommitImpl
  // import CommitterInitImpl
  // import CommitterAppendImpl
  // import CommitterReplayImpl
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
  import SyncModel
  import CoordinationModel
  import opened MainDiskIOHandler
  import opened LinearMutableMap

  method pushSync(linear inout s: Full)
  returns (id: uint64)
  requires old_s.Inv()
  ensures s.W()
  ensures (s.I(), id) == CoordinationModel.pushSync(old_s.I())
  {
    CoordinationModel.reveal_pushSync();

    id := inout s.jc.pushSync();
  }

  method receiveLoc(linear inout s: Variables, loc: DiskLayout.Location)
  requires old_s.WF()
  ensures s.W()
  ensures s.I() == CoordinationModel.receiveLoc(old_s.I(), loc)
  {
    CoordinationModel.reveal_receiveLoc();

    inout s.loading := true;
    inout s.Ready? := false;
    inout s.indirectionTableLoc := loc;
    inout s.indirectionTableRead := None;
  }

  // [yizhou7][FIXME]: this takes long to verify
  method initialization(linear inout s: Full, io: DiskIOHandler)
  requires old_s.Inv()
  requires io.initialized()
  modifies io
  ensures s.W()
  ensures CoordinationModel.initialization(old_s.I(), old(IIO(io)), s.I(), IIO(io))
  {
    CoordinationModel.reveal_initialization();

    if s.jc.status.StatusLoadingSuperblock? {
      if s.jc.superblock1.SuperblockSuccess?
          && s.jc.superblock2.SuperblockSuccess? {
        inout s.jc.finishLoadingSuperblockPhase();
        var loc := s.jc.superblock.indirectionTableLoc;
        receiveLoc(inout s.bc, loc);
      } else if s.jc.superblock1Read.None?
          && s.jc.superblock1.SuperblockUnfinished? {
        inout s.jc.pageInSuperblockReq(io, 0);
      } else if s.jc.superblock2Read.None?
          && s.jc.superblock2.SuperblockUnfinished? {
        inout s.jc.pageInSuperblockReq(io, 1);
      } else {
        print "initialization: doing nothing, superblock reads out\n";
      }
    } else if s.jc.status.StatusLoadingOther? {
      inout s.jc.tryFinishLoadingOtherPhase(io);
    } else if s.bc.loading && !s.bc.ready
        && s.bc.indirectionTableRead.None? {
      IOImpl.PageInIndirectionTableReq(inout s.bc, io);
    } else if s.bc.ready {
      var isEmpty := s.jc.isReplayEmpty();
      if !isEmpty {
        var je := s.jc.journalist.replayJournalTop();
        var success := InsertImpl.insert(inout s.bc, io, je.key, je.value);
        if success {
          inout s.jc.journalReplayOne(je);
        }
      } else {
        print "initialization: doing nothing, no replay journal\n";
      }
    } else {
      print "initialization: doing nothing\n";
    }

  }

  method doSync(
      linear inout s: Full, io: DiskIOHandler, graphSync: bool)
  returns (wait: bool)
  requires old_s.Inv()
  requires io.initialized()
  requires old_s.bc.ready
  requires old_s.jc.Inv() // [yizhou7][NOTE]: this is implied by s.Inv(), but opaqued
  requires old_s.jc.status.StatusReady?

  // [yizhou7] this additional precondition is added
  requires old_s.jc.journalist.I().replayJournal == []

  modifies io
  ensures s.W()
  ensures CoordinationModel.doSync(
      old_s.I(), old(IIO(io)), graphSync, s.I(), IIO(io))
  {

    wait := false;

    if s.jc.isFrozen {
      if s.jc.frozenLoc.Some? {
        wait := inout s.jc.tryAdvanceLocation(io);
      } else {
        var froze, wait0 := SyncImpl.sync(inout s.bc, io);
        wait := wait0;
      }
    } else if s.jc.superblockWrite.Some? {
      wait := true;
    } else {
      if graphSync {
        var froze, wait0 := SyncImpl.sync(inout s.bc, io);
        wait := wait0;
        if froze {
          inout s.jc.freeze();
        }
      } else {
        wait := inout s.jc.tryAdvanceLog(io);
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
  ensures b == CoordinationModel.isInitialized(s.I())
  {
    if (
      && s.bc.ready
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
  // requires old_s.Inv()
  // requires io.initialized()
  modifies io
  ensures s.W()
  ensures CoordinationModel.popSync(
      old_s.I(), old(IIO(io)), id, graphSync,
      s.I(), IIO(io), success)
  {
    CoordinationModel.reveal_popSync();

    wait := false;

    var committerSyncState := getCommitterSyncState(s, id);
    assert committerSyncState.Some? <==> id in s.jc.syncReqs.contents;

    if committerSyncState == Some(JC.State1) {
      inout s.jc.popSync(id);
      success := true;
    } else {
      var isInit := isInitialized(s);
      if !isInit {
        initialization(inout s, io);
        success := false;
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
  ensures s.W()
  ensures CoordinationModel.query(
      old_s.I(), old(IIO(io)), key,
      s.I(), result, IIO(io))
  {
    CoordinationModel.reveal_query();

    var is_init := isInitialized(s);
    if !is_init {
      initialization(inout s, io);
      result := None;
    } else {
      result := QueryImpl.query(inout s.bc, io, key);

    }
  }

  method succ(
      linear inout s: Full, io: DiskIOHandler, start: UI.RangeStart, maxToFind: uint64)
  returns (result: Option<UI.SuccResultList>)
  requires maxToFind >= 1
  requires old_s.Inv() 
  requires io.initialized()
  modifies io
  ensures s.W()
  ensures CoordinationModel.succ(
      old_s.I(), old(IIO(io)), start, maxToFind as int,
      s.I(), result, IIO(io))
  {
    CoordinationModel.reveal_succ();

    var is_init := isInitialized(s);
    if !is_init {
      initialization(inout s, io);
      result := None;
    } else {
      result := SuccImpl.doSucc(inout s.bc, io, start, maxToFind);

    }
  }

  function method canJournalistAppend(shared s: Full, key: Key, value: Value) : (b: bool)
  requires s.WF()
  {
    s.jc.journalist.canAppend(Journal.JournalInsert(key, value))
  }

  // [yizhou7][FIXME]: this takes long to verify
  method insert(
      linear inout s: Full, io: DiskIOHandler, key: Key, value: Value)
  returns (success: bool)
  requires old_s.Inv() 
  requires io.initialized()
  modifies io
  ensures s.W()
  ensures CoordinationModel.insert(
      old_s.I(), old(IIO(io)), key, value,
      s.I(), success, IIO(io))
  {
    CoordinationModel.reveal_insert();

    var is_init := isInitialized(s);
    if !is_init {
      initialization(inout s, io);
      success := false;
    } else {
      var can_append := canJournalistAppend(s, key, value);
      if can_append {
        success := InsertImpl.insert(inout s.bc, io, key, value);
        if success {
          inout s.jc.journalAppend(key, value);
        }
      } else {
        var wait := doSync(inout s, io, true /* graphSync */);
        success := false;
      }
    }
  }
}
