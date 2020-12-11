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

  method pushSync(s: Full)
  returns (id: uint64)
  requires s.Inv()
  modifies s.Repr
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures (s.I(), id) == CoordinationModel.pushSync(old(s.I()))
  {
    s.reveal_ReprInv();
    CoordinationModel.reveal_pushSync();

    linear var jc := s.jc.Take();
    id := inout jc.pushSync();
    s.jc.Give(jc);

    s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
    s.reveal_ReprInv();
  }

  method receiveLoc(s: Variables, loc: DiskLayout.Location)
  requires s.WF()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == CoordinationModel.receiveLoc(old(s.I()), loc)
  {
    CoordinationModel.reveal_receiveLoc();

    s.loading := true;
    s.ready := false;
    s.indirectionTableLoc := loc;
    s.indirectionTableRead := None;
  }

  // [yizhou7][FIXME]: this takes long to verify
  method initialization(s: Full, io: DiskIOHandler)
  requires s.Inv()
  requires io.initialized()
  requires io !in s.Repr
  modifies s.Repr
  modifies io
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures CoordinationModel.initialization(old(s.I()), old(IIO(io)), s.I(), IIO(io))
  {
    CoordinationModel.reveal_initialization();
    s.reveal_ReprInv();

    linear var jc := s.jc.Take();

    if jc.status.StatusLoadingSuperblock? {
      if jc.superblock1.SuperblockSuccess?
          && jc.superblock2.SuperblockSuccess? {
        inout jc.FinishLoadingSuperblockPhase();
        receiveLoc(s.bc, jc.superblock.indirectionTableLoc);
      } else if jc.superblock1Read.None?
          && jc.superblock1.SuperblockUnfinished? {
        inout jc.PageInSuperblockReq(io, 0);
      } else if jc.superblock2Read.None?
          && jc.superblock2.SuperblockUnfinished? {
        inout jc.PageInSuperblockReq(io, 1);
      } else {
        print "initialization: doing nothing, superblock reads out\n";
      }
    } else if jc.status.StatusLoadingOther? {
      inout jc.tryFinishLoadingOtherPhase(io);
    } else if s.bc.loading && !s.bc.ready
        && s.bc.indirectionTableRead.None? {
      IOImpl.PageInIndirectionTableReq(s.bc, io);
    } else if s.bc.ready {
      var isEmpty := jc.isReplayEmpty();
      if !isEmpty {
        var je := jc.journalist.replayJournalTop();
        var success := InsertImpl.insert(s.bc, io, je.key, je.value);
        if success {
          inout jc.JournalReplayOne();
        }
      } else {
        print "initialization: doing nothing, no replay journal\n";
      }
    } else {
      print "initialization: doing nothing\n";
    }

    s.jc.Give(jc);
    s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
    s.reveal_ReprInv();
    assert s.ProtectedReprInv();
  }

  method doSync(
      s: Full, io: DiskIOHandler, graphSync: bool)
  returns (wait: bool)
  requires s.Inv()
  requires io.initialized()
  requires io !in s.Repr
  requires s.bc.ready
  requires s.jc.Inv() // [yizhou7][NOTE]: this is implied by s.Inv(), but opaqued
  requires s.jc.Read().status.StatusReady?
  modifies s.Repr
  modifies io
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures CoordinationModel.doSync(
      old(s.I()), old(IIO(io)), graphSync, s.I(), IIO(io))
  {
    s.reveal_ReprInv();

    linear var jc := s.jc.Take();
    wait := false;

    if jc.isFrozen {
      if jc.frozenLoc.Some? {
        wait := inout jc.tryAdvanceLocation(io);
      } else {
        var froze, wait0 := SyncImpl.sync(s.bc, io);
        wait := wait0;

        /*s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
        s.reveal_ReprInv();
        assert 
          && SyncModel.sync(old(s.I()).bc, old(IIO(io)), s.I().bc, IIO(io), froze)
          && old(s.I()).jc == s.I().jc;*/
      }
    } else if jc.superblockWrite.Some? {
      wait := true;
    } else {
      if graphSync {
        var froze, wait0 := SyncImpl.sync(s.bc, io);
        wait := wait0;
        if froze {
          inout jc.freeze();
        }
      } else {
        wait := inout jc.tryAdvanceLog(io);
      }
    }

    s.jc.Give(jc);
    s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
    s.reveal_ReprInv();
  }

  function method getCommitterSyncState(s: Full, id: uint64) : Option<JC.SyncReqStatus>
  requires s.WF()
  reads s.Repr
  {
    s.reveal_ReprInv();
    LinearMutableMap.Get(s.jc.Borrow().syncReqs, id)
  }

  function method isCommitterStatusReady(s: Full) : bool
  requires s.WF()
  reads s.Repr
  {
    s.reveal_ReprInv();
    s.jc.Borrow().status.StatusReady?
  }

  method isInitialized(s: Full) returns (b: bool)
  requires s.WF()
  ensures b == CoordinationModel.isInitialized(s.I())
  {
    s.reveal_ReprInv();
    if (
      && s.bc.ready
      && isCommitterStatusReady(s)
    ) {
      b := s.jc.Borrow().isReplayEmpty();
    } else {
      b := false;
    }
  }

  method popSync(
      s: Full, io: DiskIOHandler, id: uint64, graphSync: bool)
  returns (success: bool, wait: bool)
  requires s.Inv()
  requires io.initialized()
  requires s.Inv()
  requires io.initialized()
  requires io !in s.Repr
  modifies s.Repr
  modifies io
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures CoordinationModel.popSync(
      old(s.I()), old(IIO(io)), id, graphSync,
      s.I(), IIO(io), success)
  {
    CoordinationModel.reveal_popSync();
    s.reveal_ReprInv();

    wait := false;

    if getCommitterSyncState(s, id) == Some(JC.State1) {
      linear var jc := s.jc.Take();
      inout jc.popSync(id);
      success := true;
      s.jc.Give(jc);
      s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
      s.reveal_ReprInv();
      assert s.ProtectedReprInv();
    } else {
      var isInit := isInitialized(s);
      if !isInit {
        initialization(s, io);
        success := false;
      } else {
        wait := doSync(s, io, graphSync);
        success := false;
      }
    }
  }

  method query(s: Full, io: DiskIOHandler, key: Key)
  returns (result: Option<Value>) 
  requires s.Inv() 
  requires io.initialized()
  requires io !in s.Repr
  modifies s.Repr
  modifies io
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures CoordinationModel.query(
      old(s.I()), old(IIO(io)), key,
      s.I(), result, IIO(io))
  {
    CoordinationModel.reveal_query();
    s.reveal_ReprInv();

    var is_init := isInitialized(s);
    if !is_init {
      initialization(s, io);
      result := None;
    } else {
      result := QueryImpl.query(s.bc, io, key);

      s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
      s.reveal_ReprInv();
      assert s.ProtectedReprInv();
    }
  }

  method succ(
      s: Full, io: DiskIOHandler, start: UI.RangeStart, maxToFind: uint64)
  returns (result: Option<UI.SuccResultList>)
  requires maxToFind >= 1
  requires s.Inv() 
  requires io.initialized()
  requires io !in s.Repr
  modifies s.Repr
  modifies io
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures CoordinationModel.succ(
      old(s.I()), old(IIO(io)), start, maxToFind as int,
      s.I(), result, IIO(io))
  {
    CoordinationModel.reveal_succ();
    s.reveal_ReprInv();

    var is_init := isInitialized(s);
    if !is_init {
      initialization(s, io);
      result := None;
    } else {
      result := SuccImpl.doSucc(s.bc, io, start, maxToFind);

      s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
      s.reveal_ReprInv();
      assert s.ProtectedReprInv();
    }
  }

  function method canJournalistAppend(s: Full, key: Key, value: Value) : (b: bool)
  requires s.WF()
  reads s.Repr
  {
    s.reveal_ReprInv();
    s.jc.Borrow().journalist.canAppend(Journal.JournalInsert(key, value))
  }

  // [yizhou7][FIXME]: this takes long to verify
  method insert(
      s: Full, io: DiskIOHandler, key: Key, value: Value)
  returns (success: bool)
  requires s.Inv() 
  requires io.initialized()
  requires io !in s.Repr
  modifies s.Repr
  modifies io
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures CoordinationModel.insert(
      old(s.I()), old(IIO(io)), key, value,
      s.I(), success, IIO(io))
  {
    CoordinationModel.reveal_insert();
    s.reveal_ReprInv();

    var is_init := isInitialized(s);
    if !is_init {
      initialization(s, io);
      success := false;
    } else {
      var can_append := canJournalistAppend(s, key, value);
      if can_append {
        success := InsertImpl.insert(s.bc, io, key, value);
        if success {
          linear var jc := s.jc.Take();
          inout jc.JournalAppend(key, value);
          s.jc.Give(jc);
        }
        s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
        s.reveal_ReprInv();
        assert s.ProtectedReprInv();
      } else {
        var wait := doSync(s, io, true /* graphSync */);
        success := false;
      }
    }
  }
}
