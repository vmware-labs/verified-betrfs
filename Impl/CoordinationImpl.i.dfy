include "CoordinationModel.i.dfy"
include "FullImpl.i.dfy"
include "CommitterCommitImpl.i.dfy"
include "CommitterInitImpl.i.dfy"
include "CommitterAppendImpl.i.dfy"
include "CommitterReplayImpl.i.dfy"
include "QueryImpl.i.dfy"
include "InsertImpl.i.dfy"
include "SuccImpl.i.dfy"

module CoordinationImpl {
  import opened StateImpl
  import opened Options
  import CommitterCommitImpl
  import CommitterInitImpl
  import CommitterAppendImpl
  import CommitterReplayImpl
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

  method pushSync(k: ImplConstants, s: Full)
  returns (id: uint64)
  requires s.Inv(k)
  modifies s.Repr
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures (s.I(), id) == CoordinationModel.pushSync(Ic(k), old(s.I()))
  {
    s.reveal_ReprInv();
    CoordinationModel.reveal_pushSync();

    id := CommitterCommitImpl.pushSync(k, s.jc);

    s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
    s.reveal_ReprInv();
  }

  method receiveLoc(k: ImplConstants, s: Variables, loc: DiskLayout.Location)
  requires s.WF()
  modifies s.Repr()
  ensures WellUpdated(s)
  ensures s.I() == CoordinationModel.receiveLoc(Ic(k), old(s.I()), loc)
  {
    CoordinationModel.reveal_receiveLoc();

    s.loading := true;
    s.ready := false;
    s.indirectionTableLoc := loc;
    s.indirectionTableRead := None;
  }

  method initialization(k: ImplConstants, s: Full, io: DiskIOHandler)
  requires s.Inv(k)
  requires io.initialized()
  requires io !in s.Repr
  modifies s.Repr
  modifies io
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures CoordinationModel.initialization(Ic(k), old(s.I()), old(IIO(io)), s.I(), IIO(io))
  {
    CoordinationModel.reveal_initialization();
    s.reveal_ReprInv();

    if s.jc.status.StatusLoadingSuperblock? {
      if s.jc.superblock1.SuperblockSuccess?
          && s.jc.superblock2.SuperblockSuccess? {
        CommitterInitImpl.FinishLoadingSuperblockPhase(k, s.jc);
        receiveLoc(k, s.bc, s.jc.superblock.indirectionTableLoc);
      } else if s.jc.superblock1Read.None?
          && s.jc.superblock1.SuperblockUnfinished? {
        CommitterInitImpl.PageInSuperblockReq(k, s.jc, io, 0);
      } else if s.jc.superblock2Read.None?
          && s.jc.superblock2.SuperblockUnfinished? {
        CommitterInitImpl.PageInSuperblockReq(k, s.jc, io, 1);
      } else {
        print "initialization: doing nothing, superblock reads out\n";
      }
    } else if s.jc.status.StatusLoadingOther? {
      CommitterInitImpl.tryFinishLoadingOtherPhase(k, s.jc, io);
    } else if s.bc.loading && !s.bc.ready
        && s.bc.indirectionTableRead.None? {
      IOImpl.PageInIndirectionTableReq(k, s.bc, io);
    } else if s.bc.ready {
      var isEmpty := CommitterInitImpl.isReplayEmpty(s.jc);
      if !isEmpty {
        var je := s.jc.journalist.replayJournalTop();
        var success := InsertImpl.insert(k, s.bc, io, je.key, je.value);
        if success {
          CommitterReplayImpl.JournalReplayOne(k, s.jc);
        }
      } else {
        print "initialization: doing nothing, no replay journal\n";
      }
    } else {
      print "initialization: doing nothing\n";
    }

    s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
    s.reveal_ReprInv();
    assert s.ProtectedReprInv();
  }

  method doSync(
      k: ImplConstants, s: Full, io: DiskIOHandler, graphSync: bool)
  returns (wait: bool)
  requires s.Inv(k)
  requires io.initialized()
  requires io !in s.Repr
  requires s.bc.ready
  requires s.jc.status.StatusReady?
  modifies s.Repr
  modifies io
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures CoordinationModel.doSync(
      Ic(k), old(s.I()), old(IIO(io)), graphSync, s.I(), IIO(io))
  {
    //CoordinationModel.reveal_doSync();
    s.reveal_ReprInv();

    wait := false;

    if s.jc.isFrozen {
      if s.jc.frozenLoc.Some? {
        wait := CommitterCommitImpl.tryAdvanceLocation(k, s.jc, io);
      } else {
        var froze, wait0 := SyncImpl.sync(k, s.bc, io);
        wait := wait0;

        /*s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
        s.reveal_ReprInv();
        assert 
          && SyncModel.sync(Ic(k), old(s.I()).bc, old(IIO(io)), s.I().bc, IIO(io), froze)
          && old(s.I()).jc == s.I().jc;*/
      }
    } else if s.jc.superblockWrite.Some? {
      //print "doSync: doing nothing, superblock write out\n";
      wait := true;
    } else {
      if graphSync {
        var froze, wait0 := SyncImpl.sync(k, s.bc, io);
        wait := wait0;
        if froze {
          CommitterCommitImpl.freeze(k, s.jc);
        }
      } else {
        wait := CommitterCommitImpl.tryAdvanceLog(k, s.jc, io);
      }
    }

    s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
    s.reveal_ReprInv();
  }

  method popSync(
      k: ImplConstants, s: Full, io: DiskIOHandler, id: uint64, graphSync: bool)
  returns (success: bool, wait: bool)
  requires s.Inv(k)
  requires io.initialized()
  requires s.Inv(k)
  requires io.initialized()
  requires io !in s.Repr
  modifies s.Repr
  modifies io
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures CoordinationModel.popSync(
      Ic(k), old(s.I()), old(IIO(io)), id, graphSync,
      s.I(), IIO(io), success)
  {
    CoordinationModel.reveal_popSync();
    s.reveal_ReprInv();

    wait := false;

    var syncState := s.jc.syncReqs.Get(id);
    if syncState == Some(JC.State1) {
      CommitterCommitImpl.popSync(k, s.jc, id);
      success := true;

      s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
      s.reveal_ReprInv();
      assert s.ProtectedReprInv();
    } else {
      var isInit := isInitialized(s);
      if !isInit {
        initialization(k, s, io);
        success := false;
      } else {
        wait := doSync(k, s, io, graphSync);
        success := false;
      }
    }
  }

  method isInitialized(s: Full) returns (b: bool)
  requires s.WF()
  ensures b == CoordinationModel.isInitialized(s.I())
  {
    if (
      && s.bc.ready
      && s.jc.status.StatusReady?
    ) {
      b := CommitterInitImpl.isReplayEmpty(s.jc);
    } else {
      b := false;
    }
  }

  method query(k: ImplConstants, s: Full, io: DiskIOHandler, key: Key)
  returns (result: Option<Value>) 
  requires s.Inv(k) 
  requires io.initialized()
  requires io !in s.Repr
  modifies s.Repr
  modifies io
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures CoordinationModel.query(
      Ic(k), old(s.I()), old(IIO(io)), key,
      s.I(), result, IIO(io))
  {
    CoordinationModel.reveal_query();
    s.reveal_ReprInv();

    var is_init := isInitialized(s);
    if !is_init {
      initialization(k, s, io);
      result := None;
    } else {
      result := QueryImpl.query(k, s.bc, io, key);

      s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
      s.reveal_ReprInv();
      assert s.ProtectedReprInv();
    }
  }

  method succ(
      k: ImplConstants, s: Full, io: DiskIOHandler, start: UI.RangeStart, maxToFind: uint64)
  returns (result: Option<UI.SuccResultList>)
  requires maxToFind >= 1
  requires s.Inv(k) 
  requires io.initialized()
  requires io !in s.Repr
  modifies s.Repr
  modifies io
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures CoordinationModel.succ(
      Ic(k), old(s.I()), old(IIO(io)), start, maxToFind as int,
      s.I(), result, IIO(io))
  {
    CoordinationModel.reveal_succ();
    s.reveal_ReprInv();

    var is_init := isInitialized(s);
    if !is_init {
      initialization(k, s, io);
      result := None;
    } else {
      result := SuccImpl.doSucc(k, s.bc, io, start, maxToFind);

      s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
      s.reveal_ReprInv();
      assert s.ProtectedReprInv();
    }
  }

  method insert(
      k: ImplConstants, s: Full, io: DiskIOHandler, key: Key, value: Value)
  returns (success: bool)
  requires s.Inv(k) 
  requires io.initialized()
  requires io !in s.Repr
  modifies s.Repr
  modifies io
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures CoordinationModel.insert(
      Ic(k), old(s.I()), old(IIO(io)), key, value,
      s.I(), success, IIO(io))

  {
    CoordinationModel.reveal_insert();
    s.reveal_ReprInv();

    var is_init := isInitialized(s);
    if !is_init {
      initialization(k, s, io);
      success := false;
    } else {
      var can_append := s.jc.journalist.canAppend(
          Journal.JournalInsert(key, value));
      if can_append {
        success := InsertImpl.insert(k, s.bc, io, key, value);
        if success {
          CommitterAppendImpl.JournalAppend(k, s.jc, key, value);
        }

        s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
        s.reveal_ReprInv();
        assert s.ProtectedReprInv();
      } else {
        var wait := doSync(k, s, io, true /* graphSync */);
        success := false;
      }
    }
  }
}
