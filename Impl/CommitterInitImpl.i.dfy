include "CommitterImpl.i.dfy"
include "CommitterInitModel.i.dfy"
include "DiskOpImpl.i.dfy"
include "IOImpl.i.dfy"

module CommitterInitImpl {
  import opened NativeTypes
  import opened Options

  import opened DiskLayout
  import JC = JournalCache
  import opened Journal
  import opened JournalBytes
  import opened DiskOpImpl
  import opened MainDiskIOHandler
  import opened IOImpl
  import opened InterpretationDiskOps
  import StateImpl
  import SectorType
  import MutableMapModel
  import JournalistParsingImpl

  import opened CommitterImpl
  import CommitterInitModel

  method PageInSuperblockReq(
      k: ImplConstants, cm: Committer, io: DiskIOHandler, which: uint64)
  requires cm.Inv()
  requires which == 0 || which == 1
  requires which == 0 ==> cm.superblock1.SuperblockUnfinished?
  requires which == 1 ==> cm.superblock2.SuperblockUnfinished?
  requires cm.status.StatusLoadingSuperblock?
  requires io.initialized()
  requires io !in cm.Repr
  modifies io
  modifies cm.Repr
  ensures cm.W()
  ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
  ensures (cm.I(), IIO(io)) ==
      CommitterInitModel.PageInSuperblockReq(
          Ic(k), old(cm.I()), old(IIO(io)), which)
  {
    CommitterInitModel.reveal_PageInSuperblockReq();
    cm.reveal_ReprInv();

    if which == 0 {
      if cm.superblock1Read.None? {
        var loc := Superblock1Location();
        var id := RequestRead(io, loc);
        cm.superblock1Read := Some(id);
      } else {
        print "PageInSuperblockReq: doing nothing\n";
      }
    } else {
      if cm.superblock2Read.None? {
        var loc := Superblock2Location();
        var id := RequestRead(io, loc);
        cm.superblock2Read := Some(id);
      } else {
        print "PageInSuperblockReq: doing nothing\n";
      }
    }

    cm.Repr := {cm} + cm.syncReqs.Repr + cm.journalist.Repr;
    cm.reveal_ReprInv();
  }

  method FinishLoadingSuperblockPhase(k: ImplConstants, cm: Committer)
  requires cm.Inv()
  requires cm.status.StatusLoadingSuperblock?
  requires cm.superblock1.SuperblockSuccess?
  requires cm.superblock2.SuperblockSuccess?

  modifies cm.Repr
  ensures cm.W()
  ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
  ensures cm.I() ==
      CommitterInitModel.FinishLoadingSuperblockPhase(
          Ic(k), old(cm.I()));
  {
    CommitterInitModel.reveal_FinishLoadingSuperblockPhase();
    cm.reveal_ReprInv();

    var idx := if JC.increments1(
        cm.superblock1.value.counter, cm.superblock2.value.counter)
        then 1 else 0;

    var sup := if idx == 1 then
      cm.superblock2.value
    else
      cm.superblock1.value;

    cm.whichSuperblock := idx;
    cm.superblock := sup;
    cm.status := CommitterModel.StatusLoadingOther;
    cm.journalFrontRead := None;
    cm.journalBackRead := None;

    cm.Repr := {cm} + cm.syncReqs.Repr + cm.journalist.Repr;
    cm.reveal_ReprInv();
  }

  method FinishLoadingOtherPhase(k: ImplConstants, cm: Committer)
  requires cm.Inv()
  requires cm.status.StatusLoadingOther?
  modifies cm.Repr
  ensures cm.W()
  ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
  ensures cm.I() ==
      CommitterInitModel.FinishLoadingOtherPhase(
          Ic(k), old(cm.I()));
  {
    CommitterInitModel.reveal_FinishLoadingOtherPhase();
    cm.reveal_ReprInv();

    var success := cm.journalist.parseJournals();

    if success {
      cm.status := CommitterModel.StatusReady;
      cm.frozenLoc := None;
      cm.isFrozen := false;
      cm.frozenJournalPosition := 0;
      cm.superblockWrite := None;
      cm.outstandingJournalWrites := {};
      cm.newSuperblock := None;
      cm.commitStatus := JC.CommitNone;
      cm.journalist.setWrittenJournalLen(cm.superblock.journalLen);
    } else {
      print "FinishLoadingOtherPhase: there is replay journal\n";
    }

    cm.Repr := {cm} + cm.syncReqs.Repr + cm.journalist.Repr;
    cm.reveal_ReprInv();
  }

  method isReplayEmpty(cm: Committer)
  returns (b : bool)
  requires cm.WF()
  ensures b == CommitterInitModel.isReplayEmpty(cm.I())
  {
    //CommitterInitModel.reveal_isReplayEmpty();
    b := cm.journalist.isReplayEmpty();
  }

  method PageInJournalReqFront(k: ImplConstants, cm: Committer, io: DiskIOHandler)
  requires cm.WF()
  requires cm.status.StatusLoadingOther?
  requires cm.superblock.journalLen > 0
  requires io.initialized()
  requires io !in cm.Repr
  modifies cm.Repr
  modifies io
  ensures cm.W()
  ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
  ensures (cm.I(), IIO(io)) == CommitterInitModel.PageInJournalReqFront(
      Ic(k), old(cm.I()), old(IIO(io)))
  {
    CommitterInitModel.reveal_PageInJournalReqFront();
    cm.reveal_ReprInv();

    var len :=
      if cm.superblock.journalStart + cm.superblock.journalLen
          >= NumJournalBlocks()
      then
        NumJournalBlocks() - cm.superblock.journalStart
      else
        cm.superblock.journalLen;
    var loc := JournalRangeLocation(cm.superblock.journalStart, len);
    var id := RequestRead(io, loc);
    cm.journalFrontRead := Some(id);
    cm.journalBackRead :=
        if cm.journalBackRead == Some(id)
          then None else cm.journalBackRead;

    cm.Repr := {cm} + cm.syncReqs.Repr + cm.journalist.Repr;
    cm.reveal_ReprInv();
  }
  
  method PageInJournalReqBack(k: ImplConstants, cm: Committer, io: DiskIOHandler)
  requires cm.WF()
  requires cm.status.StatusLoadingOther?
  requires cm.superblock.journalLen > 0
  requires cm.superblock.journalStart + cm.superblock.journalLen > NumJournalBlocks()
  requires io.initialized()
  requires io !in cm.Repr
  modifies cm.Repr
  modifies io
  ensures cm.W()
  ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
  ensures (cm.I(), IIO(io)) == CommitterInitModel.PageInJournalReqBack(
      Ic(k), old(cm.I()), old(IIO(io)))
  {
    CommitterInitModel.reveal_PageInJournalReqBack();
    cm.reveal_ReprInv();

    var len := cm.superblock.journalStart + cm.superblock.journalLen - NumJournalBlocks();
    var loc := JournalRangeLocation(0, len);
    var id := RequestRead(io, loc);
    cm.journalBackRead := Some(id);
    cm.journalFrontRead :=
        if cm.journalFrontRead == Some(id)
          then None else cm.journalFrontRead;

    cm.Repr := {cm} + cm.syncReqs.Repr + cm.journalist.Repr;
    cm.reveal_ReprInv();
  }

  method PageInJournalResp(
      k: ImplConstants,
      cm: Committer,
      io: DiskIOHandler)
  requires cm.WF()
  requires cm.status.StatusLoadingOther?
  requires io.diskOp().RespReadOp?
  requires ValidDiskOp(io.diskOp())
  requires ValidJournalLocation(LocOfRespRead(io.diskOp().respRead))
  requires io !in cm.Repr
  modifies cm.Repr
  ensures cm.W()
  ensures cm.Repr == old(cm.Repr)
  ensures cm.I() == CommitterInitModel.PageInJournalResp(
      Ic(k), old(cm.I()), old(IIO(io)))
  {
    CommitterInitModel.reveal_PageInJournalResp();
    cm.reveal_ReprInv();

    var id, addr, bytes := io.getReadResult();
    var jr := JournalistParsingImpl.computeJournalRangeOfByteSeq(bytes);
    if jr.Some? {
      assert |jr.value| <= NumJournalBlocks() as int by {
        reveal_ValidJournalLocation();
      }

      if cm.journalFrontRead == Some(id) {
        cm.journalist.setFront(jr.value);
        cm.journalFrontRead := None;
      } else if cm.journalBackRead == Some(id) {
        cm.journalist.setBack(jr.value);
        cm.journalBackRead := None;
      }
    }

    cm.Repr := {cm} + cm.syncReqs.Repr + cm.journalist.Repr;
    cm.reveal_ReprInv();
  }

  method tryFinishLoadingOtherPhase(k: ImplConstants, cm: Committer, io: DiskIOHandler)
  requires cm.Inv()
  requires cm.status.StatusLoadingOther?
  requires io.initialized()
  requires io !in cm.Repr
  modifies cm.Repr
  modifies io
  ensures cm.W()
  ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
  ensures (cm.I(), IIO(io)) == CommitterInitModel.tryFinishLoadingOtherPhase(
      Ic(k), old(cm.I()), old(IIO(io)))
  {
    CommitterInitModel.reveal_tryFinishLoadingOtherPhase();
    cm.reveal_ReprInv();

    var hasFront := cm.journalist.hasFront();
    var hasBack := cm.journalist.hasBack();
    if cm.superblock.journalLen > 0 && !cm.journalFrontRead.Some? && !hasFront {
      PageInJournalReqFront(k, cm, io);
    } else if cm.superblock.journalStart + cm.superblock.journalLen > NumJournalBlocks() && !cm.journalBackRead.Some? && !hasBack {
      PageInJournalReqBack(k, cm, io);
    } else if (cm.superblock.journalLen > 0 ==> hasFront)
        && (cm.superblock.journalStart + cm.superblock.journalLen > NumJournalBlocks() ==> hasBack) {
      FinishLoadingOtherPhase(k, cm);
    } else {
    }
  }
}
