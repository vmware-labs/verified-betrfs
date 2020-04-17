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

  method PageInSuperblockResp(
    k: ImplConstants, cm: Committer, io: DiskIOHandler, which: uint64)
  requires cm.Inv()
  requires io.diskOp().RespReadOp?
  requires ValidDiskOp(io.diskOp())
  requires which == 0 || which == 1
  requires which == 0 ==> ValidSuperblock1Location(
      LocOfRespRead(io.diskOp().respRead))
  requires which == 1 ==> ValidSuperblock2Location(
      LocOfRespRead(io.diskOp().respRead))

  requires io !in cm.Repr
  modifies cm.Repr
  ensures cm.W()
  ensures forall o | o in cm.Repr :: o in old(cm.Repr) || fresh(o)
  ensures cm.I() ==
      CommitterInitModel.PageInSuperblockResp(
          Ic(k), old(cm.I()), old(IIO(io)), which)
  {
    CommitterInitModel.reveal_PageInSuperblockResp();
    cm.reveal_ReprInv();

    if cm.status.StatusLoadingSuperblock? {
      var id, sector := ReadSector(io);
      var sup := (
        if sector.Some? &&
            JC.WFSuperblock(sector.value.superblock) then (
          JC.SuperblockSuccess(sector.value.superblock)
        ) else (
          JC.SuperblockCorruption
        )
      );
      if which == 0 {
        if cm.superblock1Read == Some(id) {
          cm.superblock1Read := None;
          cm.superblock1 := sup;
        } else {
          print "PageInSuperblockResp: did nothing\n";
        }
      } else {
        if cm.superblock2Read == Some(id) {
          cm.superblock2Read := None;
          cm.superblock2 := sup;
        } else {
          print "PageInSuperblockResp: did nothing\n";
        }
      }
    } else {
      print "PageInSuperblockResp: did nothing\n";
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

    if cm.superblock.journalLen == 0 {
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
    CommitterInitModel.reveal_isReplayEmpty();
    b := cm.journalist.isReplayEmpty();
  }
}
