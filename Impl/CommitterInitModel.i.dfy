include "CommitterModel.i.dfy"
include "StateModel.i.dfy"
include "IOModel.i.dfy"

module CommitterInitModel {
  import opened NativeTypes
  import opened Options

  import opened DiskLayout
  import opened InterpretationDiskOps
  import opened ViewOp
  import JournalCache

  import opened CommitterModel
  import opened StateModel
  import opened IOModel

  function {:opaque} PageInSuperblockReq(k: Constants, cm: CM, io: IO, which: uint64) : (res : (CM, IO))
  requires which == 0 || which == 1
  requires which == 0 ==> cm.superblock1.SuperblockUnfinished?
  requires which == 1 ==> cm.superblock2.SuperblockUnfinished?
  requires io.IOInit?
  requires cm.status.StatusLoadingSuperblock?
  {
    if which == 0 then (
      if cm.superblock1Read.None? then (
        var loc := Superblock1Location();
        var (id, io') := RequestRead(io, loc);
        var cm' := cm.(superblock1Read := Some(id));
        (cm', io')
      ) else (
        (cm, io)
      )
    ) else (
      if cm.superblock2Read.None? then (
        var loc := Superblock2Location();
        var (id, io') := RequestRead(io, loc);
        var cm' := cm.(superblock2Read := Some(id));
        (cm', io')
      ) else (
        (cm, io)
      )
    )
  }

  lemma PageInSuperblockReqCorrect(k: Constants,
      cm: CM, io: IO, which: uint64)
  requires CommitterModel.WF(cm)
  requires PageInSuperblockReq.requires(k, cm, io, which)
  ensures var (cm', io') := PageInSuperblockReq(k, cm, io, which);
    && CommitterModel.WF(cm')
    && ValidDiskOp(diskOp(io'))
    && JournalCache.Next(Ik(k).jc,
        CommitterModel.I(cm),
        CommitterModel.I(cm'),
        IDiskOp(diskOp(io')).jdop,
        JournalInternalOp)
  {
    reveal_PageInSuperblockReq();
    var (cm', io') := PageInSuperblockReq(k, cm, io, which);

    var loc;
    if which == 0 {
      loc := Superblock1Location();
    } else {
      loc := Superblock2Location();
    }
    RequestReadCorrect(io, loc);

    if (which == 0 && cm.superblock1Read.None?)
      || (which == 1 && cm.superblock2Read.None?)
    {
      assert JournalCache.PageInSuperblockReq(Ik(k).jc,
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          IDiskOp(diskOp(io')).jdop,
          JournalInternalOp, which as int);
      assert JournalCache.NextStep(Ik(k).jc,
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          IDiskOp(diskOp(io')).jdop,
          JournalInternalOp,
          JournalCache.PageInSuperblockReqStep(which as int));
    } else {
      assert JournalCache.NoOp(Ik(k).jc,
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          IDiskOp(diskOp(io')).jdop,
          JournalInternalOp);
      assert JournalCache.NextStep(Ik(k).jc,
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          IDiskOp(diskOp(io')).jdop,
          JournalInternalOp,
          JournalCache.NoOpStep);

    }
  }

  function {:opaque} PageInSuperblockResp(k: Constants, cm: CM, io: IO, which: uint64) : (cm' : CM)
  requires diskOp(io).RespReadOp?
  requires ValidDiskOp(diskOp(io))
  requires which == 0 || which == 1
  requires which == 0 ==> ValidSuperblock1Location(
      LocOfRespRead(diskOp(io).respRead))
  requires which == 1 ==> ValidSuperblock2Location(
      LocOfRespRead(diskOp(io).respRead))
  {
    if cm.status.StatusLoadingSuperblock? then (
      var (id, sector) := ReadSector(io);
      var sup := (
        if sector.Some? &&
            JournalCache.WFSuperblock(sector.value.superblock) then
          JournalCache.SuperblockSuccess(sector.value.superblock)
        else
          JournalCache.SuperblockCorruption
      );
      if which == 0 then (
        if cm.superblock1Read == Some(id) then 
          cm.(superblock1Read := None)
            .(superblock1 := sup)
        else
          cm
      ) else (
        if cm.superblock2Read == Some(id) then 
          cm.(superblock2Read := None)
            .(superblock2 := sup)
        else
          cm
      )
    ) else (
      cm
    )
  }

  lemma {:opaque} PageInSuperblockRespCorrect(k: Constants, cm: CM, io: IO, which: uint64)
  requires PageInSuperblockResp.requires(k, cm, io, which)
  requires CommitterModel.WF(cm)
  ensures var cm' := PageInSuperblockResp(k, cm, io, which);
    && CommitterModel.WF(cm')
    && ValidDiskOp(diskOp(io))
    && JournalCache.Next(Ik(k).jc,
        CommitterModel.I(cm),
        CommitterModel.I(cm'),
        IDiskOp(diskOp(io)).jdop,
        JournalInternalOp)
  {
    reveal_PageInSuperblockResp();
    var cm' := PageInSuperblockResp(k, cm, io, which);
    if cm.status.StatusLoadingSuperblock?
    {
      var (id, sector) := ReadSector(io);
      ReadSectorCorrect(io);
      var sup := (
        if sector.Some? &&
            JournalCache.WFSuperblock(sector.value.superblock) then
          JournalCache.SuperblockSuccess(sector.value.superblock)
        else
          JournalCache.SuperblockCorruption
      );

      var dop := IDiskOp(diskOp(io)).jdop;
      assert dop.superblock.Some? ==> sector.Some?;
      assert sector.Some? ==> dop.superblock.Some?;
      assert (dop.superblock.Some? && JournalCache.WFSuperblock(dop.superblock.value))
          == (sector.Some? &&
            JournalCache.WFSuperblock(sector.value.superblock));
      //assert sector.value.superblock == diskOp(io).superblock.value;

      if (
        || (which == 0 && cm.superblock1Read == Some(id))
        || (which == 1 && cm.superblock2Read == Some(id))
       )
      {
        if which == 0 {
          assert CommitterModel.I(cm').outstandingSuperblock1Read == None;
          assert CommitterModel.I(cm').superblock1 == sup;
          assert CommitterModel.I(cm') == CommitterModel.I(cm)
              .(outstandingSuperblock1Read := None)
              .(superblock1 := sup);
        } else {
          assert CommitterModel.I(cm').outstandingSuperblock2Read == None;
          assert CommitterModel.I(cm').superblock2 == sup;
          assert CommitterModel.I(cm') == CommitterModel.I(cm)
            .(outstandingSuperblock2Read := None)
            .(superblock2 := sup);
        }
        assert JournalCache.PageInSuperblockResp(Ik(k).jc,
            CommitterModel.I(cm),
            CommitterModel.I(cm'),
            IDiskOp(diskOp(io)).jdop,
            JournalInternalOp, which as int);
        assert JournalCache.NextStep(Ik(k).jc,
            CommitterModel.I(cm),
            CommitterModel.I(cm'),
            IDiskOp(diskOp(io)).jdop,
            JournalInternalOp,
            JournalCache.PageInSuperblockRespStep(which as int));
      } else {
        assert JournalCache.NoOp(Ik(k).jc,
            CommitterModel.I(cm),
            CommitterModel.I(cm'),
            IDiskOp(diskOp(io)).jdop,
            JournalInternalOp);
        assert JournalCache.NextStep(Ik(k).jc,
            CommitterModel.I(cm),
            CommitterModel.I(cm'),
            IDiskOp(diskOp(io)).jdop,
            JournalInternalOp,
            JournalCache.NoOpStep);
      }
    } else {
      assert JournalCache.NoOp(Ik(k).jc,
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          IDiskOp(diskOp(io)).jdop,
          JournalInternalOp);
      assert JournalCache.NextStep(Ik(k).jc,
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          IDiskOp(diskOp(io)).jdop,
          JournalInternalOp,
          JournalCache.NoOpStep);
    }
  }

  function {:opaque} FinishLoadingSuperblockPhase(k: Constants, cm: CM) : (cm' : CM)
  requires cm.status.StatusLoadingSuperblock?
  requires cm.superblock1.SuperblockSuccess?
  requires cm.superblock2.SuperblockSuccess?
  {
    var idx := if JournalCache.increments1(
        cm.superblock1.value.counter, cm.superblock2.value.counter)
        then 1 else 0;

    var sup := if idx == 1 then
      cm.superblock2.value
    else
      cm.superblock1.value;

    cm.(whichSuperblock := idx)
      .(superblock := sup)
      .(status := StatusLoadingOther)
      .(journalFrontRead := None)
      .(journalBackRead := None)
  }

  lemma FinishLoadingSuperblockPhaseCorrect(k: Constants, cm: CM)
  requires cm.status.StatusLoadingSuperblock?
  requires cm.superblock1.SuperblockSuccess?
  requires cm.superblock2.SuperblockSuccess?
  requires CommitterModel.WF(cm)
  ensures var cm' := FinishLoadingSuperblockPhase(k, cm);
    && CommitterModel.WF(cm')
    && JournalCache.Next(Ik(k).jc,
        CommitterModel.I(cm),
        CommitterModel.I(cm'),
        JournalDisk.NoDiskOp,
        SendPersistentLocOp(cm'.superblock.indirectionTableLoc))
  {
    var cm' := FinishLoadingSuperblockPhase(k, cm);
    var vop := SendPersistentLocOp(cm'.superblock.indirectionTableLoc);
    reveal_FinishLoadingSuperblockPhase();
    assert JournalCache.FinishLoadingSuperblockPhase(Ik(k).jc,
        CommitterModel.I(cm),
        CommitterModel.I(cm'),
        JournalDisk.NoDiskOp,
        vop);
    assert JournalCache.NextStep(Ik(k).jc,
        CommitterModel.I(cm),
        CommitterModel.I(cm'),
        JournalDisk.NoDiskOp,
        vop,
        JournalCache.FinishLoadingSuperblockPhaseStep);
  }

  function {:opaque} FinishLoadingOtherPhase(k: Constants, cm: CM) : (cm' : CM)
  requires cm.status.StatusLoadingOther?
  requires CommitterModel.WF(cm)
  {
    if cm.superblock.journalLen == 0 then
      cm.(status := StatusReady)
        .(frozenLoc := None)
        .(isFrozen := false)
        .(frozenJournalPosition := 0)
        .(superblockWrite := None)
        .(outstandingJournalWrites := {})
        .(newSuperblock := None)
        .(commitStatus := JournalCache.CommitNone)
        .(journalist := JournalistModel.setWrittenJournalLen(
            cm.journalist, cm.superblock.journalLen))
    else
      cm
  }

  lemma FinishLoadingOtherPhaseCorrect(k: Constants, cm: CM)
  requires cm.status.StatusLoadingOther?
  requires CommitterModel.WF(cm)
  ensures var cm' := FinishLoadingOtherPhase(k, cm)
  {
  }
}
