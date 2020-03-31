include "IOModel.i.dfy"

module HandleReadResponseModel {
  import opened NativeTypes
  import opened StateModel
  import opened DiskLayout
  import opened InterpretationDiskOps
  import opened ViewOp
  import opened Options
  import IOModel
  import CommitterModel

  function {:opaque} readSuperblockResp(
      k: Constants,
      cm: CommitterModel.CM,
      io: IO,
      which: uint64) : CommitterModel.CM
  requires diskOp(io).RespReadOp?
  {
    var (id, sector) := IOModel.ReadSector(io);
    var res := (if sector.Some? && sector.value.SectorSuperblock?
        then JC.SuperblockSuccess(sector.value.superblock)
        else JC.SuperblockCorruption);
    if which == 0 then (
      if Some(id) == cm.superblock1Read then
        cm.(superblock1 := res)
          .(superblock1Read := None)
      else
        cm
    ) else (
      if Some(id) == cm.superblock2Read then
        cm.(superblock2 := res)
          .(superblock2Read := None)
      else
        cm
    )
  }

  lemma readSuperblockRespCorrect(
      k: Constants,
      cm: CommitterModel.CM,
      io: IO,
      which: uint64)
  requires CommitterModel.WF(cm)
  requires ValidDiskOp(diskOp(io))
  requires diskOp(io).RespReadOp?
  requires which == 0 || which == 1
  requires which == 0 ==>
      LocOfRespRead(diskOp(io).respRead) == Superblock1Location()
  requires which == 1 ==>
      LocOfRespRead(diskOp(io).respRead) == Superblock2Location()
  ensures var cm' := readSuperblockResp(k, cm, io, which);
    && CommitterModel.WF(cm')
    && JC.Next(Ik(k).jc,
        CommitterModel.I(cm),
        CommitterModel.I(cm'),
        IDiskOp(diskOp(io)).jdop,
        JournalInternalOp)
  {
    var cm' := readSuperblockResp(k, cm, io, which);
    reveal_readSuperblockResp();
    IOModel.ReadSectorCorrect(io);
    var dop := IDiskOp(diskOp(io)).jdop;
    assert dop.RespReadSuperblockOp?;
    assert dop.which == which as int;

    if cm.status.StatusLoadingSuperblock?
        && (which == 0 ==> Some(dop.id) == cm.superblock1Read)
        && (which == 1 ==> Some(dop.id) == cm.superblock2Read)
    {
      assert JC.PageInSuperblockResp(Ik(k).jc,
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          dop,
          JournalInternalOp, which as int);
      assert JC.NextStep(Ik(k).jc,
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          dop,
          JournalInternalOp,
          JC.PageInSuperblockRespStep(which as int));
    } else {
      assert JC.NoOp(Ik(k).jc,
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          dop,
          JournalInternalOp);
      assert JC.NextStep(Ik(k).jc,
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          dop,
          JournalInternalOp,
          JC.NoOpStep);
    }
  }

  function readResponse(k: Constants, s: Variables, io: IO)
      : Variables
  requires Inv(k, s)
  requires diskOp(io).RespReadOp?
  requires |io.respRead.bytes| < 0x1_0000_0000_0000_0000
  {
    var loc := DiskLayout.Location(
        io.respRead.addr,
        |io.respRead.bytes| as uint64);

    if ValidNodeLocation(loc) then (
      if s.bc.Ready? then (
        var bc' := IOModel.PageInNodeResp(k, s.bc, io);
        s.(bc := bc')
      ) else (
        s
      )
    ) else if ValidIndirectionTableLocation(loc) then (
      if s.bc.LoadingIndirectionTable? then (
        var bc' := IOModel.PageInIndirectionTableResp(k, s.bc, io);
        s.(bc := bc')
      ) else (
        s
      )
    ) else (
      s
    )
  }
}
