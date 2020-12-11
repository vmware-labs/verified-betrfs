include "IOModel.i.dfy"
include "CommitterInitModel.i.dfy"

module HandleReadResponseModel {
  import opened NativeTypes
  import opened StateModel
  import opened StateBCModel
  import opened StateSectorModel

  import opened DiskLayout
  import opened InterpretationDiskOps
  import opened ViewOp
  import opened Options
  import opened DiskOpModel
  import IOModel
  import CommitterModel
  import CommitterInitModel
  import MarshallingModel

  function {:opaque} readSuperblockResp(
      
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

  lemma jcNoOp_respread(s: Variables, s': Variables, vop: VOp, io: IO)
  requires CommitterModel.WF(s.jc)
  requires ValidDiskOp(diskOp(io))
  requires diskOp(io).RespReadOp?
  requires s.jc == s'.jc
  requires vop.StatesInternalOp? || vop.JournalInternalOp?
  ensures JC.Next(CommitterModel.I(s.jc), CommitterModel.I(s'.jc),
      IDiskOp(diskOp(io)).jdop, vop);
  {
    assert JC.NoOp(CommitterModel.I(s.jc), CommitterModel.I(s'.jc),
        IDiskOp(diskOp(io)).jdop, vop);
    assert JC.NextStep(CommitterModel.I(s.jc), CommitterModel.I(s'.jc),
        IDiskOp(diskOp(io)).jdop, vop, JC.NoOpStep);
  }

  lemma bcNoOp_respread(s: Variables, s': Variables, vop: VOp, io: IO)
  requires WFBCVars(s.bc)
  requires s.bc == s'.bc
  requires ValidDiskOp(diskOp(io))
  requires diskOp(io).RespReadOp?
  requires vop.StatesInternalOp? || vop.JournalInternalOp?
  ensures BBC.Next(IBlockCache(s.bc), IBlockCache(s'.bc),
    IDiskOp(diskOp(io)).bdop, vop);
  {
    reveal_Parse();
    MarshallingModel.reveal_parseCheckedSector();
    Marshalling.reveal_parseSector();
    MarshallingModel.reveal_parseSector();
    reveal_SectorOfBytes();
    reveal_ValidCheckedBytes();
    reveal_Parse();

    assert BC.NoOp(IBlockCache(s.bc), IBlockCache(s'.bc),
      IDiskOp(diskOp(io)).bdop, vop);
    assert BC.NextStep(IBlockCache(s.bc), IBlockCache(s'.bc),
      IDiskOp(diskOp(io)).bdop, vop, BC.NoOpStep);
    assert BBC.NextStep(IBlockCache(s.bc), IBlockCache(s'.bc),
      IDiskOp(diskOp(io)).bdop, vop, BBC.BlockCacheMoveStep(BC.NoOpStep));
  }

  lemma noop_respread(s: Variables, io: IO)
  requires WFVars(s)
  requires diskOp(io).RespReadOp?
  ensures M.Next(IVars(s), IVars(s), UI.NoOp, diskOp(io))
  {
    if ValidDiskOp(diskOp(io)) {
      jcNoOp_respread(s, s, StatesInternalOp, io);
      bcNoOp_respread(s, s, StatesInternalOp, io);
      assert BJC.NextStep(IVars(s), IVars(s), UI.NoOp, IDiskOp(diskOp(io)), StatesInternalOp);
    }
  }

  lemma readSuperblockRespCorrect(
      
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
  ensures var cm' := readSuperblockResp(cm, io, which);
    && CommitterModel.WF(cm')
    && JC.Next(
        CommitterModel.I(cm),
        CommitterModel.I(cm'),
        IDiskOp(diskOp(io)).jdop,
        JournalInternalOp)
  {
    var cm' := readSuperblockResp(cm, io, which);
    reveal_readSuperblockResp();
    IOModel.ReadSectorCorrect(io);
    var dop := IDiskOp(diskOp(io)).jdop;
    assert dop.RespReadSuperblockOp?;
    assert dop.which == which as int;

    if cm.status.StatusLoadingSuperblock?
        && (which == 0 ==> Some(dop.id) == cm.superblock1Read)
        && (which == 1 ==> Some(dop.id) == cm.superblock2Read)
    {
      assert JC.PageInSuperblockResp(
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          dop,
          JournalInternalOp, which as int);
      assert JC.NextStep(
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          dop,
          JournalInternalOp,
          JC.PageInSuperblockRespStep(which as int));
    } else {
      assert JC.NoOp(
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          dop,
          JournalInternalOp);
      assert JC.NextStep(
          CommitterModel.I(cm),
          CommitterModel.I(cm'),
          dop,
          JournalInternalOp,
          JC.NoOpStep);
    }
  }

  function {:opaque} readResponse(s: Variables, io: IO)
      : Variables
  requires Inv(s)
  requires diskOp(io).RespReadOp?
  requires |io.respRead.bytes| < 0x1_0000_0000_0000_0000
  {
    var loc := DiskLayout.Location(
        io.respRead.addr,
        |io.respRead.bytes| as uint64);

    if ValidNodeLocation(loc) then (
      if s.bc.Ready? then (
        var bc' := IOModel.PageInNodeResp(s.bc, io);
        s.(bc := bc')
      ) else (
        s
      )
    ) else if ValidIndirectionTableLocation(loc) then (
      if s.bc.LoadingIndirectionTable? then (
        var bc' := IOModel.PageInIndirectionTableResp(s.bc, io);
        s.(bc := bc')
      ) else (
        s
      )
    ) else if ValidJournalLocation(loc) then (
      if s.jc.status.StatusLoadingOther? then (
        var jc' := CommitterInitModel.PageInJournalResp(s.jc, io);
        s.(jc := jc')
      ) else (
        s
      )
    ) else if loc == Superblock1Location() then (
      var jc' := readSuperblockResp(s.jc, io, 0);
      s.(jc := jc')
    ) else if loc == Superblock2Location() then (
      var jc' := readSuperblockResp(s.jc, io, 1);
      s.(jc := jc')
    ) else (
      s
    )
  }

  lemma readResponseCorrect(s: Variables, io: IO)
  requires diskOp(io).RespReadOp?
  requires Inv(s)
  requires |io.respRead.bytes| < 0x1_0000_0000_0000_0000
  ensures var s' := readResponse(s, io);
    && WFVars(s')
    && M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io))
  {
    var loc := DiskLayout.Location(
        io.respRead.addr,
        |io.respRead.bytes| as uint64);

    reveal_readResponse();
    var s' := readResponse(s, io);

    if ValidNodeLocation(loc) {
      if s.bc.Ready? {
        IOModel.PageInNodeRespCorrect(s.bc, io);

        jcNoOp_respread(s, s', StatesInternalOp, io);
        assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)), StatesInternalOp);
        assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)));
        assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io));
      } else {
        noop_respread(s, io);
      }
    } else if ValidIndirectionTableLocation(loc) {
      if s.bc.LoadingIndirectionTable? {
        IOModel.PageInIndirectionTableRespCorrect(s.bc, io);

        jcNoOp_respread(s, s', StatesInternalOp, io);
        assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)), StatesInternalOp);
        assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)));
        assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io));
      } else {
        noop_respread(s, io);
      }
    } else if ValidJournalLocation(loc) {
      if s.jc.status.StatusLoadingOther? {
        CommitterInitModel.PageInJournalRespCorrect(s.jc, io);

        bcNoOp_respread(s, s', JournalInternalOp, io);
        assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)), JournalInternalOp);
        assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)));
        assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io));
      } else {
        noop_respread(s, io);
      }
    } else if loc == Superblock1Location() {
      readSuperblockRespCorrect(s.jc, io, 0);

      bcNoOp_respread(s, s', JournalInternalOp, io);
      assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)), JournalInternalOp);
      assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)));
      assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io));
    } else if loc == Superblock2Location() {
      readSuperblockRespCorrect(s.jc, io, 1);

      bcNoOp_respread(s, s', JournalInternalOp, io);
      assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)), JournalInternalOp);
      assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)));
      assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io));
    } else {
      noop_respread(s, io);
    }
  }
}
