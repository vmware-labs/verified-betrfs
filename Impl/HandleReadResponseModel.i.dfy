// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

include "IOModel.i.dfy"
include "StateModel.i.dfy"

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
  // import CommitterInitModel
  import MarshallingModel
  import M = ByteCache

  lemma jcNoOp_respread(s: Variables, s': Variables, vop: VOp, io: IO)
  requires s.jc.WF()
  requires ValidDiskOp(diskOp(io))
  requires diskOp(io).RespReadOp?
  requires s.jc == s'.jc
  requires vop.StatesInternalOp? || vop.JournalInternalOp?
  ensures JC.Next(s.jc.I(), s'.jc.I(),
      IDiskOp(diskOp(io)).jdop, vop);
  {
    assert JC.NoOp(s.jc.I(), s'.jc.I(),
        IDiskOp(diskOp(io)).jdop, vop);
    assert JC.NextStep(s.jc.I(), s'.jc.I(),
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
        var jc' := s.jc.PageInJournalResp(io);
        s.(jc := jc')
      ) else (
        s
      )
    ) else if loc == Superblock1Location() then (
      var jc' := s.jc.ReadSuperblockResp(io, 0);
      s.(jc := jc')
    ) else if loc == Superblock2Location() then (
      var jc' := s.jc.ReadSuperblockResp(io, 1);
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
        bcNoOp_respread(s, s', JournalInternalOp, io);
        assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)), JournalInternalOp);
        assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)));
        assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io));
      } else {
        noop_respread(s, io);
      }
    } else if loc == Superblock1Location() {
      bcNoOp_respread(s, s', JournalInternalOp, io);
      assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)), JournalInternalOp);
      assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)));
      assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io));
    } else if loc == Superblock2Location() {
      bcNoOp_respread(s, s', JournalInternalOp, io);
      assert BJC.NextStep(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)), JournalInternalOp);
      assert BJC.Next(IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)));
      assert M.Next(IVars(s), IVars(s'), UI.NoOp, diskOp(io));
    } else {
      noop_respread(s, io);
    }
  }
}
