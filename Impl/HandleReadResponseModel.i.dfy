// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "IOModel.i.dfy"
include "FullImpl.i.dfy"

module HandleReadResponseModel {
  import opened NativeTypes
  import opened StateSectorModel

  import opened DiskLayout
  import opened InterpretationDiskOps
  import opened ViewOp
  import opened Options
  import opened DiskOpModel
  import IOModel
  import MarshallingModel
  import M = ByteCache
  import opened FullImpl
  import BBC = BetreeCache

  lemma jcNoOp_respread(s: Full, s': Full, vop: VOp, io: IO)
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

  lemma bcNoOp_respread(s: Full, s': Full, vop: VOp, io: IO)
  requires s.bc.W()
  requires s.bc == s'.bc
  requires ValidDiskOp(diskOp(io))
  requires diskOp(io).RespReadOp?
  requires vop.StatesInternalOp? || vop.JournalInternalOp?
  ensures BBC.Next(s.bc.I(), s'.bc.I(),
    IDiskOp(diskOp(io)).bdop, vop);
  {
    reveal_Parse();
    MarshallingModel.reveal_parseCheckedSector();
    Marshalling.reveal_parseSector();
    MarshallingModel.reveal_parseSector();
    reveal_SectorOfBytes();
    reveal_ValidCheckedBytes();
    reveal_Parse();

    assert BC.NoOp(s.bc.I(), s'.bc.I(),
      IDiskOp(diskOp(io)).bdop, vop);
    assert BC.NextStep(s.bc.I(), s'.bc.I(),
      IDiskOp(diskOp(io)).bdop, vop, BC.NoOpStep);
    assert BBC.NextStep(s.bc.I(), s'.bc.I(),
      IDiskOp(diskOp(io)).bdop, vop, BBC.BlockCacheMoveStep(BC.NoOpStep));
  }

  lemma noop_respread(s: Full, io: IO)
  requires s.W()
  requires diskOp(io).RespReadOp?
  ensures M.Next(s.I(), s.I(), UI.NoOp, diskOp(io))
  {
    if ValidDiskOp(diskOp(io)) {
      jcNoOp_respread(s, s, StatesInternalOp, io);
      bcNoOp_respread(s, s, StatesInternalOp, io);
      assert BJC.NextStep(s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(io)), StatesInternalOp);
    }
  }
}
