// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "CommitterImpl.i.dfy"
// include "HandleWriteResponseModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "IOImpl.i.dfy"
include "FullImpl.i.dfy"

module HandleWriteResponseImpl {
  import opened NativeTypes
  import opened DiskLayout
  import opened InterpretationDiskOps
  import opened ViewOp
  import opened Options
  import opened CommitterImpl
  import opened DiskOpImpl
  import opened MainDiskIOHandler
  import opened FullImpl
  import IOImpl
  // import HandleWriteResponseModel
  import MarshallingModel
  import opened DiskOpModel
  import M = ByteCache
  import BBC = BetreeCache

  method writeResponse(linear inout s: Full, io: DiskIOHandler)
  requires old_s.Inv()
  requires io.diskOp().RespWriteOp?
  ensures s.WF()
  ensures M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)))
  {
    var id, addr, len := io.getWriteResult();

    var loc := DiskLayout.Location(addr, len);

    if ValidNodeLocation(loc) &&
        s.bc.Ready? && id in s.bc.outstandingBlockWrites {
      IOImpl.writeNodeResponse(inout s.bc, io);

      assert JC.NextStep(old_s.jc.I(), s.jc.I(), IDiskOp(diskOp(IIO(io))).jdop, StatesInternalOp, JC.NoOpStep);
      assert JC.Next(old_s.jc.I(), s.jc.I(), IDiskOp(diskOp(IIO(io))).jdop, StatesInternalOp);
      assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), StatesInternalOp);
      assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
      assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
    } else if ValidIndirectionTableLocation(loc)
        && s.bc.Ready?
        && s.bc.outstandingIndirectionTableWrite == Some(id) {
      var frozen_loc := IOImpl.writeIndirectionTableResponse(inout s.bc, io);
      inout s.jc.receiveFrozenLoc(frozen_loc);

      assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), SendFrozenLocOp(frozen_loc));
      assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
      assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
    } else if s.jc.status.StatusReady? && ValidJournalLocation(loc) {
      inout s.jc.writeBackJournalResp(io);
      
      assert BC.NextStep(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp, BC.NoOpStep);
      assert BBC.NextStep(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp, BBC.BlockCacheMoveStep(BC.NoOpStep));
      assert BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp);
      assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), JournalInternalOp);
      assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
      assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
    } else if ValidSuperblockLocation(loc) && Some(id) == s.jc.superblockWrite {
      ghost var cleanUp := false;
      if s.jc.status.StatusReady? && s.jc.commitStatus.CommitAdvanceLocation? {
        cleanUp := true;
        IOImpl.cleanUp(inout s.bc);
      }
      inout s.jc.writeBackSuperblockResp(IIO(io));

      if cleanUp {
        assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), CleanUpOp);
        assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
      } else {
        assert BC.NextStep(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp, BC.NoOpStep);
        assert BBC.NextStep(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp, BBC.BlockCacheMoveStep(BC.NoOpStep));
        assert BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp);

        assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), JournalInternalOp);
        assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
      }
      assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
    } else {
      print "writeResponse: doing nothing\n";
      if ValidDiskOp(diskOp(IIO(io))) {
        assert JC.NextStep(old_s.jc.I(), s.jc.I(), IDiskOp(diskOp(IIO(io))).jdop, JournalInternalOp, JC.NoOpStep);
        assert JC.Next(old_s.jc.I(), s.jc.I(), IDiskOp(diskOp(IIO(io))).jdop, JournalInternalOp);
        assert BC.NextStep(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp, BC.NoOpStep);
        assert BBC.NextStep(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp, BBC.BlockCacheMoveStep(BC.NoOpStep));
        assert BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp);

        assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), JournalInternalOp);
        assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
      }

      assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
    }
  }
}
