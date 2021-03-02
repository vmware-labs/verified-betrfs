// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "CommitterImpl.i.dfy"
include "HandleWriteResponseModel.i.dfy"
include "MainDiskIOHandler.s.dfy"
include "IOImpl.i.dfy"
include "FullImpl.i.dfy"

module HandleWriteResponseImpl {
  import opened NativeTypes
  import opened StateModel
  import opened DiskLayout
  import opened InterpretationDiskOps
  import opened ViewOp
  import opened Options
  import opened CommitterImpl
  import opened DiskOpImpl
  import opened MainDiskIOHandler
  import opened FullImpl
  import IOImpl
  import HandleWriteResponseModel
  import MarshallingModel

  method writeResponse(linear inout s: Full, io: DiskIOHandler)
  requires old_s.Inv()
  requires io.diskOp().RespWriteOp?
  ensures s.W()
  ensures s.I() == HandleWriteResponseModel.writeResponse(
      old_s.I(), old(IIO(io)))
  {
    HandleWriteResponseModel.reveal_writeResponse();

    var id, addr, len := io.getWriteResult();

    var loc := DiskLayout.Location(addr, len);

    if ValidNodeLocation(loc) &&
        s.bc.Ready? && id in s.bc.outstandingBlockWrites {
      IOImpl.writeNodeResponse(inout s.bc, io);
    } else if ValidIndirectionTableLocation(loc)
        && s.bc.Ready?
        && s.bc.outstandingIndirectionTableWrite == Some(id) {
      var frozen_loc := IOImpl.writeIndirectionTableResponse(inout s.bc, io);
      inout s.jc.receiveFrozenLoc(frozen_loc);
    } else if s.jc.status.StatusReady? && ValidJournalLocation(loc) {
      inout s.jc.writeBackJournalResp(io);
    } else if ValidSuperblockLocation(loc) && Some(id) == s.jc.superblockWrite {
      if s.jc.status.StatusReady? && s.jc.commitStatus.CommitAdvanceLocation? {
        IOImpl.cleanUp(inout s.bc);
      }
      inout s.jc.writeBackSuperblockResp(IIO(io));
    } else {
      print "writeResponse: doing nothing\n";
    }
  }
}
