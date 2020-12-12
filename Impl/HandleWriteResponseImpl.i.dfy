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

  // [yizhou7][FIXME]: this takes long to verify
  method writeResponse(s: Full, io: DiskIOHandler)
  requires s.Inv()
  requires io.diskOp().RespWriteOp?
  requires io !in s.Repr
  modifies s.Repr
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures s.I() == HandleWriteResponseModel.writeResponse(
      old(s.I()), old(IIO(io)))
  {
    HandleWriteResponseModel.reveal_writeResponse();
    s.reveal_ReprInv();

    var id, addr, len := io.getWriteResult();

    var loc := DiskLayout.Location(addr, len);

    linear var jc := s.jc.Take();

    if ValidNodeLocation(loc) &&
        s.bc.ready && id in s.bc.outstandingBlockWrites {
      IOImpl.writeNodeResponse(s.bc, io);
    } else if ValidIndirectionTableLocation(loc)
        && s.bc.ready
        && s.bc.outstandingIndirectionTableWrite == Some(id) {
      var frozen_loc := IOImpl.writeIndirectionTableResponse(s.bc, io);
      inout jc.receiveFrozenLoc(frozen_loc);
    } else if jc.status.StatusReady? && ValidJournalLocation(loc) {
      writeBackJournalResp(inout jc, io);
    } else if ValidSuperblockLocation(loc) && Some(id) == jc.superblockWrite {
      if jc.status.StatusReady? && jc.commitStatus.CommitAdvanceLocation? {
        IOImpl.cleanUp(s.bc);
      }
      inout jc.writeBackSuperblockResp();
    } else {
      print "writeResponse: doing nothing\n";
    }

    s.jc.Give(jc);

    s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
    s.reveal_ReprInv();
    assert s.ProtectedReprInv();
  }
}
