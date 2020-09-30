include "CommitterImpl.i.dfy"
include "CommitterCommitImpl.i.dfy"
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
  import CommitterCommitImpl
  import HandleWriteResponseModel
  import MarshallingModel

  method writeBackJournalResp(
      cm: Committer, io: DiskIOHandler)
  requires cm.W()
  requires io.diskOp().RespWriteOp?
  requires io !in cm.Repr
  modifies cm.Repr
  ensures cm.W()
  ensures cm.Repr == old(cm.Repr)
  ensures cm.I() == HandleWriteResponseModel.writeBackJournalResp(
      old(cm.I()), old(IIO(io)))
  {
    cm.reveal_ReprInv();
    HandleWriteResponseModel.reveal_writeBackJournalResp();

    var id, addr, len := io.getWriteResult();
    cm.outstandingJournalWrites :=
        cm.outstandingJournalWrites - {id};

    cm.reveal_ReprInv();
  }

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

    if ValidNodeLocation(loc) &&
        s.bc.ready && id in s.bc.outstandingBlockWrites {
      IOImpl.writeNodeResponse(s.bc, io);
    } else if ValidIndirectionTableLocation(loc)
        && s.bc.ready
        && s.bc.outstandingIndirectionTableWrite == Some(id) {
      var frozen_loc := IOImpl.writeIndirectionTableResponse(s.bc, io);
      CommitterCommitImpl.receiveFrozenLoc(s.jc, frozen_loc);
    } else if s.jc.status.StatusReady? && ValidJournalLocation(loc) {
      writeBackJournalResp(s.jc, io);
    } else if ValidSuperblockLocation(loc) && Some(id) == s.jc.superblockWrite {
      if s.jc.status.StatusReady? && s.jc.commitStatus.CommitAdvanceLocation? {
        IOImpl.cleanUp(s.bc);
      }
      CommitterCommitImpl.writeBackSuperblockResp(s.jc);
    } else {
      print "writeResponse: doing nothing\n";
    }

    s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
    s.reveal_ReprInv();
    assert s.ProtectedReprInv();
  }
}
