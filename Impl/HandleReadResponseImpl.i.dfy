include "IOImpl.i.dfy"
include "FullImpl.i.dfy"
include "HandleReadResponseModel.i.dfy"

module HandleReadResponseImpl {
  import opened NativeTypes
  import opened StateModel
  import opened DiskLayout
  import opened InterpretationDiskOps
  import opened Options
  import opened FullImpl
  import opened DiskOpImpl
  import opened CommitterImpl
  import opened MainDiskIOHandler
  import HandleReadResponseModel
  import IOImpl

  method readResponse(linear inout s: Full, io: DiskIOHandler)
  requires old_s.Inv()
  requires io.diskOp().RespReadOp?
  ensures s.W()
  ensures |old(io.diskOp()).respRead.bytes| < 0x1_0000_0000_0000_0000
  ensures s.I() == HandleReadResponseModel.readResponse(
      old_s.I(), old(IIO(io)))
  {
    HandleReadResponseModel.reveal_readResponse();
    var id, addr, bytes := io.getReadResult();

    var loc := DiskLayout.Location(addr, |bytes| as uint64);

    if ValidNodeLocation(loc) {
      if s.bc.Ready? {
        IOImpl.PageInNodeResp(inout s.bc, io);
      } else {
        print "readResponse: doing nothing\n";
      }
    } else if ValidIndirectionTableLocation(loc) {
      if s.bc.Loading? {
        IOImpl.PageInIndirectionTableResp(inout s.bc, io);
      } else {
        print "readResponse: doing nothing\n";
      }
    } else if ValidJournalLocation(loc) {
      if s.jc.status.StatusLoadingOther? {
        inout s.jc.pageInJournalResp(io);
      }
    } else if loc == Superblock1Location() {
      inout s.jc.readSuperblockResp(io, 0);
    } else if loc == Superblock2Location() {
      inout s.jc.readSuperblockResp(io, 1);
    } else {
      print "readResponse: doing nothing\n";
    }
  }
}
