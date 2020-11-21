include "IOImpl.i.dfy"
include "FullImpl.i.dfy"
include "CommitterInitImpl.i.dfy"
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
  import CommitterInitImpl
  import HandleReadResponseModel
  import IOImpl

  method readSuperblockResp(
      linear inout cm: Committer,
      io: DiskIOHandler,
      which: uint64)
  requires old_cm.W()
  requires io.diskOp().RespReadOp?
  ensures cm.W()
  ensures cm.I() == HandleReadResponseModel.readSuperblockResp(
      old_cm.I(), old(IIO(io)), which)
  {
    HandleReadResponseModel.reveal_readSuperblockResp();

    var id, sector := IOImpl.ReadSector(io);
    var res := (if sector.Some? && sector.value.SectorSuperblock?
        then JC.SuperblockSuccess(sector.value.superblock)
        else JC.SuperblockCorruption);
    if which == 0 {
      if Some(id) == cm.superblock1Read {
        inout cm.superblock1 := res;
        inout cm.superblock1Read := None;
      } else {
        print "readSuperblockResp did nothing\n";
      }
    } else {
      if Some(id) == cm.superblock2Read {
        inout cm.superblock2 := res;
        inout cm.superblock2Read := None;
      } else {
        print "readSuperblockResp did nothing\n";
      }
    }
  }

  // [yizhou7][FIXME]: this takes long to verify
  method readResponse(s: Full, io: DiskIOHandler)
  requires s.Inv()
  requires io.diskOp().RespReadOp?
  requires io !in s.Repr
  modifies s.Repr
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures |old(io.diskOp()).respRead.bytes| < 0x1_0000_0000_0000_0000
  ensures s.I() == HandleReadResponseModel.readResponse(
      old(s.I()), old(IIO(io)))
  {
    HandleReadResponseModel.reveal_readResponse();
    s.reveal_ReprInv();

    var id, addr, bytes := io.getReadResult();

    var loc := DiskLayout.Location(addr, |bytes| as uint64);
    linear var jc := s.jc.Take();

    if ValidNodeLocation(loc) {
      if s.bc.ready {
        IOImpl.PageInNodeResp(s.bc, io);
      } else {
        print "readResponse: doing nothing\n";
      }
    } else if ValidIndirectionTableLocation(loc) {
      if !s.bc.ready && s.bc.loading {
        IOImpl.PageInIndirectionTableResp(s.bc, io);
      } else {
        print "readResponse: doing nothing\n";
      }
    } else if ValidJournalLocation(loc) {
      if jc.status.StatusLoadingOther? {
        inout jc.PageInJournalResp(io);
      }
    } else if loc == Superblock1Location() {
      readSuperblockResp(inout jc, io, 0);
    } else if loc == Superblock2Location() {
      readSuperblockResp(inout jc, io, 1);
    } else {
      print "readResponse: doing nothing\n";
    }

    s.jc.Give(jc);
    s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
    s.reveal_ReprInv();
    assert s.ProtectedReprInv();
  }
}
