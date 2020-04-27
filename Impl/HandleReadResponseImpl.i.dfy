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
      k: ImplConstants,
      cm: Committer,
      io: DiskIOHandler,
      which: uint64)
  requires cm.W()
  requires io.diskOp().RespReadOp?
  requires io !in cm.Repr
  modifies cm.Repr
  ensures cm.W()
  ensures cm.Repr == old(cm.Repr)
  ensures cm.I() == HandleReadResponseModel.readSuperblockResp(
      Ic(k), old(cm.I()), old(IIO(io)), which)
  {
    cm.reveal_ReprInv();
    HandleReadResponseModel.reveal_readSuperblockResp();

    var id, sector := IOImpl.ReadSector(io);
    var res := (if sector.Some? && sector.value.SectorSuperblock?
        then JC.SuperblockSuccess(sector.value.superblock)
        else JC.SuperblockCorruption);
    if which == 0 {
      if Some(id) == cm.superblock1Read {
        cm.superblock1 := res;
        cm.superblock1Read := None;
      } else {
        print "readSuperblockResp did nothing\n";
      }
    } else {
      if Some(id) == cm.superblock2Read {
        cm.superblock2 := res;
        cm.superblock2Read := None;
      } else {
        print "readSuperblockResp did nothing\n";
      }
    }

    cm.reveal_ReprInv();
  }

  method readResponse(k: ImplConstants, s: Full, io: DiskIOHandler)
  requires s.Inv(k)
  requires io.diskOp().RespReadOp?
  requires io !in s.Repr
  modifies s.Repr
  ensures s.W()
  ensures forall o | o in s.Repr :: o in old(s.Repr) || fresh(o)
  ensures |old(io.diskOp()).respRead.bytes| < 0x1_0000_0000_0000_0000
  ensures s.I() == HandleReadResponseModel.readResponse(
      Ic(k), old(s.I()), old(IIO(io)))
  {
    HandleReadResponseModel.reveal_readResponse();
    s.reveal_ReprInv();

    var id, addr, bytes := io.getReadResult();

    var loc := DiskLayout.Location(addr, |bytes| as uint64);

    if ValidNodeLocation(loc) {
      if s.bc.ready {
        IOImpl.PageInNodeResp(k, s.bc, io);
      } else {
        print "readResponse: doing nothing\n";
      }
    } else if ValidIndirectionTableLocation(loc) {
      if !s.bc.ready && s.bc.loading {
        IOImpl.PageInIndirectionTableResp(k, s.bc, io);
      } else {
        print "readResponse: doing nothing\n";
      }
    } else if ValidJournalLocation(loc) {
      if s.jc.status.StatusLoadingOther? {
        CommitterInitImpl.PageInJournalResp(k, s.jc, io);
      }
    } else if loc == Superblock1Location() {
      readSuperblockResp(k, s.jc, io, 0);
    } else if loc == Superblock2Location() {
      readSuperblockResp(k, s.jc, io, 1);
    } else {
      print "readResponse: doing nothing\n";
    }

    s.Repr := {s} + s.bc.Repr() + s.jc.Repr;
    s.reveal_ReprInv();
    assert s.ProtectedReprInv();
  }
}
