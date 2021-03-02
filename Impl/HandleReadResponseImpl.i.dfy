include "IOImpl.i.dfy"
include "FullImpl.i.dfy"
include "HandleReadResponseModel.i.dfy"

module HandleReadResponseImpl {
  import opened NativeTypes
  import opened DiskLayout
  import opened InterpretationDiskOps
  import opened Options
  import opened FullImpl
  import opened DiskOpImpl
  import opened CommitterImpl
  import opened MainDiskIOHandler
  import opened HandleReadResponseModel
  import IOImpl

  import opened ViewOp
  import opened DiskOpModel
  import M = ByteCache

  method readResponse(linear inout s: Full, io: DiskIOHandler)
  requires old_s.Inv()
  requires io.diskOp().RespReadOp?
  ensures s.WF()
  ensures |old(io.diskOp()).respRead.bytes| < 0x1_0000_0000_0000_0000
  ensures M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)))
  {
    var id, addr, bytes := io.getReadResult();

    var loc := DiskLayout.Location(addr, |bytes| as uint64);

    if ValidNodeLocation(loc) {
      if s.bc.Ready? {
        IOImpl.PageInNodeResp(inout s.bc, io);

        jcNoOp_respread(old_s, s, StatesInternalOp, IIO(io));
        assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), StatesInternalOp);
        assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
        assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
      } else {
        noop_respread(s, IIO(io));
        print "readResponse: doing nothing\n";
      }
    } else if ValidIndirectionTableLocation(loc) {
      if s.bc.Loading? {
        IOImpl.PageInIndirectionTableResp(inout s.bc, io);

        jcNoOp_respread(old_s, s, StatesInternalOp, IIO(io));
        assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), StatesInternalOp);
        assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
        assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
      } else {
        print "readResponse: doing nothing\n";
        noop_respread(s, IIO(io));
      }
    } else if ValidJournalLocation(loc) {
      if s.jc.status.StatusLoadingOther? {
        inout s.jc.pageInJournalResp(io);

        bcNoOp_respread(old_s, s, JournalInternalOp, IIO(io));
        assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), JournalInternalOp);
        assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
        assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
      } else {
        noop_respread(s, IIO(io));
      }
    } else if loc == Superblock1Location() {
      inout s.jc.readSuperblockResp(io, 0);

      bcNoOp_respread(old_s, s, JournalInternalOp, IIO(io));
      assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), JournalInternalOp);
      assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
      assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
    } else if loc == Superblock2Location() {
      inout s.jc.readSuperblockResp(io, 1);
    
      bcNoOp_respread(old_s, s, JournalInternalOp, IIO(io));
      assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), JournalInternalOp);
      assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
      assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
    } else {
      print "readResponse: doing nothing\n";
      noop_respread(s, IIO(io));
    }
  }
}
