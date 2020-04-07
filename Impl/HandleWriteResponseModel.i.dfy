include "IOModel.i.dfy"
include "DiskOpImpl.i.dfy"
include "CommitterCommitModel.i.dfy"

module HandleWriteResponseModel {
  import opened NativeTypes
  import opened StateModel
  import opened DiskLayout
  import opened InterpretationDiskOps
  import opened ViewOp
  import opened Options
  import opened DiskOpModel
  import IOModel
  import CommitterCommitModel
  import CommitterModel
  import MarshallingModel

  function {:opaque} writeBackJournalResp(
      k: Constants, cm: CommitterModel.CM, io: IO) : CommitterModel.CM
  {
    cm.(outstandingJournalWrites :=
        cm.outstandingJournalWrites - {io.id})
  }

  lemma writeBackJournalRespCorrect(k: Constants, cm: CommitterModel.CM, io: IO)
  requires CommitterModel.Inv(cm)
  requires diskOp(io).RespWriteOp?
  //requires ValidDiskOp(diskOp(io))
  requires ValidJournalLocation(LocOfRespWrite(diskOp(io).respWrite))
  requires cm.status.StatusReady?
  ensures var cm' := writeBackJournalResp(k, cm, io);
    && CommitterModel.WF(cm')
    && JC.Next(Ik(k).jc, CommitterModel.I(cm), CommitterModel.I(cm'), 
        IDiskOp(diskOp(io)).jdop, JournalInternalOp)
  {
    reveal_writeBackJournalResp();
    var cm' := writeBackJournalResp(k, cm, io);
    if diskOp(io).id in cm.outstandingJournalWrites {
      assert JC.WriteBackJournalResp(Ik(k).jc,
            CommitterModel.I(cm),
            CommitterModel.I(cm'),
            IDiskOp(diskOp(io)).jdop,
            JournalInternalOp);
      assert JC.NextStep(Ik(k).jc,
            CommitterModel.I(cm),
            CommitterModel.I(cm'),
            IDiskOp(diskOp(io)).jdop,
            JournalInternalOp,
            JC.WriteBackJournalRespStep);
    } else {
      assert JC.NoOp(Ik(k).jc,
            CommitterModel.I(cm),
            CommitterModel.I(cm'),
            IDiskOp(diskOp(io)).jdop,
            JournalInternalOp);
      assert JC.NextStep(Ik(k).jc,
            CommitterModel.I(cm),
            CommitterModel.I(cm'),
            IDiskOp(diskOp(io)).jdop,
            JournalInternalOp,
            JC.NoOpStep);

      assert cm == cm';
    }
  }

  function {:opaque} writeResponse(k: Constants, s: Variables, io: IO)
      : Variables
  requires Inv(k, s)
  requires diskOp(io).RespWriteOp?
  {
    var loc := DiskLayout.Location(
        io.respWrite.addr,
        io.respWrite.len);

    if ValidNodeLocation(loc) &&
        s.bc.Ready? && io.id in s.bc.outstandingBlockWrites then (
      var bc' := IOModel.writeNodeResponse(k, s.bc, io);
      s.(bc := bc')
    ) else if ValidIndirectionTableLocation(loc)
        && s.bc.Ready?
        && s.bc.outstandingIndirectionTableWrite == Some(io.id) then (
      var (bc', frozen_loc) := IOModel.writeIndirectionTableResponse(k, s.bc, io);
      var jc' := CommitterCommitModel.receiveFrozenLoc(k, s.jc, frozen_loc);
      s.(bc := bc')
       .(jc := jc')
    ) else if s.jc.status.StatusReady? && ValidJournalLocation(loc) then (
      var jc' := writeBackJournalResp(k, s.jc, io);
      s.(jc := jc')
    ) else if ValidSuperblockLocation(loc) && Some(io.id) == s.jc.superblockWrite then (
      var bc' := if s.jc.status.StatusReady? && s.jc.commitStatus.CommitAdvanceLocation? then (
        IOModel.cleanUp(k, s.bc)
      ) else (
        s.bc
      );
      var jc' := CommitterCommitModel.writeBackSuperblockResp(k, s.jc);
      s.(jc := jc')
       .(bc := bc')
    ) else (
      s
    )
  }

  lemma writeResponseCorrect(k: Constants, s: Variables, io: IO)
  requires Inv(k, s)
  requires diskOp(io).RespWriteOp?
  //requires ValidDiskOp(diskOp(io))

  ensures var s' := writeResponse(k, s, io);
    && WFVars(s')
    && M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io))
  {
    var loc := DiskLayout.Location(
        io.respWrite.addr,
        io.respWrite.len);
    var s' := writeResponse(k, s, io);
    reveal_writeResponse();

    if ValidNodeLocation(loc) &&
        s.bc.Ready? && io.id in s.bc.outstandingBlockWrites {
      IOModel.writeNodeResponseCorrect(k, s.bc, io);
      assert JC.NextStep(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), IDiskOp(diskOp(io)).jdop, StatesInternalOp, JC.NoOpStep);
      assert JC.Next(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), IDiskOp(diskOp(io)).jdop, StatesInternalOp);
      assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)), StatesInternalOp);
      assert BJC.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)));
      assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io));
    } else if ValidIndirectionTableLocation(loc)
        && s.bc.Ready?
        && s.bc.outstandingIndirectionTableWrite == Some(io.id) {
      IOModel.writeIndirectionTableResponseCorrect(k, s.bc, io);
      var (bc', frozen_loc) := IOModel.writeIndirectionTableResponse(k, s.bc, io);
      CommitterCommitModel.receiveFrozenLocCorrect(k, s.jc, frozen_loc);
      assert s'.jc == CommitterCommitModel.receiveFrozenLoc(k, s.jc, frozen_loc);

      assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)), SendFrozenLocOp(frozen_loc));
      assert BJC.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)));
      assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io));
    } else if s.jc.status.StatusReady? && ValidJournalLocation(loc) {
      writeBackJournalRespCorrect(k, s.jc, io);

      assert BC.NextStep(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io)).bdop, JournalInternalOp, BC.NoOpStep);
      assert BBC.NextStep(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io)).bdop, JournalInternalOp, BBC.BlockCacheMoveStep(BC.NoOpStep));
      assert BBC.Next(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io)).bdop, JournalInternalOp);
      assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)), JournalInternalOp);
      assert BJC.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)));
      assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io));
    } else if ValidSuperblockLocation(loc) && Some(io.id) == s.jc.superblockWrite {
      CommitterCommitModel.writeBackSuperblockRespCorrect(k, s.jc, io);
      if s.jc.status.StatusReady? && s.jc.commitStatus.CommitAdvanceLocation? {
        IOModel.cleanUpCorrect(k, s.bc);
        assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)), CleanUpOp);
        assert BJC.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)));
      } else {
        assert BC.NextStep(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io)).bdop, JournalInternalOp, BC.NoOpStep);
        assert BBC.NextStep(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io)).bdop, JournalInternalOp, BBC.BlockCacheMoveStep(BC.NoOpStep));
        assert BBC.Next(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io)).bdop, JournalInternalOp);

        assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)), JournalInternalOp);
        assert BJC.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)));
      }
      assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io));
    } else {
      if ValidDiskOp(diskOp(io)) {
        assert JC.NextStep(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), IDiskOp(diskOp(io)).jdop, JournalInternalOp, JC.NoOpStep);
        assert JC.Next(Ik(k).jc, CommitterModel.I(s.jc), CommitterModel.I(s'.jc), IDiskOp(diskOp(io)).jdop, JournalInternalOp);
        assert BC.NextStep(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io)).bdop, JournalInternalOp, BC.NoOpStep);
        assert BBC.NextStep(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io)).bdop, JournalInternalOp, BBC.BlockCacheMoveStep(BC.NoOpStep));
        assert BBC.Next(Ik(k).bc, IBlockCache(s.bc), IBlockCache(s'.bc), IDiskOp(diskOp(io)).bdop, JournalInternalOp);

        assert BJC.NextStep(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)), JournalInternalOp);
        assert BJC.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, IDiskOp(diskOp(io)));
      }

      assert M.Next(Ik(k), IVars(s), IVars(s'), UI.NoOp, diskOp(io));
    }
  }

}
