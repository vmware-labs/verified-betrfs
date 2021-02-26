// include "IOModel.i.dfy"
// include "DiskOpImpl.i.dfy"
// include "StateModel.i.dfy"

// module HandleWriteResponseModel {
//   import opened NativeTypes
//   import opened StateModel
//   import opened StateSectorModel
//   import opened StateBCModel
//   import opened DiskLayout
//   import opened InterpretationDiskOps
//   import opened ViewOp
//   import opened Options
//   import opened DiskOpModel
//   import IOModel
//   import MarshallingModel
//   import M = ByteCache
//   import opened CommitterImpl

//   function {:opaque} writeResponse(s: Variables, io: IO)
//       : Variables
//   requires Inv(s)
//   requires diskOp(IIO(io)).RespWriteOp?
//   {
//     var loc := DiskLayout.Location(
//         io.respWrite.addr,
//         io.respWrite.len);

//     if ValidNodeLocation(loc) &&
//         old_s.bc.Ready? && io.id in old_s.bc.outstandingBlockWrites then (
//       var bc' := IOModel.writeNodeResponse(old_s.bc, io);
//       old_s.(bc := bc')
//     ) else if ValidIndirectionTableLocation(loc)
//         && old_s.bc.Ready?
//         && old_s.bc.outstandingIndirectionTableWrite == Some(io.id) then (
//       var (bc', frozen_loc) := IOModel.writeIndirectionTableResponse(old_s.bc, io);
//       var jc' := old_s.jc.ReceiveFrozenLoc(frozen_loc);
//       old_s.(bc := bc')
//        .(jc := jc')
//     ) else if old_s.jc.statuold_s.StatusReady? && ValidJournalLocation(loc) then (
//       var jc' := old_s.jc.WriteBackJournalResp(IIO(io));
//       old_s.(jc := jc')
//     ) else if ValidSuperblockLocation(loc) && Some(io.id) == old_s.jc.superblockWrite then (
//       var bc' := if old_s.jc.statuold_s.StatusReady? && old_s.jc.commitStatuold_s.CommitAdvanceLocation? then (
//         IOModel.cleanUp(old_s.bc)
//       ) else (
//         old_s.bc
//       );
//       var jc' := old_s.jc.WriteBackSuperblockResp(IIO(io));
//       old_s.(jc := jc')
//        .(bc := bc')
//     ) else (
//       s
//     )
//   }

//   lemma writeResponseCorrect(s: Variables, io: IO)
//   requires Inv(s)
//   requires diskOp(IIO(io)).RespWriteOp?
//   ensures var s' := writeResponse(s, io);
//     && WFVars(s')
//     && M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)))
//   {
//     var loc := DiskLayout.Location(
//         io.respWrite.addr,
//         io.respWrite.len);
//     var s' := writeResponse(s, io);
//     reveal_writeResponse();

//     if ValidNodeLocation(loc) &&
//         old_s.bc.Ready? && io.id in old_s.bc.outstandingBlockWrites {
//       IOModel.writeNodeResponseCorrect(old_s.bc, io);
//       assert JC.NextStep(old_s.jc.I(), s.jc.I(), IDiskOp(diskOp(IIO(io))).jdop, StatesInternalOp, JC.NoOpStep);
//       assert JC.Next(old_s.jc.I(), s.jc.I(), IDiskOp(diskOp(IIO(io))).jdop, StatesInternalOp);
//       assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), StatesInternalOp);
//       assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
//       assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
//     } else if ValidIndirectionTableLocation(loc)
//         && old_s.bc.Ready?
//         && old_s.bc.outstandingIndirectionTableWrite == Some(io.id) {
//       IOModel.writeIndirectionTableResponseCorrect(old_s.bc, io);
//       var (bc', frozen_loc) := IOModel.writeIndirectionTableResponse(old_s.bc, io);
//       // CommitterCommitModel.receiveFrozenLocCorrect(old_s.jc, frozen_loc);
//       assert s.jc == old_s.jc.ReceiveFrozenLoc(frozen_loc);

//       assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), SendFrozenLocOp(frozen_loc));
//       assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
//       assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
//     } else if old_s.jc.statuold_s.StatusReady? && ValidJournalLocation(loc) {
//       assert s.jc == old_s.jc.WriteBackJournalResp(IIO(io));

//       assert BC.NextStep(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp, BC.NoOpStep);
//       assert BBC.NextStep(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp, BBC.BlockCacheMoveStep(BC.NoOpStep));
//       assert BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp);
//       assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), JournalInternalOp);
//       assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
//       assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
//     } else if ValidSuperblockLocation(loc) && Some(io.id) == old_s.jc.superblockWrite {
//       assert s.jc == old_s.jc.WriteBackSuperblockResp(IIO(io));

//       if old_s.jc.statuold_s.StatusReady? && old_s.jc.commitStatuold_s.CommitAdvanceLocation? {
//         IOModel.cleanUpCorrect(old_s.bc);
//         assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), CleanUpOp);
//         assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
//       } else {
//         assert BC.NextStep(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp, BC.NoOpStep);
//         assert BBC.NextStep(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp, BBC.BlockCacheMoveStep(BC.NoOpStep));
//         assert BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp);

//         assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), JournalInternalOp);
//         assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
//       }
//       assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
//     } else {
//       // assert s' == s;
//       if ValidDiskOp(diskOp(IIO(io))) {
//         assert JC.NextStep(old_s.jc.I(), s.jc.I(), IDiskOp(diskOp(IIO(io))).jdop, JournalInternalOp, JC.NoOpStep);
//         assert JC.Next(old_s.jc.I(), s.jc.I(), IDiskOp(diskOp(IIO(io))).jdop, JournalInternalOp);
//         assert BC.NextStep(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp, BC.NoOpStep);
//         assert BBC.NextStep(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp, BBC.BlockCacheMoveStep(BC.NoOpStep));
//         assert BBC.Next(old_s.bc.I(), s.bc.I(), IDiskOp(diskOp(IIO(io))).bdop, JournalInternalOp);

//         assert BJC.NextStep(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))), JournalInternalOp);
//         assert BJC.Next(old_s.I(), s.I(), UI.NoOp, IDiskOp(diskOp(IIO(io))));
//       }

//       assert M.Next(old_s.I(), s.I(), UI.NoOp, diskOp(IIO(io)));
//     }
//   }

// }
