include "AsyncDiskModel.s.dfy"
include "ByteCache.i.dfy"
include "InterpretationDisk.i.dfy"
include "../BlockCacheSystem/BetreeJournalSystem.i.dfy"

module ByteSystem refines AsyncDiskModel {
  import M = ByteCache

  import opened AsyncSectorDiskModelTypes
  import opened Maps
  import BC = BlockCache
  import JournalCache
  import BetreeCache
  import BJC = BlockJournalCache
  import BJD = BlockJournalDisk
  import BlockSystem
  import opened DiskLayout
  import opened JournalIntervals
  import opened InterpretationDisk
  import opened InterpretationDiskOps
  import opened SectorType
  import opened Options
  import opened JournalRanges
  import BetreeJournalSystem
  import BetreeSystem
  import JournalSystem
  
  function Ik(k: Constants) : BetreeJournalSystem.Constants
  {
    BetreeJournalSystem.Constants(
      AsyncSectorDiskModelConstants(k.machine.bc, BlockDisk.Constants()),
      AsyncSectorDiskModelConstants(k.machine.jc, JournalDisk.Constants())
    )
  }

  function I(k: Constants, s: Variables) : BetreeJournalSystem.Variables
  requires reqWritesHaveValidSuperblocks(s.disk.reqWrites)
  {
    BetreeJournalSystem.Variables(
      AsyncSectorDiskModelVariables(s.machine.bc, IBlockDisk(s.disk)),
      AsyncSectorDiskModelVariables(s.machine.jc, IJournalDisk(s.disk))
    )
  }

  predicate Init(k: Constants, s: Variables)
  {
    && D.Init(k.disk, s.disk)
    && BetreeJournalSystem.Init(Ik(k), I(k, s))
  }

  ///// Define Inv

  predicate Inv(k: Constants, s: Variables)
  {
    && InterpretationDisk.Inv(s.disk)
    && BetreeJournalSystem.Inv(Ik(k), I(k, s))
  }
  
  lemma InitImpliesInv(k: Constants, s: Variables)
    // Inherited from abstract module:
    //requires Init(k, s)
    //ensures Inv(k, s)
  {
    BetreeJournalSystem.InitImpliesInv(Ik(k), I(k, s));
  }

  lemma ReqReadStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(k, s)
    requires Machine(k, s, s', uiop, dop)
    requires dop.ReqReadOp?
    ensures BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), uiop)
    ensures Inv(k, s')
  {
    var idop := IDiskOp(dop);
    var vop :| BJC.NextStep(k.machine, s.machine, s'.machine,
        uiop, idop, vop);
    assert BetreeCache.Next(k.machine.bc, s.machine.bc, s'.machine.bc, idop.bdop, vop);
    assert JournalCache.Next(k.machine.jc, s.machine.jc, s'.machine.jc, idop.jdop, vop);
    var bstep :| BetreeCache.NextStep(k.machine.bc, s.machine.bc, s'.machine.bc, idop.bdop, vop, bstep);
    var jstep :| JournalCache.NextStep(k.machine.jc, s.machine.jc, s'.machine.jc, idop.jdop, vop, jstep);
    assert bstep.BlockCacheMoveStep?;
    var bcstep := bstep.blockCacheStep;

    var loc := LocOfReqRead(dop.reqRead);

    forall id1 | id1 in s.disk.reqWrites
      && writeReqReadOverlap(s.disk.reqWrites[id1], dop.reqRead)
    ensures false
    {
      var loc1 := LocOfReqWrite(s.disk.reqWrites[id1]);
      overlappingLocsSameType(loc1, loc);
      if ValidNodeLocation(loc) {
        BlockSystem.NewRequestReadNodeDoesntOverlap(
            Ik(k).bs, I(k, s).bs, I(k, s').bs, idop.bdop, vop, bcstep, id1);
      }
      else if ValidIndirectionTableLocation(loc) {
        //assert ReqReadIndirectionTables(s'.disk)
        //    == ReqReadIndirectionTables(s.disk)[dop.id := loc];
        BlockSystem.NewRequestReadIndirectionTableDoesntOverlap(
            Ik(k).bs, I(k, s).bs, I(k, s').bs, idop.bdop, vop, bcstep, id1);
      }
      else if ValidJournalLocation(loc) {
        JournalSystem.NewRequestReadJournalDoesntOverlap(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep, id1);
      }
      else if ValidSuperblockLocation(loc) {
        JournalSystem.NewRequestReadSuperblockDoesntOverlap(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep);
      }
    }

   /* assert BlockSystem.Machine(Ik(k).bs, I(k,s).bs, I(k,s').bs, idop.bdop, vop, bcstep);
    assert BlockSystem.NextStep(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop, BlockSystem.MachineStep(idop.bdop, bcstep));
    assert BlockSystem.Next(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop);*/

    assert BetreeCache.Next(Ik(k).bs.machine, I(k,s).bs.machine, I(k,s').bs.machine, idop.bdop, vop);
    assert BetreeSystem.Machine(Ik(k).bs, I(k,s).bs, I(k,s').bs, idop.bdop, vop);
    assert BetreeSystem.NextStep(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop, BetreeSystem.MachineStep(idop.bdop));
    assert BetreeSystem.Next(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop);

    if ValidJournalLocation(loc) {
      /*assert ReqReadJournals(s'.disk)
          == ReqReadJournals(s.disk)[dop.id := idop.jdop.interval];
      assert ReqReadSuperblock1(s'.disk)
          == ReqReadSuperblock1(s.disk);
      assert ReqReadSuperblock2(s'.disk)
          == ReqReadSuperblock2(s.disk);*/
      assert JournalSystem.Machine(Ik(k).js, I(k,s).js, I(k,s').js, idop.jdop, vop, jstep);
    } else if ValidSuperblockLocation(loc) {
      assert JournalSystem.Machine(Ik(k).js, I(k,s).js, I(k,s').js, idop.jdop, vop, jstep);
    } else {
      assert JournalSystem.Machine(Ik(k).js, I(k,s).js, I(k,s').js, idop.jdop, vop, jstep);
    }

    assert JournalSystem.NextStep(Ik(k).js, I(k,s).js, I(k,s').js, vop, JournalSystem.MachineStep(idop.jdop, jstep));
    assert JournalSystem.Next(Ik(k).js, I(k,s).js, I(k,s').js, vop);

    assert BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), uiop);
    BetreeJournalSystem.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
  }

  lemma ReqWriteStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(k, s)
    requires Machine(k, s, s', uiop, dop)
    requires dop.ReqWriteOp?
    ensures Inv(k, s')
  {
    var idop := IDiskOp(dop);
    var vop :| BJC.NextStep(k.machine, s.machine, s'.machine,
        uiop, idop, vop);
    assert BetreeCache.Next(k.machine.bc, s.machine.bc, s'.machine.bc, idop.bdop, vop);
    assert JournalCache.Next(k.machine.jc, s.machine.jc, s'.machine.jc, idop.jdop, vop);
    var bstep :| BetreeCache.NextStep(k.machine.bc, s.machine.bc, s'.machine.bc, idop.bdop, vop, bstep);
    var jstep :| JournalCache.NextStep(k.machine.jc, s.machine.jc, s'.machine.jc, idop.jdop, vop, jstep);
    assert bstep.BlockCacheMoveStep?;
    var bcstep := bstep.blockCacheStep;

    var loc := LocOfReqWrite(dop.reqWrite);

    forall id1 | id1 in s.disk.reqWrites
      && writesOverlap(s.disk.reqWrites[id1], dop.reqWrite)
    ensures false
    {
      var loc1 := LocOfReqWrite(s.disk.reqWrites[id1]);
      overlappingLocsSameType(loc1, loc);
      if ValidNodeLocation(loc) {
        BlockSystem.NewRequestWriteNodeDoesntOverlap(
            Ik(k).bs, I(k, s).bs, I(k, s').bs, idop.bdop, vop, bcstep, id1);
      }
      else if ValidIndirectionTableLocation(loc) {
        BlockSystem.NewRequestWriteIndirectionTableDoesntOverlap(
            Ik(k).bs, I(k, s).bs, I(k, s').bs, idop.bdop, vop, bcstep, id1);
      }
      else if ValidJournalLocation(loc) {
        JournalSystem.NewRequestWriteJournalDoesntOverlap(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep, id1);
      }
      else if ValidSuperblockLocation(loc) {
        JournalSystem.NewRequestWriteSuperblockDoesntOverlap(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep);
      }
    }

    forall id1 | id1 in s.disk.reqReads
      && writeReqReadOverlap(dop.reqWrite, s.disk.reqReads[id1])
    ensures false
    {
    }

    forall id1 | id1 in s.disk.respReads
      && writeRespReadOverlap(dop.reqWrite, s.disk.respReads[id1])
    ensures false
    {
    }

    assert BlockDisk.Next(Ik(k).bs.disk,
        IBlockDisk(s.disk),
        IBlockDisk(s'.disk),
        idop.bdop);
    assert JournalDisk.Next(Ik(k).js.disk,
        IJournalDisk(s.disk),
        IJournalDisk(s'.disk),
        idop.jdop);

    assert BetreeCache.Next(Ik(k).bs.machine, I(k,s).bs.machine, I(k,s').bs.machine, idop.bdop, vop);
    assert BetreeSystem.Machine(Ik(k).bs, I(k,s).bs, I(k,s').bs, idop.bdop, vop);
    assert BetreeSystem.NextStep(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop, BetreeSystem.MachineStep(idop.bdop));
    assert BetreeSystem.Next(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop);

    if ValidJournalLocation(loc) {
      assert JournalSystem.Machine(Ik(k).js, I(k,s).js, I(k,s').js, idop.jdop, vop, jstep);
    } else if ValidSuperblockLocation(loc) {
      assert JournalSystem.Machine(Ik(k).js, I(k,s).js, I(k,s').js, idop.jdop, vop, jstep);
    } else {
      assert JournalSystem.Machine(Ik(k).js, I(k,s).js, I(k,s').js, idop.jdop, vop, jstep);
    }

    assert JournalSystem.NextStep(Ik(k).js, I(k,s).js, I(k,s').js, vop, JournalSystem.MachineStep(idop.jdop, jstep));
    assert JournalSystem.Next(Ik(k).js, I(k,s).js, I(k,s').js, vop);

    assert BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), uiop);
    BetreeJournalSystem.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);

  }

  lemma ReqWrite2StepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(k, s)
    requires Machine(k, s, s', uiop, dop)
    requires dop.ReqWrite2Op?
    ensures Inv(k, s')
  {
  }

  lemma RespReadStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(k, s)
    requires Machine(k, s, s', uiop, dop)
    requires dop.RespReadOp?
    ensures Inv(k, s')
  {
  }

  lemma RespWriteStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(k, s)
    requires Machine(k, s, s', uiop, dop)
    requires dop.RespWriteOp?
    ensures Inv(k, s')
  {
  }

  lemma NoDiskOpStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(k, s)
    requires Machine(k, s, s', uiop, dop)
    requires dop.NoDiskOp?
    ensures Inv(k, s')
  {
  }

  lemma MachineStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(k, s)
    requires Machine(k, s, s', uiop, dop)
    ensures Inv(k, s')
  {
    match dop {
      case ReqReadOp(_, _) => ReqReadStepPreservesInv(k, s, s', uiop, dop);
      case ReqWriteOp(_, _) => ReqWriteStepPreservesInv(k, s, s', uiop, dop);
      case ReqWrite2Op(_, _, _, _) => ReqWrite2StepPreservesInv(k, s, s', uiop, dop);
      case RespReadOp(_, _) => RespReadStepPreservesInv(k, s, s', uiop, dop);
      case RespWriteOp(_, _) => RespWriteStepPreservesInv(k, s, s', uiop, dop);
      case NoDiskOp => NoDiskOpStepPreservesInv(k, s, s', uiop, dop);
    }
  }

  lemma DiskInternalStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: D.InternalStep)
    requires Inv(k, s)
    requires DiskInternal(k, s, s', uiop, step)
    ensures Inv(k, s')
  {
  }

  lemma CrashStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp)
    requires Inv(k, s)
    requires Crash(k, s, s', uiop)
    ensures Inv(k, s')
  {
  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', uiop, step)
    ensures Inv(k, s')
  {
    match step {
      case MachineStep(dop) => MachineStepPreservesInv(k, s, s', uiop, dop);
      case DiskInternalStep(step) => DiskInternalStepPreservesInv(k, s, s', uiop, step);
      case CrashStep => CrashStepPreservesInv(k, s, s', uiop);
    }
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp)
    // Inherited from abstract module:
    //requires Inv(k, s)
    //requires Next(k, s, s', uiop)
    //ensures Inv(k, s')
  {
    var step :| NextStep(k, s, s', uiop, step);
    NextStepPreservesInv(k, s, s', uiop, step);
  }
}
