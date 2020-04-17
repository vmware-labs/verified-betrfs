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
  import opened ViewOp
  import BetreeJournalSystem
  import BetreeSystem
  import JournalSystem
  import UI
  
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

    if ValidNodeLocation(loc) {
      BlockSystem.NewRequestReadNodeIsValid(
        Ik(k).bs, I(k, s).bs, I(k, s').bs, idop.bdop, vop, bcstep);
    }
    else if ValidIndirectionTableLocation(loc) {
      BlockSystem.NewRequestReadIndirectionTableIsValid(
        Ik(k).bs, I(k, s).bs, I(k, s').bs, idop.bdop, vop, bcstep);
    }
    else if ValidJournalLocation(loc) {
      JournalSystem.NewRequestReadJournalIsValid(
        Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep);
    }
    else if ValidSuperblockLocation(loc) {
      JournalSystem.NewRequestReadSuperblockIsValid(
        Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep);
    }

    RefinesReqReadOp(k.disk, s.disk, s'.disk, dop);

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
        assert false;
      }
      else if ValidIndirectionTableLocation(loc) {
        BlockSystem.NewRequestWriteIndirectionTableDoesntOverlap(
            Ik(k).bs, I(k, s).bs, I(k, s').bs, idop.bdop, vop, bcstep, id1);
        assert false;
      }
      else if ValidJournalLocation(loc) {
        JournalSystem.NewRequestWriteJournalDoesntOverlap(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep, id1);
        assert false;
      }
      else if ValidSuperblockLocation(loc) {
        JournalSystem.NewRequestWriteSuperblockDoesntOverlap(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep);
        assert false;
      }
    }

    forall id1 | id1 in s.disk.respWrites
      && writesReqRespOverlap(dop.reqWrite, s.disk.respWrites[id1])
    ensures false
    {
      var loc1 := LocOfRespWrite(s.disk.respWrites[id1]);
      overlappingLocsSameType(loc1, loc);
      if ValidNodeLocation(loc) {
        BlockSystem.NewRequestWriteNodeDoesntOverlap(
            Ik(k).bs, I(k, s).bs, I(k, s').bs, idop.bdop, vop, bcstep, id1);
        assert false;
      }
      else if ValidIndirectionTableLocation(loc) {
        BlockSystem.NewRequestWriteIndirectionTableDoesntOverlap(
            Ik(k).bs, I(k, s).bs, I(k, s').bs, idop.bdop, vop, bcstep, id1);
        assert false;
      }
      else if ValidJournalLocation(loc) {
        JournalSystem.NewRequestWriteJournalDoesntOverlap(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep, id1);
        assert false;
      }
      else if ValidSuperblockLocation(loc) {
        JournalSystem.NewRequestWriteSuperblockDoesntOverlap(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep);
        assert false;
      }
    }

    forall id1 | id1 in s.disk.reqReads
      && writeReqReadOverlap(dop.reqWrite, s.disk.reqReads[id1])
    ensures false
    {
      var loc1 := LocOfReqRead(s.disk.reqReads[id1]);
      overlappingLocsSameType(loc1, loc);
      if ValidNodeLocation(loc) {
        BlockSystem.NewRequestWriteNodeDoesntOverlapRead(
            Ik(k).bs, I(k, s).bs, I(k, s').bs, idop.bdop, vop, bcstep, id1);
        assert false;
      }
      else if ValidIndirectionTableLocation(loc) {
        BlockSystem.NewRequestWriteIndirectionTableDoesntOverlapRead(
            Ik(k).bs, I(k, s).bs, I(k, s').bs, idop.bdop, vop, bcstep, id1);
        assert false;
      }
      else if ValidJournalLocation(loc) {
        JournalSystem.NewRequestWriteJournalDoesntOverlapRead(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep, id1);
        assert false;
      }
      else if ValidSuperblockLocation(loc) {
        JournalSystem.NewRequestWriteSuperblockDoesntOverlapRead(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep);
        assert loc == loc1;
        if idop.jdop.which == 0 {
          assert loc == Superblock1Location();
          assert loc1 == Superblock1Location();
          assert id1 in I(k, s).js.disk.reqReadSuperblock1;
        }
        if idop.jdop.which == 1 {
          assert loc == Superblock2Location();
          assert loc1 == Superblock2Location();
          assert id1 in I(k, s).js.disk.reqReadSuperblock2;
        }
        assert false;
      }
    }

    forall id1 | id1 in s.disk.respReads
      && writeRespReadOverlap(dop.reqWrite, s.disk.respReads[id1])
    ensures false
    {
      var loc1 := LocOfRespRead(s.disk.respReads[id1]);
      overlappingLocsSameType(loc1, loc);
      if ValidNodeLocation(loc) {
        BlockSystem.NewRequestWriteNodeDoesntOverlapRead(
            Ik(k).bs, I(k, s).bs, I(k, s').bs, idop.bdop, vop, bcstep, id1);
        assert false;
      }
      else if ValidIndirectionTableLocation(loc) {
        BlockSystem.NewRequestWriteIndirectionTableDoesntOverlapRead(
            Ik(k).bs, I(k, s).bs, I(k, s').bs, idop.bdop, vop, bcstep, id1);
        assert false;
      }
      else if ValidJournalLocation(loc) {
        JournalSystem.NewRequestWriteJournalDoesntOverlapRead(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep, id1);
        assert false;
      }
      else if ValidSuperblockLocation(loc) {
        JournalSystem.NewRequestWriteSuperblockDoesntOverlapRead(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep);
        assert loc == loc1;
        if idop.jdop.which == 0 {
          assert loc == Superblock1Location();
          assert loc1 == Superblock1Location();
          assert id1 in I(k, s).js.disk.reqReadSuperblock1;
        }
        if idop.jdop.which == 1 {
          assert loc == Superblock2Location();
          assert loc1 == Superblock2Location();
          assert id1 in I(k, s).js.disk.reqReadSuperblock2;
        }
        assert false;
      }
    }

    RefinesReqWriteOp(k.disk, s.disk, s'.disk, dop);

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

    var loc1 := LocOfReqWrite(dop.reqWrite1);
    var loc2 := LocOfReqWrite(dop.reqWrite2);
    assert ValidJournalLocation(loc1);
    assert ValidJournalLocation(loc2);

    forall id | id in s.disk.reqWrites
    ensures !writesOverlap(s.disk.reqWrites[id], dop.reqWrite1)
    ensures !writesOverlap(s.disk.reqWrites[id], dop.reqWrite2)
    {
      var loc := LocOfReqWrite(s.disk.reqWrites[id]);
      if writesOverlap(s.disk.reqWrites[id], dop.reqWrite1) {
        overlappingLocsSameType(loc1, loc);
      }
      if writesOverlap(s.disk.reqWrites[id], dop.reqWrite2) {
        overlappingLocsSameType(loc2, loc);
      }

      if ValidJournalLocation(loc) {
        JournalSystem.NewRequestWrite2JournalDoesntOverlap(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep, id);
      }
    }

    forall id | id in s.disk.respWrites
    ensures !writesReqRespOverlap(dop.reqWrite1, s.disk.respWrites[id])
    ensures !writesReqRespOverlap(dop.reqWrite2, s.disk.respWrites[id])
    {
      var loc := LocOfRespWrite(s.disk.respWrites[id]);
      if writesReqRespOverlap(dop.reqWrite1, s.disk.respWrites[id]) {
        overlappingLocsSameType(loc1, loc);
      }
      if writesReqRespOverlap(dop.reqWrite2, s.disk.respWrites[id]) {
        overlappingLocsSameType(loc2, loc);
      }

      if ValidJournalLocation(loc) {
        JournalSystem.NewRequestWrite2JournalDoesntOverlap(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep, id);
      }
    }

    forall id | id in s.disk.reqReads
    ensures !writeReqReadOverlap(dop.reqWrite1, s.disk.reqReads[id])
    ensures !writeReqReadOverlap(dop.reqWrite2, s.disk.reqReads[id])
    {
      var loc := LocOfReqRead(s.disk.reqReads[id]);
      if writeReqReadOverlap(dop.reqWrite1, s.disk.reqReads[id]) {
        overlappingLocsSameType(loc1, loc);
      }
      if writeReqReadOverlap(dop.reqWrite2, s.disk.reqReads[id]) {
        overlappingLocsSameType(loc2, loc);
      }

      if ValidJournalLocation(loc) {
        JournalSystem.NewRequestWrite2JournalDoesntOverlapRead(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep, id);
      }
    }

    forall id | id in s.disk.respReads
    ensures !writeRespReadOverlap(dop.reqWrite1, s.disk.respReads[id])
    ensures !writeRespReadOverlap(dop.reqWrite2, s.disk.respReads[id])
    {
      var loc := LocOfRespRead(s.disk.respReads[id]);
      if writeRespReadOverlap(dop.reqWrite1, s.disk.respReads[id]) {
        overlappingLocsSameType(loc1, loc);
      }
      if writeRespReadOverlap(dop.reqWrite2, s.disk.respReads[id]) {
        overlappingLocsSameType(loc2, loc);
      }

      if ValidJournalLocation(loc) {
        JournalSystem.NewRequestWrite2JournalDoesntOverlapRead(
            Ik(k).js, I(k, s).js, I(k, s').js, idop.jdop, vop, jstep, id);
      }
    }

    RefinesReqWrite2Op(k.disk, s.disk, s'.disk, dop);

    assert BetreeCache.Next(Ik(k).bs.machine, I(k,s).bs.machine, I(k,s').bs.machine, idop.bdop, vop);
    assert BetreeSystem.Machine(Ik(k).bs, I(k,s).bs, I(k,s').bs, idop.bdop, vop);
    assert BetreeSystem.NextStep(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop, BetreeSystem.MachineStep(idop.bdop));
    assert BetreeSystem.Next(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop);

    assert JournalSystem.Machine(Ik(k).js, I(k,s).js, I(k,s').js, idop.jdop, vop, jstep);
    assert JournalSystem.NextStep(Ik(k).js, I(k,s).js, I(k,s').js, vop, JournalSystem.MachineStep(idop.jdop, jstep));
    assert JournalSystem.Next(Ik(k).js, I(k,s).js, I(k,s').js, vop);

    assert BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), uiop);
    BetreeJournalSystem.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
  }

  lemma RespReadStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(k, s)
    requires Machine(k, s, s', uiop, dop)
    requires dop.RespReadOp?
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

    RefinesRespReadOp(k.disk, s.disk, s'.disk, dop);

    assert BetreeCache.Next(Ik(k).bs.machine, I(k,s).bs.machine, I(k,s').bs.machine, idop.bdop, vop);
    assert BetreeSystem.Machine(Ik(k).bs, I(k,s).bs, I(k,s').bs, idop.bdop, vop);
    assert BetreeSystem.NextStep(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop, BetreeSystem.MachineStep(idop.bdop));
    assert BetreeSystem.Next(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop);

    assert JournalSystem.Machine(Ik(k).js, I(k,s).js, I(k,s').js, idop.jdop, vop, jstep);
    assert JournalSystem.NextStep(Ik(k).js, I(k,s).js, I(k,s').js, vop, JournalSystem.MachineStep(idop.jdop, jstep));
    assert JournalSystem.Next(Ik(k).js, I(k,s).js, I(k,s').js, vop);

    assert BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), uiop);
    BetreeJournalSystem.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
  }

  lemma RespWriteStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(k, s)
    requires Machine(k, s, s', uiop, dop)
    requires dop.RespWriteOp?
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

    RefinesRespWriteOp(k.disk, s.disk, s'.disk, dop);

    assert BetreeCache.Next(Ik(k).bs.machine, I(k,s).bs.machine, I(k,s').bs.machine, idop.bdop, vop);
    assert BetreeSystem.Machine(Ik(k).bs, I(k,s).bs, I(k,s').bs, idop.bdop, vop);
    assert BetreeSystem.NextStep(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop, BetreeSystem.MachineStep(idop.bdop));
    assert BetreeSystem.Next(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop);

    assert JournalSystem.Machine(Ik(k).js, I(k,s).js, I(k,s').js, idop.jdop, vop, jstep);
    assert JournalSystem.NextStep(Ik(k).js, I(k,s).js, I(k,s').js, vop, JournalSystem.MachineStep(idop.jdop, jstep));
    assert JournalSystem.Next(Ik(k).js, I(k,s).js, I(k,s').js, vop);

    assert BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), uiop);
    BetreeJournalSystem.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
  }

  lemma NoDiskOpStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(k, s)
    requires Machine(k, s, s', uiop, dop)
    requires dop.NoDiskOp?
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
    //assert bstep.BlockCacheMoveStep?;
    //var bcstep := bstep.blockCacheStep;

    RefinesStutterOp(k.disk, s.disk, s'.disk, dop);

    assert JournalSystem.Machine(Ik(k).js, I(k,s).js, I(k,s').js, idop.jdop, vop, jstep);
    assert JournalSystem.NextStep(Ik(k).js, I(k,s).js, I(k,s').js, vop, JournalSystem.MachineStep(idop.jdop, jstep));
    assert JournalSystem.Next(Ik(k).js, I(k,s).js, I(k,s').js, vop);

    assert BetreeCache.Next(Ik(k).bs.machine, I(k,s).bs.machine, I(k,s').bs.machine, idop.bdop, vop);
    BetreeJournalSystem.OkaySendPersistentLocStep(Ik(k), I(k, s), I(k, s'), vop);
    assert BetreeSystem.Machine(Ik(k).bs, I(k,s).bs, I(k,s').bs, idop.bdop, vop);
    assert BetreeSystem.NextStep(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop, BetreeSystem.MachineStep(idop.bdop));
    assert BetreeSystem.Next(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop);

    assert BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), uiop);
    BetreeJournalSystem.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
  }

  lemma MachineStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(k, s)
    requires Machine(k, s, s', uiop, dop)
    ensures BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), uiop)
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

  lemma ProcessReadFailurePreservesInv(k: Constants, s: Variables, s': Variables, id: D.ReqId, fakeContents: seq<byte>)
    requires Inv(k, s)
    requires s.machine == s'.machine
    requires D.ProcessReadFailure(k.disk, s.disk, s'.disk, id, fakeContents)
    ensures BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), UI.NoOp)
    ensures Inv(k, s')
  {
    RefinesProcessRead(k.disk, s.disk, s'.disk, id, fakeContents);

    var vop := StatesInternalOp;
    var jstep := JournalCache.NoOpStep;
    var bstep := BC.NoOpStep;

    assert JournalSystem.Machine(Ik(k).js, I(k,s).js, I(k,s').js, JournalDisk.NoDiskOp, vop, jstep);
    assert JournalSystem.NextStep(Ik(k).js, I(k,s).js, I(k,s').js, vop, JournalSystem.MachineStep(JournalDisk.NoDiskOp, jstep));
    assert JournalSystem.Next(Ik(k).js, I(k,s).js, I(k,s').js, vop);

    assert BetreeCache.NextStep(Ik(k).bs.machine, I(k,s).bs.machine, I(k,s').bs.machine, BlockDisk.NoDiskOp, vop, BetreeCache.BlockCacheMoveStep(bstep));
    assert BetreeCache.Next(Ik(k).bs.machine, I(k,s).bs.machine, I(k,s').bs.machine, BlockDisk.NoDiskOp, vop);
    assert BetreeSystem.Machine(Ik(k).bs, I(k,s).bs, I(k,s').bs, BlockDisk.NoDiskOp, vop);
    assert BetreeSystem.NextStep(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop, BetreeSystem.MachineStep(BlockDisk.NoDiskOp));
    assert BetreeSystem.Next(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop);

    assert BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), UI.NoOp);
    BetreeJournalSystem.NextPreservesInv(Ik(k), I(k, s), I(k, s'), UI.NoOp);
  }

  lemma ProcessWritePreservesInv(k: Constants, s: Variables, s': Variables, id: D.ReqId)
    requires Inv(k, s)
    requires s.machine == s'.machine
    requires D.ProcessWrite(k.disk, s.disk, s'.disk, id)
    ensures BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), UI.NoOp)
    ensures Inv(k, s')
  {
    RefinesProcessWrite(k.disk, s.disk, s'.disk, id);

    var vop := JournalInternalOp;
    var bstep := BC.NoOpStep;

    if IJournalDisk(s.disk) == IJournalDisk(s'.disk) {
      var jstep := JournalCache.NoOpStep;
      assert JournalSystem.Machine(Ik(k).js, I(k,s).js, I(k,s').js, JournalDisk.NoDiskOp, vop, jstep);
      assert JournalSystem.NextStep(Ik(k).js, I(k,s).js, I(k,s').js, vop, JournalSystem.MachineStep(JournalDisk.NoDiskOp, jstep));
      assert JournalSystem.Next(Ik(k).js, I(k,s).js, I(k,s').js, vop);
    } else {
      var which :| (which == 0 || which == 1) &&
        JournalDisk.ProcessWriteSuperblock(JournalDisk.Constants(),   
          IJournalDisk(s.disk), IJournalDisk(s'.disk), which);
      var diskStep := JournalDisk.ProcessWriteSuperblockStep(which);
      assert JournalSystem.DiskInternal(Ik(k).js, I(k,s).js, I(k,s').js, diskStep, vop);
      assert JournalSystem.NextStep(Ik(k).js, I(k,s).js, I(k,s').js, vop, JournalSystem.DiskInternalStep(diskStep));
      assert JournalSystem.Next(Ik(k).js, I(k,s).js, I(k,s').js, vop);
    }

    assert BetreeCache.NextStep(Ik(k).bs.machine, I(k,s).bs.machine, I(k,s').bs.machine, BlockDisk.NoDiskOp, vop, BetreeCache.BlockCacheMoveStep(bstep));
    assert BetreeCache.Next(Ik(k).bs.machine, I(k,s).bs.machine, I(k,s').bs.machine, BlockDisk.NoDiskOp, vop);
    assert BetreeSystem.Machine(Ik(k).bs, I(k,s).bs, I(k,s').bs, BlockDisk.NoDiskOp, vop);
    assert BetreeSystem.NextStep(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop, BetreeSystem.MachineStep(BlockDisk.NoDiskOp));
    assert BetreeSystem.Next(Ik(k).bs, I(k,s).bs, I(k,s').bs, vop);

    assert BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), UI.NoOp);
    BetreeJournalSystem.NextPreservesInv(Ik(k), I(k, s), I(k, s'), UI.NoOp);
  }

  lemma DiskInternalStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: D.InternalStep)
    requires Inv(k, s)
    requires DiskInternal(k, s, s', uiop, step)
    ensures BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), uiop)
    ensures Inv(k, s')
  {
    match step {
      case ProcessReadFailureStep(id, fakeContents) => ProcessReadFailurePreservesInv(k, s, s', id, fakeContents);
      case ProcessWriteStep(id) => ProcessWritePreservesInv(k, s, s', id);
      case HavocConflictingWritesStep(id, id') => RefinesHavocConflictingWrites(k.disk, s.disk, s'.disk, id, id');
      case HavocConflictingWriteReadStep(id, id') => RefinesHavocConflictingWriteRead(k.disk, s.disk, s'.disk, id, id');
    }
  }

  lemma CrashStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp)
    requires Inv(k, s)
    requires Crash(k, s, s', uiop)
    ensures BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), uiop)
    ensures Inv(k, s')
  {
    RefinesCrash(k.disk, s.disk, s'.disk);

    var vop := StatesInternalOp;
    var jstep := JournalCache.NoOpStep;
    var bstep := BC.NoOpStep;

    assert JournalSystem.Crash(Ik(k).js, I(k,s).js, I(k,s').js, CrashOp);
    assert JournalSystem.NextStep(Ik(k).js, I(k,s).js, I(k,s').js, CrashOp, JournalSystem.CrashStep);
    assert JournalSystem.Next(Ik(k).js, I(k,s).js, I(k,s').js, CrashOp);

    assert BetreeSystem.Crash(Ik(k).bs, I(k,s).bs, I(k,s').bs, CrashOp);
    assert BetreeSystem.NextStep(Ik(k).bs, I(k,s).bs, I(k,s').bs, CrashOp, BetreeSystem.CrashStep);
    assert BetreeSystem.Next(Ik(k).bs, I(k,s).bs, I(k,s').bs, CrashOp);

    assert BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), UI.CrashOp);
    BetreeJournalSystem.NextPreservesInv(Ik(k), I(k, s), I(k, s'), UI.CrashOp);

  }

  lemma NextStepPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: Step)
    requires Inv(k, s)
    requires NextStep(k, s, s', uiop, step)
    ensures BetreeJournalSystem.Next(Ik(k), I(k, s), I(k, s'), uiop)
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
