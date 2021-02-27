// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

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
  
  function I(s: Variables) : BetreeJournalSystem.Variables
  requires reqWritesHaveValidSuperblocks(s.disk.reqWrites)
  {
    BetreeJournalSystem.Variables(
      AsyncSectorDiskModelVariables(s.machine.bc, IBlockDisk(s.disk)),
      AsyncSectorDiskModelVariables(s.machine.jc, IJournalDisk(s.disk))
    )
  }

  predicate Init(s: Variables)
  {
    && D.Init(s.disk)
    && BetreeJournalSystem.Init(I(s))
  }

  ///// Define Inv

  predicate Inv(s: Variables)
  {
    && InterpretationDisk.Inv(s.disk)
    && BetreeJournalSystem.Inv(I(s))
  }
  
  lemma InitImpliesInv(s: Variables)
    // Inherited from abstract module:
    //requires Init(s)
    //ensures Inv(s)
  {
    BetreeJournalSystem.InitImpliesInv(I(s));
  }

  lemma ReqReadStepPreservesInv(s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(s)
    requires Machine(s, s', uiop, dop)
    requires dop.ReqReadOp?
    ensures BetreeJournalSystem.Next(I(s), I(s'), uiop)
    ensures Inv(s')
  {
    var idop := IDiskOp(dop);
    var vop :| BJC.NextStep(s.machine, s'.machine,
        uiop, idop, vop);
    assert BetreeCache.Next(s.machine.bc, s'.machine.bc, idop.bdop, vop);
    assert JournalCache.Next(s.machine.jc, s'.machine.jc, idop.jdop, vop);
    var bstep :| BetreeCache.NextStep(s.machine.bc, s'.machine.bc, idop.bdop, vop, bstep);
    var jstep :| JournalCache.NextStep(s.machine.jc, s'.machine.jc, idop.jdop, vop, jstep);
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
            I(s).bs, I(s').bs, idop.bdop, vop, bcstep, id1);
      }
      else if ValidIndirectionTableLocation(loc) {
        //assert ReqReadIndirectionTables(s'.disk)
        //    == ReqReadIndirectionTables(s.disk)[dop.id := loc];
        BlockSystem.NewRequestReadIndirectionTableDoesntOverlap(
            I(s).bs, I(s').bs, idop.bdop, vop, bcstep, id1);
      }
      else if ValidJournalLocation(loc) {
        JournalSystem.NewRequestReadJournalDoesntOverlap(
            I(s).js, I(s').js, idop.jdop, vop, jstep, id1);
      }
      else if ValidSuperblockLocation(loc) {
        JournalSystem.NewRequestReadSuperblockDoesntOverlap(
            I(s).js, I(s').js, idop.jdop, vop, jstep);
      }
    }

    if ValidNodeLocation(loc) {
      BlockSystem.NewRequestReadNodeIsValid(
        I(s).bs, I(s').bs, idop.bdop, vop, bcstep);
    }
    else if ValidIndirectionTableLocation(loc) {
      BlockSystem.NewRequestReadIndirectionTableIsValid(
        I(s).bs, I(s').bs, idop.bdop, vop, bcstep);
    }
    else if ValidJournalLocation(loc) {
      JournalSystem.NewRequestReadJournalIsValid(
        I(s).js, I(s').js, idop.jdop, vop, jstep);
    }
    else if ValidSuperblockLocation(loc) {
      JournalSystem.NewRequestReadSuperblockIsValid(
        I(s).js, I(s').js, idop.jdop, vop, jstep);
    }

    RefinesReqReadOp(s.disk, s'.disk, dop);

   /* assert BlockSystem.Machine(I(s).bs, I(s').bs, idop.bdop, vop, bcstep);
    assert BlockSystem.NextStep(I(s).bs, I(s').bs, vop, BlockSystem.MachineStep(idop.bdop, bcstep));
    assert BlockSystem.Next(I(s).bs, I(s').bs, vop);*/

    assert BetreeCache.Next(I(s).bs.machine, I(s').bs.machine, idop.bdop, vop);
    assert BetreeSystem.Machine(I(s).bs, I(s').bs, idop.bdop, vop);
    assert BetreeSystem.NextStep(I(s).bs, I(s').bs, vop, BetreeSystem.MachineStep(idop.bdop));
    assert BetreeSystem.Next(I(s).bs, I(s').bs, vop);

    if ValidJournalLocation(loc) {
      /*assert ReqReadJournals(s'.disk)
          == ReqReadJournals(s.disk)[dop.id := idop.jdop.interval];
      assert ReqReadSuperblock1(s'.disk)
          == ReqReadSuperblock1(s.disk);
      assert ReqReadSuperblock2(s'.disk)
          == ReqReadSuperblock2(s.disk);*/
      assert JournalSystem.Machine(I(s).js, I(s').js, idop.jdop, vop, jstep);
    } else if ValidSuperblockLocation(loc) {
      assert JournalSystem.Machine(I(s).js, I(s').js, idop.jdop, vop, jstep);
    } else {
      assert JournalSystem.Machine(I(s).js, I(s').js, idop.jdop, vop, jstep);
    }

    assert JournalSystem.NextStep(I(s).js, I(s').js, vop, JournalSystem.MachineStep(idop.jdop, jstep));
    assert JournalSystem.Next(I(s).js, I(s').js, vop);

    assert BetreeJournalSystem.Next(I(s), I(s'), uiop);
    BetreeJournalSystem.NextPreservesInv(I(s), I(s'), uiop);
  }

  lemma ReqWriteStepPreservesInv(s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(s)
    requires Machine(s, s', uiop, dop)
    requires dop.ReqWriteOp?
    ensures BetreeJournalSystem.Next(I(s), I(s'), uiop)
    ensures Inv(s')
  {
    var idop := IDiskOp(dop);
    var vop :| BJC.NextStep(s.machine, s'.machine,
        uiop, idop, vop);
    assert BetreeCache.Next(s.machine.bc, s'.machine.bc, idop.bdop, vop);
    assert JournalCache.Next(s.machine.jc, s'.machine.jc, idop.jdop, vop);
    var bstep :| BetreeCache.NextStep(s.machine.bc, s'.machine.bc, idop.bdop, vop, bstep);
    var jstep :| JournalCache.NextStep(s.machine.jc, s'.machine.jc, idop.jdop, vop, jstep);
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
            I(s).bs, I(s').bs, idop.bdop, vop, bcstep, id1);
        assert false;
      }
      else if ValidIndirectionTableLocation(loc) {
        BlockSystem.NewRequestWriteIndirectionTableDoesntOverlap(
            I(s).bs, I(s').bs, idop.bdop, vop, bcstep, id1);
        assert false;
      }
      else if ValidJournalLocation(loc) {
        JournalSystem.NewRequestWriteJournalDoesntOverlap(
            I(s).js, I(s').js, idop.jdop, vop, jstep, id1);
        assert false;
      }
      else if ValidSuperblockLocation(loc) {
        JournalSystem.NewRequestWriteSuperblockDoesntOverlap(
            I(s).js, I(s').js, idop.jdop, vop, jstep);
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
            I(s).bs, I(s').bs, idop.bdop, vop, bcstep, id1);
        assert false;
      }
      else if ValidIndirectionTableLocation(loc) {
        BlockSystem.NewRequestWriteIndirectionTableDoesntOverlap(
            I(s).bs, I(s').bs, idop.bdop, vop, bcstep, id1);
        assert false;
      }
      else if ValidJournalLocation(loc) {
        JournalSystem.NewRequestWriteJournalDoesntOverlap(
            I(s).js, I(s').js, idop.jdop, vop, jstep, id1);
        assert false;
      }
      else if ValidSuperblockLocation(loc) {
        JournalSystem.NewRequestWriteSuperblockDoesntOverlap(
            I(s).js, I(s').js, idop.jdop, vop, jstep);
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
            I(s).bs, I(s').bs, idop.bdop, vop, bcstep, id1);
        assert false;
      }
      else if ValidIndirectionTableLocation(loc) {
        BlockSystem.NewRequestWriteIndirectionTableDoesntOverlapRead(
            I(s).bs, I(s').bs, idop.bdop, vop, bcstep, id1);
        assert false;
      }
      else if ValidJournalLocation(loc) {
        JournalSystem.NewRequestWriteJournalDoesntOverlapRead(
            I(s).js, I(s').js, idop.jdop, vop, jstep, id1);
        assert false;
      }
      else if ValidSuperblockLocation(loc) {
        JournalSystem.NewRequestWriteSuperblockDoesntOverlapRead(
            I(s).js, I(s').js, idop.jdop, vop, jstep);
        assert loc == loc1;
        if idop.jdop.which == 0 {
          assert loc == Superblock1Location();
          assert loc1 == Superblock1Location();
          assert id1 in I(s).js.disk.reqReadSuperblock1;
        }
        if idop.jdop.which == 1 {
          assert loc == Superblock2Location();
          assert loc1 == Superblock2Location();
          assert id1 in I(s).js.disk.reqReadSuperblock2;
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
            I(s).bs, I(s').bs, idop.bdop, vop, bcstep, id1);
        assert false;
      }
      else if ValidIndirectionTableLocation(loc) {
        BlockSystem.NewRequestWriteIndirectionTableDoesntOverlapRead(
            I(s).bs, I(s').bs, idop.bdop, vop, bcstep, id1);
        assert false;
      }
      else if ValidJournalLocation(loc) {
        JournalSystem.NewRequestWriteJournalDoesntOverlapRead(
            I(s).js, I(s').js, idop.jdop, vop, jstep, id1);
        assert false;
      }
      else if ValidSuperblockLocation(loc) {
        JournalSystem.NewRequestWriteSuperblockDoesntOverlapRead(
            I(s).js, I(s').js, idop.jdop, vop, jstep);
        assert loc == loc1;
        if idop.jdop.which == 0 {
          assert loc == Superblock1Location();
          assert loc1 == Superblock1Location();
          assert id1 in I(s).js.disk.reqReadSuperblock1;
        }
        if idop.jdop.which == 1 {
          assert loc == Superblock2Location();
          assert loc1 == Superblock2Location();
          assert id1 in I(s).js.disk.reqReadSuperblock2;
        }
        assert false;
      }
    }

    RefinesReqWriteOp(s.disk, s'.disk, dop);

    assert BlockDisk.Next(
        IBlockDisk(s.disk),
        IBlockDisk(s'.disk),
        idop.bdop);
    assert JournalDisk.Next(
        IJournalDisk(s.disk),
        IJournalDisk(s'.disk),
        idop.jdop);

    assert BetreeCache.Next(I(s).bs.machine, I(s').bs.machine, idop.bdop, vop);
    assert BetreeSystem.Machine(I(s).bs, I(s').bs, idop.bdop, vop);
    assert BetreeSystem.NextStep(I(s).bs, I(s').bs, vop, BetreeSystem.MachineStep(idop.bdop));
    assert BetreeSystem.Next(I(s).bs, I(s').bs, vop);

    if ValidJournalLocation(loc) {
      assert JournalSystem.Machine(I(s).js, I(s').js, idop.jdop, vop, jstep);
    } else if ValidSuperblockLocation(loc) {
      assert JournalSystem.Machine(I(s).js, I(s').js, idop.jdop, vop, jstep);
    } else {
      assert JournalSystem.Machine(I(s).js, I(s').js, idop.jdop, vop, jstep);
    }

    assert JournalSystem.NextStep(I(s).js, I(s').js, vop, JournalSystem.MachineStep(idop.jdop, jstep));
    assert JournalSystem.Next(I(s).js, I(s').js, vop);

    assert BetreeJournalSystem.Next(I(s), I(s'), uiop);
    BetreeJournalSystem.NextPreservesInv(I(s), I(s'), uiop);

  }

  lemma ReqWrite2StepPreservesInv(s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(s)
    requires Machine(s, s', uiop, dop)
    requires dop.ReqWrite2Op?
    ensures BetreeJournalSystem.Next(I(s), I(s'), uiop)
    ensures Inv(s')
  {
    var idop := IDiskOp(dop);
    var vop :| BJC.NextStep(s.machine, s'.machine,
        uiop, idop, vop);
    assert BetreeCache.Next(s.machine.bc, s'.machine.bc, idop.bdop, vop);
    assert JournalCache.Next(s.machine.jc, s'.machine.jc, idop.jdop, vop);
    var bstep :| BetreeCache.NextStep(s.machine.bc, s'.machine.bc, idop.bdop, vop, bstep);
    var jstep :| JournalCache.NextStep(s.machine.jc, s'.machine.jc, idop.jdop, vop, jstep);
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
            I(s).js, I(s').js, idop.jdop, vop, jstep, id);
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
            I(s).js, I(s').js, idop.jdop, vop, jstep, id);
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
            I(s).js, I(s').js, idop.jdop, vop, jstep, id);
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
            I(s).js, I(s').js, idop.jdop, vop, jstep, id);
      }
    }

    RefinesReqWrite2Op(s.disk, s'.disk, dop);

    assert BetreeCache.Next(I(s).bs.machine, I(s').bs.machine, idop.bdop, vop);
    assert BetreeSystem.Machine(I(s).bs, I(s').bs, idop.bdop, vop);
    assert BetreeSystem.NextStep(I(s).bs, I(s').bs, vop, BetreeSystem.MachineStep(idop.bdop));
    assert BetreeSystem.Next(I(s).bs, I(s').bs, vop);

    assert JournalSystem.Machine(I(s).js, I(s').js, idop.jdop, vop, jstep);
    assert JournalSystem.NextStep(I(s).js, I(s').js, vop, JournalSystem.MachineStep(idop.jdop, jstep));
    assert JournalSystem.Next(I(s).js, I(s').js, vop);

    assert BetreeJournalSystem.Next(I(s), I(s'), uiop);
    BetreeJournalSystem.NextPreservesInv(I(s), I(s'), uiop);
  }

  lemma RespReadStepPreservesInv(s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(s)
    requires Machine(s, s', uiop, dop)
    requires dop.RespReadOp?
    ensures BetreeJournalSystem.Next(I(s), I(s'), uiop)
    ensures Inv(s')
  {
    var idop := IDiskOp(dop);
    var vop :| BJC.NextStep(s.machine, s'.machine,
        uiop, idop, vop);
    assert BetreeCache.Next(s.machine.bc, s'.machine.bc, idop.bdop, vop);
    assert JournalCache.Next(s.machine.jc, s'.machine.jc, idop.jdop, vop);
    var bstep :| BetreeCache.NextStep(s.machine.bc, s'.machine.bc, idop.bdop, vop, bstep);
    var jstep :| JournalCache.NextStep(s.machine.jc, s'.machine.jc, idop.jdop, vop, jstep);
    assert bstep.BlockCacheMoveStep?;
    var bcstep := bstep.blockCacheStep;

    RefinesRespReadOp(s.disk, s'.disk, dop);

    assert BetreeCache.Next(I(s).bs.machine, I(s').bs.machine, idop.bdop, vop);
    assert BetreeSystem.Machine(I(s).bs, I(s').bs, idop.bdop, vop);
    assert BetreeSystem.NextStep(I(s).bs, I(s').bs, vop, BetreeSystem.MachineStep(idop.bdop));
    assert BetreeSystem.Next(I(s).bs, I(s').bs, vop);

    assert JournalSystem.Machine(I(s).js, I(s').js, idop.jdop, vop, jstep);
    assert JournalSystem.NextStep(I(s).js, I(s').js, vop, JournalSystem.MachineStep(idop.jdop, jstep));
    assert JournalSystem.Next(I(s).js, I(s').js, vop);

    assert BetreeJournalSystem.Next(I(s), I(s'), uiop);
    BetreeJournalSystem.NextPreservesInv(I(s), I(s'), uiop);
  }

  lemma RespWriteStepPreservesInv(s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(s)
    requires Machine(s, s', uiop, dop)
    requires dop.RespWriteOp?
    ensures BetreeJournalSystem.Next(I(s), I(s'), uiop)
    ensures Inv(s')
  {
    var idop := IDiskOp(dop);
    var vop :| BJC.NextStep(s.machine, s'.machine,
        uiop, idop, vop);
    assert BetreeCache.Next(s.machine.bc, s'.machine.bc, idop.bdop, vop);
    assert JournalCache.Next(s.machine.jc, s'.machine.jc, idop.jdop, vop);
    var bstep :| BetreeCache.NextStep(s.machine.bc, s'.machine.bc, idop.bdop, vop, bstep);
    var jstep :| JournalCache.NextStep(s.machine.jc, s'.machine.jc, idop.jdop, vop, jstep);
    assert bstep.BlockCacheMoveStep?;
    var bcstep := bstep.blockCacheStep;

    RefinesRespWriteOp(s.disk, s'.disk, dop);

    assert BetreeCache.Next(I(s).bs.machine, I(s').bs.machine, idop.bdop, vop);
    assert BetreeSystem.Machine(I(s).bs, I(s').bs, idop.bdop, vop);
    assert BetreeSystem.NextStep(I(s).bs, I(s').bs, vop, BetreeSystem.MachineStep(idop.bdop));
    assert BetreeSystem.Next(I(s).bs, I(s').bs, vop);

    assert JournalSystem.Machine(I(s).js, I(s').js, idop.jdop, vop, jstep);
    assert JournalSystem.NextStep(I(s).js, I(s').js, vop, JournalSystem.MachineStep(idop.jdop, jstep));
    assert JournalSystem.Next(I(s).js, I(s').js, vop);

    assert BetreeJournalSystem.Next(I(s), I(s'), uiop);
    BetreeJournalSystem.NextPreservesInv(I(s), I(s'), uiop);
  }

  lemma NoDiskOpStepPreservesInv(s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(s)
    requires Machine(s, s', uiop, dop)
    requires dop.NoDiskOp?
    ensures BetreeJournalSystem.Next(I(s), I(s'), uiop)
    ensures Inv(s')
  {
    var idop := IDiskOp(dop);
    var vop :| BJC.NextStep(s.machine, s'.machine,
        uiop, idop, vop);
    assert BetreeCache.Next(s.machine.bc, s'.machine.bc, idop.bdop, vop);
    assert JournalCache.Next(s.machine.jc, s'.machine.jc, idop.jdop, vop);
    var bstep :| BetreeCache.NextStep(s.machine.bc, s'.machine.bc, idop.bdop, vop, bstep);
    var jstep :| JournalCache.NextStep(s.machine.jc, s'.machine.jc, idop.jdop, vop, jstep);
    //assert bstep.BlockCacheMoveStep?;
    //var bcstep := bstep.blockCacheStep;

    RefinesStutterOp(s.disk, s'.disk, dop);

    assert JournalSystem.Machine(I(s).js, I(s').js, idop.jdop, vop, jstep);
    assert JournalSystem.NextStep(I(s).js, I(s').js, vop, JournalSystem.MachineStep(idop.jdop, jstep));
    assert JournalSystem.Next(I(s).js, I(s').js, vop);

    assert BetreeCache.Next(I(s).bs.machine, I(s').bs.machine, idop.bdop, vop);
    BetreeJournalSystem.OkaySendPersistentLocStep(I(s), I(s'), vop);
    assert BetreeSystem.Machine(I(s).bs, I(s').bs, idop.bdop, vop);
    assert BetreeSystem.NextStep(I(s).bs, I(s').bs, vop, BetreeSystem.MachineStep(idop.bdop));
    assert BetreeSystem.Next(I(s).bs, I(s').bs, vop);

    assert BetreeJournalSystem.Next(I(s), I(s'), uiop);
    BetreeJournalSystem.NextPreservesInv(I(s), I(s'), uiop);
  }

  lemma MachineStepPreservesInv(s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(s)
    requires Machine(s, s', uiop, dop)
    ensures BetreeJournalSystem.Next(I(s), I(s'), uiop)
    ensures Inv(s')
  {
    match dop {
      case ReqReadOp(_, _) => ReqReadStepPreservesInv(s, s', uiop, dop);
      case ReqWriteOp(_, _) => ReqWriteStepPreservesInv(s, s', uiop, dop);
      case ReqWrite2Op(_, _, _, _) => ReqWrite2StepPreservesInv(s, s', uiop, dop);
      case RespReadOp(_, _) => RespReadStepPreservesInv(s, s', uiop, dop);
      case RespWriteOp(_, _) => RespWriteStepPreservesInv(s, s', uiop, dop);
      case NoDiskOp => NoDiskOpStepPreservesInv(s, s', uiop, dop);
    }
  }

  lemma ProcessReadFailurePreservesInv(s: Variables, s': Variables, id: D.ReqId, fakeContents: seq<byte>)
    requires Inv(s)
    requires s.machine == s'.machine
    requires D.ProcessReadFailure(s.disk, s'.disk, id, fakeContents)
    ensures BetreeJournalSystem.Next(I(s), I(s'), UI.NoOp)
    ensures Inv(s')
  {
    RefinesProcessRead(s.disk, s'.disk, id, fakeContents);

    var vop := StatesInternalOp;
    var jstep := JournalCache.NoOpStep;
    var bstep := BC.NoOpStep;

    assert JournalSystem.Machine(I(s).js, I(s').js, JournalDisk.NoDiskOp, vop, jstep);
    assert JournalSystem.NextStep(I(s).js, I(s').js, vop, JournalSystem.MachineStep(JournalDisk.NoDiskOp, jstep));
    assert JournalSystem.Next(I(s).js, I(s').js, vop);

    assert BetreeCache.NextStep(I(s).bs.machine, I(s').bs.machine, BlockDisk.NoDiskOp, vop, BetreeCache.BlockCacheMoveStep(bstep));
    assert BetreeCache.Next(I(s).bs.machine, I(s').bs.machine, BlockDisk.NoDiskOp, vop);
    assert BetreeSystem.Machine(I(s).bs, I(s').bs, BlockDisk.NoDiskOp, vop);
    assert BetreeSystem.NextStep(I(s).bs, I(s').bs, vop, BetreeSystem.MachineStep(BlockDisk.NoDiskOp));
    assert BetreeSystem.Next(I(s).bs, I(s').bs, vop);

    assert BetreeJournalSystem.Next(I(s), I(s'), UI.NoOp);
    BetreeJournalSystem.NextPreservesInv(I(s), I(s'), UI.NoOp);
  }

  lemma ProcessWritePreservesInv(s: Variables, s': Variables, id: D.ReqId)
    requires Inv(s)
    requires s.machine == s'.machine
    requires D.ProcessWrite(s.disk, s'.disk, id)
    ensures BetreeJournalSystem.Next(I(s), I(s'), UI.NoOp)
    ensures Inv(s')
  {
    RefinesProcessWrite(s.disk, s'.disk, id);

    var vop := JournalInternalOp;
    var bstep := BC.NoOpStep;

    if IJournalDisk(s.disk) == IJournalDisk(s'.disk) {
      var jstep := JournalCache.NoOpStep;
      assert JournalSystem.Machine(I(s).js, I(s').js, JournalDisk.NoDiskOp, vop, jstep);
      assert JournalSystem.NextStep(I(s).js, I(s').js, vop, JournalSystem.MachineStep(JournalDisk.NoDiskOp, jstep));
      assert JournalSystem.Next(I(s).js, I(s').js, vop);
    } else {
      var which :| (which == 0 || which == 1) &&
        JournalDisk.ProcessWriteSuperblock(
          IJournalDisk(s.disk), IJournalDisk(s'.disk), which);
      var diskStep := JournalDisk.ProcessWriteSuperblockStep(which);
      assert JournalSystem.DiskInternal(I(s).js, I(s').js, diskStep, vop);
      assert JournalSystem.NextStep(I(s).js, I(s').js, vop, JournalSystem.DiskInternalStep(diskStep));
      assert JournalSystem.Next(I(s).js, I(s').js, vop);
    }

    assert BetreeCache.NextStep(I(s).bs.machine, I(s').bs.machine, BlockDisk.NoDiskOp, vop, BetreeCache.BlockCacheMoveStep(bstep));
    assert BetreeCache.Next(I(s).bs.machine, I(s').bs.machine, BlockDisk.NoDiskOp, vop);
    assert BetreeSystem.Machine(I(s).bs, I(s').bs, BlockDisk.NoDiskOp, vop);
    assert BetreeSystem.NextStep(I(s).bs, I(s').bs, vop, BetreeSystem.MachineStep(BlockDisk.NoDiskOp));
    assert BetreeSystem.Next(I(s).bs, I(s').bs, vop);

    assert BetreeJournalSystem.Next(I(s), I(s'), UI.NoOp);
    BetreeJournalSystem.NextPreservesInv(I(s), I(s'), UI.NoOp);
  }

  lemma DiskInternalStepPreservesInv(s: Variables, s': Variables, uiop: UIOp, step: D.InternalStep)
    requires Inv(s)
    requires DiskInternal(s, s', uiop, step)
    ensures BetreeJournalSystem.Next(I(s), I(s'), uiop)
    ensures Inv(s')
  {
    match step {
      case ProcessReadFailureStep(id, fakeContents) => ProcessReadFailurePreservesInv(s, s', id, fakeContents);
      case ProcessWriteStep(id) => ProcessWritePreservesInv(s, s', id);
      case HavocConflictingWritesStep(id, id') => RefinesHavocConflictingWrites(s.disk, s'.disk, id, id');
      case HavocConflictingWriteReadStep(id, id') => RefinesHavocConflictingWriteRead(s.disk, s'.disk, id, id');
    }
  }

  lemma CrashStepPreservesInv(s: Variables, s': Variables, uiop: UIOp)
    requires Inv(s)
    requires Crash(s, s', uiop)
    ensures BetreeJournalSystem.Next(I(s), I(s'), uiop)
    ensures Inv(s')
  {
    RefinesCrash(s.disk, s'.disk);

    var vop := StatesInternalOp;
    var jstep := JournalCache.NoOpStep;
    var bstep := BC.NoOpStep;

    assert JournalSystem.Crash(I(s).js, I(s').js, CrashOp);
    assert JournalSystem.NextStep(I(s).js, I(s').js, CrashOp, JournalSystem.CrashStep);
    assert JournalSystem.Next(I(s).js, I(s').js, CrashOp);

    assert BetreeSystem.Crash(I(s).bs, I(s').bs, CrashOp);
    assert BetreeSystem.NextStep(I(s).bs, I(s').bs, CrashOp, BetreeSystem.CrashStep);
    assert BetreeSystem.Next(I(s).bs, I(s').bs, CrashOp);

    assert BetreeJournalSystem.Next(I(s), I(s'), UI.CrashOp);
    BetreeJournalSystem.NextPreservesInv(I(s), I(s'), UI.CrashOp);

  }

  lemma NextStepPreservesInv(s: Variables, s': Variables, uiop: UIOp, step: Step)
    requires Inv(s)
    requires NextStep(s, s', uiop, step)
    ensures BetreeJournalSystem.Next(I(s), I(s'), uiop)
    ensures Inv(s')
  {
    match step {
      case MachineStep(dop) => MachineStepPreservesInv(s, s', uiop, dop);
      case DiskInternalStep(step) => DiskInternalStepPreservesInv(s, s', uiop, step);
      case CrashStep => CrashStepPreservesInv(s, s', uiop);
    }
  }

  lemma NextPreservesInv(s: Variables, s': Variables, uiop: UIOp)
    // Inherited from abstract module:
    //requires Inv(s)
    //requires Next(s, s', uiop)
    //ensures Inv(s')
  {
    var step :| NextStep(s, s', uiop, step);
    NextStepPreservesInv(s, s', uiop, step);
  }
}
