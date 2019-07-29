include "AsyncDiskModel.dfy"
include "ByteBetreeBlockCache.dfy"
include "BetreeBlockCacheSystem.dfy"

module ByteBetreeBlockCacheSystem refines AsyncDiskModel {
  import M = ByteBetreeBlockCache

  import opened NativeTypes
  import opened AsyncSectorDiskModelTypes
  import opened Maps
  import BC = BetreeGraphBlockCache
  import BBC = BetreeBlockCache
  import BBCS = BetreeBlockCacheSystem
  import SD = AsyncSectorDisk
  import LBAType`Internal

  function IDiskOp(diskOp: D.DiskOp) : SD.DiskOp<BBC.LBA, BBC.Sector>
  requires M.ValidDiskOp(diskOp)
  {
    M.IDiskOp(diskOp)
  }

  function IReqReads(reqReads: map<D.ReqId, D.ReqRead>) : map<SD.ReqId, SD.ReqRead<BBC.LBA>>
  requires forall id | id in reqReads :: M.ValidReqRead(reqReads[id])
  {
    map id | id in reqReads :: M.IReqRead(reqReads[id])
  }
  function IReqWrites(reqWrites: map<D.ReqId, D.ReqWrite>) : map<SD.ReqId, SD.ReqWrite<BBC.LBA, BBC.Sector>>
  requires forall id | id in reqWrites :: M.ValidReqWrite(reqWrites[id])
  {
    map id | id in reqWrites :: M.IReqWrite(reqWrites[id])
  }
  function IRespReads(respReads: map<D.ReqId, D.RespRead>) : map<SD.ReqId, SD.RespRead<BBC.Sector>>
  requires forall id | id in respReads :: M.ValidRespRead(respReads[id])
  {
    map id | id in respReads :: M.IRespRead(respReads[id])
  }
  function IRespWrites(respWrites: map<D.ReqId, D.RespWrite>) : map<SD.ReqId, SD.RespWrite>
  requires forall id | id in respWrites :: M.ValidRespWrite(respWrites[id])
  {
    map id | id in respWrites :: M.IRespWrite(respWrites[id])
  }

  predicate ValidDisk(disk: D.Variables)
  {
    && (forall id | id in disk.reqReads :: M.ValidReqRead(disk.reqReads[id]))
    && (forall id | id in disk.reqWrites :: M.ValidReqWrite(disk.reqWrites[id]))
    && (forall id | id in disk.respReads :: M.ValidRespRead(disk.respReads[id]))
    && (forall id | id in disk.respWrites :: M.ValidRespWrite(disk.respWrites[id]))
  }

  function IContents(contents: seq<byte>) : map<BBC.LBA, BBC.Sector>
  {
    map addr: uint64 |
      && M.ValidAddr(addr)
      && 0 <= addr
      && addr as int + M.BlockSize() <= |contents|
      && M.ValidBytes(contents[addr .. addr as int + M.BlockSize()])
    :: M.IBytes(contents[addr .. addr as int + M.BlockSize()])
  }

  function IDisk(disk: D.Variables) : SD.Variables<BBC.LBA, BBC.Sector>
  requires ValidDisk(disk)
  {
    SD.Variables(
        IReqReads(disk.reqReads),
        IReqWrites(disk.reqWrites),
        IRespReads(disk.respReads),
        IRespWrites(disk.respWrites),
        IContents(disk.contents))
  }

  function Ik(k: Constants) : BBCS.Constants
  {
    AsyncSectorDiskModelConstants(BC.Constants(), SD.Constants())
  }

  function I(k: Constants, s: Variables) : BBCS.Variables
  requires ValidDisk(s.disk)
  {
    AsyncSectorDiskModelVariables(s.machine, IDisk(s.disk))
  }

  predicate Init(k: Constants, s: Variables)
  {
    && ValidDisk(s.disk)
    && BBCS.Init(Ik(k), I(k, s))
  }

  predicate Inv(k: Constants, s: Variables)
  {
    && ValidDisk(s.disk)
    && BBCS.Inv(Ik(k), I(k, s))
  }

  lemma InitImpliesInv(k: Constants, s: Variables)
  {
    BBCS.InitImpliesInv(Ik(k), I(k, s));
  }

  lemma {:fuel BC.NextStep,0} {:fuel M.IBytes,0}
  DiskRecvReadStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  requires Inv(k, s)
  requires M.Next(k.machine, s.machine, s'.machine, uiop, dop)
  requires D.RecvRead(k.disk, s.disk, s'.disk, dop)
  ensures M.ValidDiskOp(dop)
  ensures ValidDisk(s'.disk)
  ensures SD.Next(Ik(k).disk, I(k,s).disk, I(k,s').disk, IDiskOp(dop))
  {
    assert SD.NextStep(Ik(k).disk, I(k,s).disk, I(k,s').disk, IDiskOp(dop), SD.RecvReadStep);
  }

  lemma {:fuel BC.NextStep,0} {:fuel M.IBytes,0}
  DiskRecvWriteStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  requires Inv(k, s)
  requires M.Next(k.machine, s.machine, s'.machine, uiop, dop)
  requires D.RecvWrite(k.disk, s.disk, s'.disk, dop)
  ensures M.ValidDiskOp(dop)
  ensures ValidDisk(s'.disk)
  ensures SD.Next(Ik(k).disk, I(k,s).disk, I(k,s').disk, IDiskOp(dop))
  {
    assert SD.NextStep(Ik(k).disk, I(k,s).disk, I(k,s').disk, IDiskOp(dop), SD.RecvWriteStep);
  }

  lemma {:fuel BC.NextStep,0} {:fuel M.IBytes,0}
  DiskAckReadStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  requires Inv(k, s)
  requires M.Next(k.machine, s.machine, s'.machine, uiop, dop)
  requires D.AckRead(k.disk, s.disk, s'.disk, dop)
  ensures M.ValidDiskOp(dop)
  ensures ValidDisk(s'.disk)
  ensures SD.Next(Ik(k).disk, I(k,s).disk, I(k,s').disk, IDiskOp(dop))
  {
    assert SD.NextStep(Ik(k).disk, I(k,s).disk, I(k,s').disk, IDiskOp(dop), SD.AckReadStep);
  }

  lemma {:fuel BC.NextStep,0} {:fuel M.IBytes,0}
  DiskAckWriteStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  requires Inv(k, s)
  requires M.Next(k.machine, s.machine, s'.machine, uiop, dop)
  requires D.AckWrite(k.disk, s.disk, s'.disk, dop)
  ensures M.ValidDiskOp(dop)
  ensures ValidDisk(s'.disk)
  ensures SD.Next(Ik(k).disk, I(k,s).disk, I(k,s').disk, IDiskOp(dop))
  {
    assert SD.NextStep(Ik(k).disk, I(k,s).disk, I(k,s').disk, IDiskOp(dop), SD.AckWriteStep);
  }

  lemma {:fuel BC.NextStep,0} {:fuel M.IBytes,0}
  DiskNextStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp, step: D.Step)
  requires Inv(k, s)
  requires M.Next(k.machine, s.machine, s'.machine, uiop, dop)
  requires D.NextStep(k.disk, s.disk, s'.disk, dop, step)
  ensures M.ValidDiskOp(dop)
  ensures ValidDisk(s'.disk)
  ensures SD.Next(Ik(k).disk, I(k,s).disk, I(k,s').disk, IDiskOp(dop))
  {
    match step {
      case RecvReadStep => DiskRecvReadStepRefines(k, s, s', uiop, dop);
      case RecvWriteStep => DiskRecvWriteStepRefines(k, s, s', uiop, dop);
      case AckReadStep => DiskAckReadStepRefines(k, s, s', uiop, dop);
      case AckWriteStep => DiskAckWriteStepRefines(k, s, s', uiop, dop);
      case StutterStep => {
        assert SD.NextStep(SD.Constants(), IDisk(s.disk), IDisk(s'.disk), IDiskOp(dop), SD.StutterStep);
      }
    }
  }

  lemma {:fuel BC.NextStep,0} {:fuel M.IBytes,0}
  DiskNextRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  requires Inv(k, s)
  requires M.Next(k.machine, s.machine, s'.machine, uiop, dop)
  requires D.Next(k.disk, s.disk, s'.disk, dop)
  ensures M.ValidDiskOp(dop)
  ensures ValidDisk(s'.disk)
  ensures SD.Next(Ik(k).disk, I(k,s).disk, I(k,s').disk, IDiskOp(dop))
  {
    var step :| D.NextStep(k.disk, s.disk, s'.disk, dop, step);
    DiskNextStepRefines(k, s, s', uiop, dop, step);
  }

  lemma {:fuel BC.NextStep,0} {:fuel M.IBytes,0}
  MachineStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  requires Inv(k, s)
  requires Machine(k, s, s', uiop, dop)
  ensures Inv(k, s')
  ensures BBCS.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    var step :| M.NextStep(k.machine, s.machine, s'.machine, uiop, dop, step);
    assert BBC.NextStep(k.machine, s.machine, s'.machine, uiop, IDiskOp(dop), step.step);
    assert Ik(k).machine == k.machine;
    assert I(k, s).machine == s.machine;
    assert I(k, s').machine == s'.machine;
    assert BBC.NextStep(Ik(k).machine, I(k, s).machine, I(k, s').machine, uiop, IDiskOp(dop), step.step);

    DiskNextRefines(k, s, s', uiop, dop);

    assert BBCS.Machine(Ik(k), I(k, s), I(k, s'), uiop, IDiskOp(dop));
    assert BBCS.NextStep(Ik(k), I(k, s), I(k, s'), uiop, BBCS.MachineStep(IDiskOp(dop)));
    BBCS.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
  }

  lemma {:fuel M.IBytes,0} {:fuel BC.Inv,0} {:fuel BC.WFIndirectionTable,0} {:fuel BC.WFCompleteIndirectionTable,0} {:fuel BC.GraphClosed,0}
  ProcessReadRefines(k: Constants, s: Variables, s': Variables, id: D.ReqId)
  requires Inv(k, s)
  requires D.ProcessRead(k.disk, s.disk, s'.disk, id)
  ensures ValidDisk(s'.disk)
  ensures SD.ProcessRead(Ik(k).disk, I(k, s).disk, I(k, s').disk, id)
  {
  }

  lemma SplicePreserves(bytes: seq<byte>, start: uint64, ins: seq<byte>, other: uint64)
  requires 0 <= start
  requires start as int + |ins| <= |bytes|
  requires 0 <= other
  requires other != start
  requires other as int + M.BlockSize() <= |bytes|
  requires M.ValidAddr(start)
  requires M.ValidAddr(other)
  requires |ins| == M.BlockSize()
  ensures |D.splice(bytes, start as int, ins)| == |bytes|
  ensures bytes[other .. other as int + M.BlockSize()]
      == D.splice(bytes, start as int, ins)[other .. other as int + M.BlockSize()]
  {
    D.reveal_splice();
    LBAType.reveal_ValidAddr();
    if (other < start) {
      assert other as int + M.BlockSize() <= start as int;
      assert D.splice(bytes, start as int, ins)[other .. other as int + M.BlockSize()]
          == bytes[.. start][other .. other as int + M.BlockSize()];

      assert bytes[.. start][other .. other as int + M.BlockSize()]
          == bytes[other .. other as int + M.BlockSize()];
    } else {
      var s := LBAType.ValidAddrDivisor(start);
      var o := LBAType.ValidAddrDivisor(other);
      assert o >= s + 1;
      assert other as int >= start as int + |ins|
          == |bytes[..start] + ins|;
      assert D.splice(bytes, start as int, ins)[other .. other as int + M.BlockSize()]
          == bytes[start as int + |ins| ..][other as int - |bytes[..start] + ins| .. other as int + M.BlockSize() - |bytes[..start] + ins|]
          == bytes[start as int + |ins| ..][other as int - (start as int + |ins|).. other as int + M.BlockSize() - (start as int + |ins|)]
          == bytes[other .. other as int + M.BlockSize()];

    }
  }

  lemma {:fuel M.IBytes,0}
  ProcessWriteRefines(k: Constants, s: Variables, s': Variables, id: D.ReqId)
  requires Inv(k, s)
  requires D.ProcessWrite(k.disk, s.disk, s'.disk, id)
  ensures ValidDisk(s'.disk)
  ensures SD.ProcessWrite(Ik(k).disk, I(k, s).disk, I(k, s').disk, id)
  {
    var req1 := s.disk.reqWrites[id];
    var bytes := req1.bytes;

    var req := I(k,s).disk.reqWrites[id];
    assert I(k,s').disk.reqWrites == MapRemove1(I(k,s).disk.reqWrites, id);
    assert I(k,s').disk.respWrites == I(k,s).disk.respWrites[id := SD.RespWrite];

    var b1 := I(k,s).disk.blocks[req.lba := req.sector];
    var b2 := I(k,s').disk.blocks;

    D.reveal_splice();
    assert 0 <= req.lba;
    assert req.lba as int + M.BlockSize() <= |s'.disk.contents|;
    assert req.lba == req1.addr;
    assert M.BlockSize() == |req1.bytes|;
    assert |s.disk.contents| == |s'.disk.contents|;

    forall lba:uint64 | lba in b1
    ensures lba in b2
    ensures b1[lba] == b2[lba]
    {
      if (lba == req.lba) {
        assert bytes
            == s'.disk.contents[lba .. lba as int + M.BlockSize()];
        assert lba in b2;
        assert b1[lba] == b2[lba];
      } else {
        SplicePreserves(s.disk.contents, req1.addr, req1.bytes, lba);
        assert s.disk.contents[lba .. lba as int + M.BlockSize()]
            == s'.disk.contents[lba .. lba as int + M.BlockSize()];
        assert lba in b2;
        assert b1[lba] == b2[lba];
      }
    }

    forall lba | lba in b2
    ensures lba in b1
    {
      if (lba == req.lba) {
        assert bytes
            == s'.disk.contents[lba .. lba as int + M.BlockSize()];
      } else {
        SplicePreserves(s.disk.contents, req1.addr, req1.bytes, lba);
      }
    }

    assert I(k,s').disk.blocks == I(k,s).disk.blocks[req.lba := req.sector];
  }

  lemma {:fuel BC.NextStep,0} {:fuel M.IBytes,0}
  DiskInternalStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp, internalStep: D.InternalStep)
  requires Inv(k, s)
  requires DiskInternal(k, s, s', uiop, internalStep)
  ensures Inv(k, s')
  ensures BBCS.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    match internalStep {
      case ProcessReadStep(id) => {
        ProcessReadRefines(k, s, s', id);
        BBCS.NextStepPreservesInv(Ik(k), I(k, s), I(k, s'), uiop, BBCS.DiskInternalStep(SD.ProcessReadStep(id)));
      }
      case ProcessWriteStep(id) => {
        ProcessWriteRefines(k, s, s', id);
        BBCS.NextStepPreservesInv(Ik(k), I(k, s), I(k, s'), uiop, BBCS.DiskInternalStep(SD.ProcessWriteStep(id)));
      }
    }
  }

  lemma {:fuel BC.NextStep,0} {:fuel M.IBytes,0}
  CrashStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  requires Inv(k, s)
  requires Crash(k, s, s', uiop)
  ensures Inv(k, s')
  ensures BBCS.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    BBCS.NextStepPreservesInv(Ik(k), I(k, s), I(k, s'), uiop, BBCS.CrashStep);
  }

  lemma {:fuel BC.NextStep,0} {:fuel M.IBytes,0}
  NextStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: Step)
  requires Inv(k, s)
  requires NextStep(k, s, s', uiop, step)
  ensures Inv(k, s')
  ensures BBCS.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    match step {
      case MachineStep(dop) => MachineStepRefines(k, s, s', uiop, dop);
      case DiskInternalStep(internalStep) => DiskInternalStepRefines(k, s, s', uiop, internalStep);
      case CrashStep => CrashStepRefines(k, s, s', uiop);
    }
    //assert ValidDisk(s'.disk);
    //BBCS.NextStepPreservesInv(Ik(k), I(k, s), I(k, s'), uiop, step);
  }

  lemma NextRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  requires Inv(k, s)
  requires Next(k, s, s', uiop)
  ensures Inv(k, s')
  ensures BBCS.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
    var step :| NextStep(k, s, s', uiop, step);
    NextStepRefines(k, s, s', uiop, step);
  }

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  {
    NextRefines(k, s, s', uiop);
  }
}
