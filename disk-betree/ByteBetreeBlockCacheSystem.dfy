include "AsyncDiskModel.dfy"
include "ByteBetreeBlockCache.dfy"
include "BetreeBlockCacheSystem.dfy"

module ByteBetreeBlockCacheSystem refines AsyncDiskModel {
  import M = ByteBetreeBlockCache

  import opened NativeTypes
  import opened AsyncSectorDiskModelTypes
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
  MachineStepRefines(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  requires Inv(k, s)
  requires Machine(k, s, s', uiop, dop)
  ensures Inv(k, s')
  ensures BBCS.Next(Ik(k), I(k, s), I(k, s'), uiop)
  {
  }

  lemma {:fuel M.IBytes,0}
  ProcessReadRefines(k: Constants, s: Variables, s': Variables, id: D.ReqId)
  requires Inv(k, s)
  requires D.ProcessRead(k.disk, s.disk, s'.disk, id)
  ensures ValidDisk(s'.disk)
  ensures SD.ProcessRead(Ik(k).disk, I(k, s).disk, I(k, s').disk, id)
  {
    var req := s.disk.reqReads[id];
    assert req.addr in IContents(s.disk.contents);
    //assert s.disk.contents[req.addr .. req.addr as int + req.len as int] ==
     //   IContents(s.disk.contents)[req.addr];
    assert M.ValidBytes(s.disk.contents[req.addr .. req.addr as int + req.len as int]);
    assert M.ValidRespRead(D.RespRead(s.disk.contents[req.addr .. req.addr as int + req.len as int]));
    forall id | id in s'.disk.respReads
    ensures M.ValidRespRead(s'.disk.respReads[id])
    {
    }
  }

  lemma {:fuel M.IBytes,0}
  ProcessWriteRefines(k: Constants, s: Variables, s': Variables, id: D.ReqId)
  requires Inv(k, s)
  requires D.ProcessWrite(k.disk, s.disk, s'.disk, id)
  ensures ValidDisk(s'.disk)
  ensures SD.ProcessWrite(Ik(k).disk, I(k, s).disk, I(k, s').disk, id)

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

  /*
  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  {
    BBCS.NextPreservesInv(Ik(k), I(k, s), I(k, s'), uiop);
  }
  */
}
