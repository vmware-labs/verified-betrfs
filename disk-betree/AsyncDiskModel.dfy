include "MapSpec.dfy"
include "CrashTypes.dfy"
include "../lib/Maps.dfy"

module AsyncDiskModelTypes {
  datatype AsyncDiskModelConstants<M,D> = AsyncDiskModelConstants(machine: M, disk: D)
  datatype AsyncDiskModelVariables<M,D> = AsyncDiskModelVariables(machine: M, disk: D)
}

module AsyncDisk {
  import opened NativeTypes
  import opened Maps

  type ReqId = uint64

  datatype ReqRead<LBA> = ReqRead(lba: LBA)
  datatype ReqWrite<LBA, Sector> = ReqWrite(lba: LBA, sector: Sector)
  datatype RespRead<Sector> = RespRead(sector: Sector)
  datatype RespWrite = RespWrite

  datatype DiskOp<LBA(==), Sector> =
    | ReqReadOp(id: ReqId, reqRead: ReqRead<LBA>)
    | ReqWriteOp(id: ReqId, reqWrite: ReqWrite<LBA, Sector>)
    | RespReadOp(id: ReqId, respRead: RespRead<Sector>)
    | RespWriteOp(id: ReqId, respWrite: RespWrite)
    | NoDiskOp

  datatype Constants = Constants()
  datatype Variables<LBA, Sector> = Variables(
    // Queue of requests and responses:
    reqReads: map<ReqId, ReqRead<LBA>>,
    reqWrites: map<ReqId, ReqWrite<LBA, Sector>>,
    respReads: map<ReqId, RespRead<Sector>>,
    respWrites: map<ReqId, RespWrite>,

    // The disk:
    blocks: map<LBA, Sector>
  )

  predicate Init(k: Constants, s: Variables)
  {
    && s.reqReads == map[]
    && s.reqWrites == map[]
    && s.respReads == map[]
    && s.respWrites == map[]
  }

  datatype Step =
    | RecvReadStep
    | RecvWriteStep
    | AckReadStep
    | AckWriteStep
    | StutterStep

  predicate RecvRead(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadOp?
    && dop.id !in s.reqReads
    && dop.id !in s.respReads
    && s' == s.(reqReads := s.reqReads[dop.id := dop.reqRead])
  }

  predicate RecvWrite(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteOp?
    && dop.id !in s.reqWrites
    && dop.id !in s.respWrites
    && s' == s.(reqWrites := s.reqWrites[dop.id := dop.reqWrite])
  }

  predicate AckRead(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadOp?
    && dop.id in s.respReads
    && s.respReads[dop.id] == dop.respRead
    && s' == s.(respReads := MapRemove1(s.respReads, dop.id))
  }

  predicate AckWrite(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteOp?
    && dop.id in s.respWrites
    && s.respWrites[dop.id] == dop.respWrite
    && s' == s.(respWrites := MapRemove1(s.respWrites, dop.id))
  }

  predicate Stutter(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.NoDiskOp?
    && s' == s
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, dop: DiskOp, step: Step) {
    match step {
      case RecvReadStep => RecvRead(k, s, s', dop)
      case RecvWriteStep => RecvWrite(k, s, s', dop)
      case AckReadStep => AckRead(k, s, s', dop)
      case AckWriteStep => AckWrite(k, s, s', dop)
      case StutterStep => Stutter(k, s, s', dop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, dop: DiskOp) {
    exists step :: NextStep(k, s, s', dop, step)
  }

  datatype InternalStep =
    | ProcessReadStep(id: ReqId)
    | ProcessWriteStep(id: ReqId)

  predicate ProcessRead(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqReads
    && var req := s.reqReads[id];
    && req.lba in s.blocks
    && s' == s.(reqReads := MapRemove1(s.reqReads, id))
              .(respReads := s.respReads[id := RespRead(s.blocks[req.lba])])
  }

  predicate ProcessWrite(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqWrites
    && var req := s.reqWrites[id];
    && s' == s.(reqWrites := MapRemove1(s.reqWrites, id))
              .(respWrites := s.respWrites[id := RespWrite])
              .(blocks := s.blocks[req.lba := req.sector])
  }

  predicate NextInternalStep(k: Constants, s: Variables, s': Variables, step: InternalStep)
  {
    match step {
      case ProcessReadStep(id) => ProcessRead(k, s, s', id)
      case ProcessWriteStep(id) => ProcessWrite(k, s, s', id)
    }
  }

  predicate NextInternal(k: Constants, s: Variables, s': Variables)
  {
    exists step :: NextInternalStep(k, s, s', step)
  }

  predicate Crash(k: Constants, s: Variables, s': Variables)
  {
    s' == Variables(map[], map[], map[], map[], s.blocks)
  }
}

abstract module AsyncDiskMachine {
  import D = AsyncDisk
  import UI

  type Variables
  type Constants
  type LBA(==)
  type Sector
  type UIOp = UI.Op

  type DiskOp = D.DiskOp<LBA, Sector>
  type ReqRead = D.ReqRead<LBA>
  type ReqWrite = D.ReqWrite<LBA, Sector>
  type RespRead = D.RespRead<Sector>
  type RespWrite = D.RespWrite

  predicate Init(k: Constants, s: Variables)
  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
}

abstract module AsyncDiskModel {
  import D = AsyncDisk
  import M : AsyncDiskMachine
  import CrashTypes
  import AsyncDiskModelTypes

  type DiskOp = M.DiskOp
  type Constants = AsyncDiskModelTypes.AsyncDiskModelConstants<M.Constants, D.Constants>
  type Variables = AsyncDiskModelTypes.AsyncDiskModelVariables<M.Variables, D.Variables<M.LBA, M.Sector>>
  type CrashableUIOp = CrashTypes.CrashableUIOp<M.UIOp>

  datatype Step =
    | MachineStep(dop: DiskOp)
    | DiskInternalStep(step: D.InternalStep)
    | CrashStep
  
  predicate Machine(k: Constants, s: Variables, s': Variables, uiop: CrashableUIOp, dop: DiskOp)
  {
    && uiop.NormalOp?
    && M.Next(k.machine, s.machine, s'.machine, uiop.uiop, dop)
    && D.Next(k.disk, s.disk, s'.disk, dop)
  }

  predicate DiskInternal(k: Constants, s: Variables, s': Variables, uiop: CrashableUIOp, step: D.InternalStep)
  {
    && uiop.NormalOp?
    && uiop.uiop.NoOp?
    && s.machine == s'.machine
    && D.NextInternalStep(k.disk, s.disk, s'.disk, step)
  }

  predicate Crash(k: Constants, s: Variables, s': Variables, uiop: CrashableUIOp)
  {
    && uiop.CrashOp?
    && M.Init(k.machine, s'.machine)
    && D.Crash(k.disk, s.disk, s'.disk)
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: CrashableUIOp, step: Step)
  {
    match step {
      case MachineStep(dop) => Machine(k, s, s', uiop, dop)
      case DiskInternalStep(step) => DiskInternal(k, s, s', uiop, step)
      case CrashStep => Crash(k, s, s', uiop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: CrashableUIOp) {
    exists step :: NextStep(k, s, s', uiop, step)
  }

  predicate Init(k: Constants, s: Variables)
  predicate Inv(k: Constants, s: Variables)

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: CrashableUIOp)
    requires Inv(k, s)
    requires Next(k, s, s', uiop)
    ensures Inv(k, s')
}
