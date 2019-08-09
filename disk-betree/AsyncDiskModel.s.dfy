include "MapSpec.s.dfy"
include "../lib/Maps.s.dfy"
include "../lib/Crypto.s.dfy"

module AsyncDiskModelTypes {
  datatype AsyncDiskModelConstants<M,D> = AsyncDiskModelConstants(machine: M, disk: D)
  datatype AsyncDiskModelVariables<M,D> = AsyncDiskModelVariables(machine: M, disk: D)
}

module AsyncDisk {
  import opened NativeTypes
  import opened Maps
  import Crypto

  type ReqId = uint64

  datatype ReqRead = ReqRead(addr: uint64, len: uint64)
  datatype ReqWrite = ReqWrite(addr: uint64, bytes: seq<byte>)
  datatype RespRead = RespRead(bytes: seq<byte>)
  datatype RespWrite = RespWrite

  datatype DiskOp =
    | ReqReadOp(id: ReqId, reqRead: ReqRead)
    | ReqWriteOp(id: ReqId, reqWrite: ReqWrite)
    | RespReadOp(id: ReqId, respRead: RespRead)
    | RespWriteOp(id: ReqId, respWrite: RespWrite)
    | NoDiskOp

  datatype Constants = Constants()
  datatype Variables = Variables(
    // Queue of requests and responses:
    reqReads: map<ReqId, ReqRead>,
    reqWrites: map<ReqId, ReqWrite>,
    respReads: map<ReqId, RespRead>,
    respWrites: map<ReqId, RespWrite>,

    // The disk:
    contents: seq<byte>
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
    | ProcessReadFailureStep(id: ReqId, fakeContents: seq<byte>)
    | ProcessWriteStep(id: ReqId)
    | HavocConflictingWritesStep(id: ReqId, id': ReqId)
    | HavocConflictingWriteReadStep(id: ReqId, id': ReqId)

  predicate ProcessRead(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqReads
    && var req := s.reqReads[id];
    && 0 <= req.addr as int <= req.addr as int + req.len as int <= |s.contents|
    && s' == s.(reqReads := MapRemove1(s.reqReads, id))
              .(respReads := s.respReads[id := RespRead(s.contents[req.addr .. req.addr as int + req.len as int])])
  }

  predicate {:opaque} ChecksumChecksOut(s: seq<byte>) {
    && |s| >= 32
    && s[0..32] == Crypto.Sha256(s[32..])
  }

  predicate ProcessReadFailure(k: Constants, s: Variables, s': Variables, id: ReqId, fakeContents: seq<byte>)
  {
    && id in s.reqReads
    && var req := s.reqReads[id];
    && 0 <= req.addr as int <= req.addr as int + req.len as int <= |s.contents|
    && var realContents := s.contents[req.addr .. req.addr as int + req.len as int];
    && |fakeContents| == |realContents|

    // We make the assumption that the disk cannot fail from a checksum-correct state
    // to a different checksum-correct state. This is a reasonable assumption for many
    // probabilistic failure models of the disk.

    // We don't make a blanket assumption that !ChecksumChecksOut(fakeContents)
    // because it would be reasonable for a disk to fail into a checksum-correct state
    // from a checksum-incorrect one.

    && (ChecksumChecksOut(realContents) ==> !ChecksumChecksOut(fakeContents))

    && s' == s.(reqReads := MapRemove1(s.reqReads, id))
              .(respReads := s.respReads[id := RespRead(fakeContents)])
  }

  function {:opaque} splice(bytes: seq<byte>, start: int, ins: seq<byte>) : seq<byte>
  requires 0 <= start
  requires start + |ins| <= |bytes|
  {
    bytes[.. start] + ins + bytes[start + |ins| ..]
  }

  predicate ProcessWrite(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqWrites
    && var req := s.reqWrites[id];
    && 0 <= req.addr
    && req.addr as int + |req.bytes| <= |s.contents|
    && s' == s.(reqWrites := MapRemove1(s.reqWrites, id))
              .(respWrites := s.respWrites[id := RespWrite])
              .(contents := splice(s.contents, req.addr as int, req.bytes))
  }

  // We assume the disk makes ABSOLUTELY NO GUARANTEES about what happens
  // when there are conflicting reads or writes.

  predicate overlap(start: int, len: int, start': int, len': int)
  {
    && start + len > start'
    && start' + len' > start
  }

  predicate HavocConflictingWrites(k: Constants, s: Variables, s': Variables, id: ReqId, id': ReqId)
  {
    && id != id'
    && id in s.reqWrites
    && id' in s.reqWrites
    && overlap(
        s.reqWrites[id].addr as int, |s.reqWrites[id].bytes|,
        s.reqWrites[id'].addr as int, |s.reqWrites[id'].bytes|)
  }

  predicate HavocConflictingWriteRead(k: Constants, s: Variables, s': Variables, id: ReqId, id': ReqId)
  {
    && id in s.reqWrites
    && id' in s.reqReads
    && overlap(
        s.reqWrites[id].addr as int, |s.reqWrites[id].bytes|,
        s.reqReads[id'].addr as int, s.reqReads[id'].len as int)
  }

  predicate NextInternalStep(k: Constants, s: Variables, s': Variables, step: InternalStep)
  {
    match step {
      case ProcessReadStep(id) => ProcessRead(k, s, s', id)
      case ProcessReadFailureStep(id, fakeContents) => ProcessReadFailure(k, s, s', id, fakeContents)
      case ProcessWriteStep(id) => ProcessWrite(k, s, s', id)
      case HavocConflictingWritesStep(id, id') => HavocConflictingWrites(k, s, s', id, id')
      case HavocConflictingWriteReadStep(id, id') => HavocConflictingWriteRead(k, s, s', id, id')
    }
  }

  predicate NextInternal(k: Constants, s: Variables, s': Variables)
  {
    exists step :: NextInternalStep(k, s, s', step)
  }

  predicate Crash(k: Constants, s: Variables, s': Variables)
  {
    s' == Variables(map[], map[], map[], map[], s.contents)
  }
}

abstract module AsyncDiskMachine {
  import D = AsyncDisk
  import UI

  type Variables
  type Constants
  type UIOp = UI.Op

  type DiskOp = D.DiskOp
  type ReqRead = D.ReqRead
  type ReqWrite = D.ReqWrite
  type RespRead = D.RespRead
  type RespWrite = D.RespWrite

  predicate Init(k: Constants, s: Variables)
  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
}

abstract module AsyncDiskModel {
  import D = AsyncDisk
  import M : AsyncDiskMachine
  import AsyncDiskModelTypes

  type DiskOp = M.DiskOp
  type Constants = AsyncDiskModelTypes.AsyncDiskModelConstants<M.Constants, D.Constants>
  type Variables = AsyncDiskModelTypes.AsyncDiskModelVariables<M.Variables, D.Variables>
  type UIOp = M.UIOp

  datatype Step =
    | MachineStep(dop: DiskOp)
    | DiskInternalStep(step: D.InternalStep)
    | CrashStep
  
  predicate Machine(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  {
    && M.Next(k.machine, s.machine, s'.machine, uiop, dop)
    && D.Next(k.disk, s.disk, s'.disk, dop)
  }

  predicate DiskInternal(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: D.InternalStep)
  {
    && uiop.NoOp?
    && s.machine == s'.machine
    && D.NextInternalStep(k.disk, s.disk, s'.disk, step)
  }

  predicate Crash(k: Constants, s: Variables, s': Variables, uiop: UIOp)
  {
    && uiop.CrashOp?
    && M.Init(k.machine, s'.machine)
    && D.Crash(k.disk, s.disk, s'.disk)
  }

  predicate NextStep(k: Constants, s: Variables, s': Variables, uiop: UIOp, step: Step)
  {
    match step {
      case MachineStep(dop) => Machine(k, s, s', uiop, dop)
      case DiskInternalStep(step) => DiskInternal(k, s, s', uiop, step)
      case CrashStep => Crash(k, s, s', uiop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp) {
    exists step :: NextStep(k, s, s', uiop, step)
  }

  predicate Init(k: Constants, s: Variables)
  predicate Inv(k: Constants, s: Variables)

  lemma InitImpliesInv(k: Constants, s: Variables)
    requires Init(k, s)
    ensures Inv(k, s)

  lemma NextPreservesInv(k: Constants, s: Variables, s': Variables, uiop: UIOp)
    requires Inv(k, s)
    requires Next(k, s, s', uiop)
    ensures Inv(k, s')
}
