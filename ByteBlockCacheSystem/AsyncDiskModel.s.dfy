include "../MapSpec/MapSpec.s.dfy"
include "../lib/Base/Maps.s.dfy"
include "../lib/Base/Crypto.s.dfy"
//
// An async disk allows concurrent outstanding I/Os. The disk is a sequence of bytes.
//
// (Real disks constrain I/Os to fall on logical-block-address boundaries, but we're
// ignoring constraint for now.)
//

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
  datatype RespRead = RespRead(addr: uint64, bytes: seq<byte>)
  datatype RespWrite = RespWrite(addr: uint64, len: uint64)

  datatype DiskOp =
    | ReqReadOp(id: ReqId, reqRead: ReqRead)
    | ReqWriteOp(id: ReqId, reqWrite: ReqWrite)
    | ReqWrite2Op(id1: ReqId, id2: ReqId,
        reqWrite1: ReqWrite, reqWrite2: ReqWrite)
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
    | RecvWrite2Step
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

  predicate RecvWrite2(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWrite2Op?
    && dop.id1 !in s.reqWrites
    && dop.id1 !in s.respWrites
    && dop.id2 !in s.reqWrites
    && dop.id2 !in s.respWrites
    && dop.id1 != dop.id2
    && s' == s.(reqWrites :=
        s.reqWrites[dop.id1 := dop.reqWrite1]
                   [dop.id2 := dop.reqWrite2]
       )
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
      case RecvWrite2Step => RecvWrite2(k, s, s', dop)
      case AckReadStep => AckRead(k, s, s', dop)
      case AckWriteStep => AckWrite(k, s, s', dop)
      case StutterStep => Stutter(k, s, s', dop)
    }
  }

  predicate Next(k: Constants, s: Variables, s': Variables, dop: DiskOp) {
    exists step :: NextStep(k, s, s', dop, step)
  }

  datatype InternalStep =
    //| ProcessReadStep(id: ReqId)
    | ProcessReadFailureStep(id: ReqId, fakeContents: seq<byte>)
    | ProcessWriteStep(id: ReqId)
    | HavocConflictingWritesStep(id: ReqId, id': ReqId)
    | HavocConflictingWriteReadStep(id: ReqId, id': ReqId)

  /*predicate ProcessRead(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqReads
    && var req := s.reqReads[id];
    && 0 <= req.addr as int <= req.addr as int + req.len as int <= |s.contents|
    && s' == s.(reqReads := MapRemove1(s.reqReads, id))
              .(respReads := s.respReads[id := RespRead(req.addr, s.contents[req.addr .. req.addr as int + req.len as int])])
  }*/

  predicate {:opaque} ChecksumChecksOut(s: seq<byte>) {
    && |s| >= 32
    && s[0..32] == Crypto.Crc32C(s[32..])
  }

  predicate ChecksumsCheckOutForSlice(realContents: seq<byte>, fakeContents: seq<byte>, i: int, j: int)
  requires |realContents| == |fakeContents|
  requires 0 <= i <= j <= |realContents|
  {
    // We make the assumption that the disk cannot fail from a checksum-correct state
    // to a different checksum-correct state. This is a reasonable assumption for many
    // probabilistic failure models of the disk.

    // We don't make a blanket assumption that !ChecksumChecksOut(fakeContents)
    // because it would be reasonable for a disk to fail into a checksum-correct state
    // from a checksum-incorrect one.

    ChecksumChecksOut(realContents[i..j]) && 
    ChecksumChecksOut(fakeContents[i..j]) ==>
        realContents[i..j] == fakeContents[i..j]
  }

  predicate AllChecksumsCheckOut(realContents: seq<byte>, fakeContents: seq<byte>)
  requires |realContents| == |fakeContents|
  {
    forall i, j | 0 <= i <= j <= |realContents| ::
      ChecksumsCheckOutForSlice(realContents, fakeContents, i, j)
  }

  predicate ProcessReadFailure(k: Constants, s: Variables, s': Variables, id: ReqId, fakeContents: seq<byte>)
  {
    && id in s.reqReads
    && var req := s.reqReads[id];
    && 0 <= req.addr as int <= req.addr as int + req.len as int <= |s.contents|
    && var realContents := s.contents[req.addr .. req.addr as int + req.len as int];
    && |fakeContents| == |realContents|
    && fakeContents != realContents

    && AllChecksumsCheckOut(realContents, fakeContents)

    && s' == s.(reqReads := MapRemove1(s.reqReads, id))
              .(respReads := s.respReads[id := RespRead(req.addr, fakeContents)])
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
    && |req.bytes| < 0x1_0000_0000_0000_0000
    && req.addr as int + |req.bytes| <= |s.contents|
    && s' == s.(reqWrites := MapRemove1(s.reqWrites, id))
              .(respWrites := s.respWrites[id := RespWrite(req.addr, |req.bytes| as uint64)])
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
      //case ProcessReadStep(id) => ProcessRead(k, s, s', id)
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

// Interface to the implementer-supplied program that is getting verified.
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

// TODO(jonh): Rename to a "System", because its job is to explain how a trusted disk interacts
// with some implementer-supplied program (Machine).
abstract module AsyncDiskModel {
  import D = AsyncDisk
  import M : AsyncDiskMachine
  import AsyncDiskModelTypes
  import opened NativeTypes

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

  predicate BlocksWrittenInByteSeq(
      contents: map<uint64, seq<byte>>,
      byteSeq: seq<byte>)
  {
    && (forall addr: uint64 | addr in contents ::
        && 0 <= addr as int <= |byteSeq|
        && addr as int + |contents[addr]| <= |byteSeq|
        && byteSeq[addr .. addr as int + |contents[addr]|] == contents[addr])
  }

  predicate BlocksDontIntersect(contents: map<uint64, seq<byte>>)
  {
    && (forall addr1, addr2 | addr1 in contents && addr2 in contents
        && addr1 != addr2 :: !D.overlap(addr1 as int, |contents[addr1]|, addr2 as int, |contents[addr2]|))
  }
}
