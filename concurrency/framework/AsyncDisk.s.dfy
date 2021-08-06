include "../../lib/Lang/NativeTypes.s.dfy"
include "StateMachines.s.dfy"

module DiskIfc refines Ifc {
  import opened NativeTypes
  import opened RequestIds

  type Block = s : seq<byte> | |s| == 4096
    witness seq(4096, (i) => 0)

  datatype ReqRead = ReqRead(addr: nat)
  datatype ReqWrite = ReqWrite(addr: nat, data: Block)
  datatype RespRead = RespRead(addr: nat, data: Block)
  datatype RespWrite = RespWrite(addr: nat)

  datatype DiskOp =
    | ReqReadOp(id: RequestId, reqRead: ReqRead)
    | ReqWriteOp(id: RequestId, reqWrite: ReqWrite)
    | RespReadOp(id: RequestId, respRead: RespRead)
    | RespWriteOp(id: RequestId, respWrite: RespWrite)

  type Op = DiskOp
}

module AsyncDisk refines StateMachine(DiskIfc) {
  import opened NativeTypes
  import opened DiskIfc
  import opened RequestIds

  datatype Variables = Variables(
    // Queue of requests and responses:
    reqReads: map<RequestId, ReqRead>,
    reqWrites: map<RequestId, ReqWrite>,
    respReads: map<RequestId, RespRead>,
    respWrites: map<RequestId, RespWrite>,

    // The disk:
    contents: map<nat, Block>
  )

  predicate Init(s: Variables)
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

  predicate RecvRead(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqReadOp?
    && dop.id !in s.reqReads
    && dop.id !in s.respReads
    && s' == s.(reqReads := s.reqReads[dop.id := dop.reqRead])
  }

  predicate RecvWrite(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWriteOp?
    && dop.id !in s.reqWrites
    && dop.id !in s.respWrites
    && s' == s.(reqWrites := s.reqWrites[dop.id := dop.reqWrite])
  }

  predicate AckRead(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespReadOp?
    && dop.id in s.respReads
    && s.respReads[dop.id] == dop.respRead
    && s' == s.(respReads := s.respReads - {dop.id})
  }

  predicate AckWrite(s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.RespWriteOp?
    && dop.id in s.respWrites
    && s.respWrites[dop.id] == dop.respWrite
    && s' == s.(respWrites := s.respWrites - {dop.id})
  }

  predicate NextStep(s: Variables, s': Variables, dop: DiskOp, step: Step) {
    match step {
      case RecvReadStep => RecvRead(s, s', dop)
      case RecvWriteStep => RecvWrite(s, s', dop)
      case AckReadStep => AckRead(s, s', dop)
      case AckWriteStep => AckWrite(s, s', dop)
    }
  }

  predicate Next(s: Variables, s': Variables, op: ifc.Op) {
    exists step :: NextStep(s, s', op, step)
  }

  datatype InternalStep =
    | ProcessReadStep(id: RequestId)
    | ProcessWriteStep(id: RequestId)
    | HavocConflictingWritesStep(id: RequestId, id': RequestId)
    | HavocConflictingWriteReadStep(id: RequestId, id': RequestId)

  predicate ProcessRead(s: Variables, s': Variables, id: RequestId)
  {
    && id in s.reqReads
    && var req := s.reqReads[id];
    && req.addr in s.contents
    && s' == s.(reqReads := s.reqReads - {id})
              .(respReads := s.respReads[id := RespRead(req.addr, s.contents[req.addr])])
  }

  predicate ProcessWrite(s: Variables, s': Variables, id: RequestId)
  {
    && id in s.reqWrites
    && var req := s.reqWrites[id];
    && s' == s.(reqWrites := s.reqWrites - {id})
              .(respWrites := s.respWrites[id := RespWrite(req.addr)])
              .(contents := s.contents[req.addr := req.data])
  }

  // We assume the disk makes ABSOLUTELY NO GUARANTEES about what happens
  // when there are conflicting reads or writes.

  predicate HavocConflictingWrites(s: Variables, s': Variables, id: RequestId, id': RequestId)
  {
    && id != id'
    && id in s.reqWrites
    && id' in s.reqWrites
    && s.reqWrites[id].addr == s.reqWrites[id'].addr
  }

  predicate HavocConflictingWriteRead(s: Variables, s': Variables, id: RequestId, id': RequestId)
  {
    && id in s.reqWrites
    && id' in s.reqReads
    && s.reqWrites[id].addr == s.reqReads[id'].addr
  }

  predicate NextInternalStep(s: Variables, s': Variables, step: InternalStep)
  {
    match step {
      case ProcessReadStep(id) => ProcessRead(s, s', id)
      case ProcessWriteStep(id) => ProcessWrite(s, s', id)
      case HavocConflictingWritesStep(id, id') => HavocConflictingWrites(s, s', id, id')
      case HavocConflictingWriteReadStep(id, id') => HavocConflictingWriteRead(s, s', id, id')
    }
  }

  predicate NextInternal(s: Variables, s': Variables)
  {
    exists step :: NextInternalStep(s, s', step)
  }

  predicate Crash(s: Variables, s': Variables)
  {
    s' == Variables(map[], map[], map[], map[], s.contents)
  }
}
