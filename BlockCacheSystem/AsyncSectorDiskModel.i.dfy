include "../MapSpec/MapSpec.s.dfy"
include "../lib/Base/Maps.s.dfy"
include "../PivotBetree/Bounds.i.dfy"
include "DiskLayout.i.dfy"
include "SectorType.i.dfy"

//
// An AsyncSectorDiskModel allows concurrent outstanding I/Os to a disk where each "sector"
// is some higher-level Node datatype. A later refinement step shows how to marshall and align
// these Nodes to the byte-ranges of the (trusted) AsyncDiskModel.
//
// TODO disallow concurrent spatially-overlapping writes/reads

module AsyncSectorDiskModelTypes {
  datatype AsyncSectorDiskModelConstants<M,D> = AsyncSectorDiskModelConstants(machine: M, disk: D)
  datatype AsyncSectorDiskModelVariables<M,D> = AsyncSectorDiskModelVariables(machine: M, disk: D)
}

// A disk, processing stuff in its queue, doing its thing.
module AsyncSectorDisk {
  import opened NativeTypes
  import opened Maps
  import opened Options
  import opened DiskLayout
  import opened SectorType
  import opened JournalRanges

  type ReqId = uint64

  datatype ReqRead = ReqRead(loc: Location)
  datatype ReqWrite = ReqWrite(loc: Location, sector: Sector)
  datatype RespRead = RespRead(sector: Option<Sector>)
  datatype RespWrite = RespWrite

  datatype DiskOp =
    | ReqReadOp(id: ReqId, reqRead: ReqRead)
    | ReqWriteOp(id: ReqId, reqWrite: ReqWrite)
    | ReqWrite2Op(id1: ReqId, id2: ReqId,
        reqWrite1: ReqWrite,
        reqWrite2: ReqWrite)
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
    blocks: imap<Location, Sector>
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

  predicate RecvWrite2(k: Constants, s: Variables, s': Variables, dop: DiskOp)
  {
    && dop.ReqWrite2Op?
    && dop.id1 !in s.reqWrites
    && dop.id1 !in s.respWrites
    && dop.id2 !in s.reqWrites
    && dop.id2 !in s.respWrites
    && dop.id1 != dop.id2
    && s' == s.(reqWrites := s.reqWrites[dop.id1 := dop.reqWrite1]
                                        [dop.id2 := dop.reqWrite2])
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
    | ProcessReadFailureStep(id: ReqId)
    | ProcessWriteStep(id: ReqId)

  predicate ProcessRead(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqReads
    && var req := s.reqReads[id];
    && s' == s.(reqReads := MapRemove1(s.reqReads, id))
              .(respReads := s.respReads[id := RespRead(ImapLookupOption(s.blocks, req.loc))])
  }

  predicate ProcessReadFailure(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqReads
    && var req := s.reqReads[id];
    && s' == s.(reqReads := MapRemove1(s.reqReads, id))
              .(respReads := s.respReads[id := RespRead(None)])
  }

  predicate ClosedUnderLogConcatenationLocs(
      blocks: imap<Location, Sector>,
      loc1: Location,
      loc2: Location,
      loc3: Location)
  {
    && loc1 in blocks
    && loc2 in blocks
    && blocks[loc1].SectorJournal?
    && blocks[loc2].SectorJournal?
    && loc2.addr as int == loc1.addr as int + loc1.len as int
    && loc3.addr == loc1.addr
    && loc3.len as int == loc1.len as int + loc2.len as int
        ==> (
          && loc3 in blocks
          && blocks[loc3] == SectorJournal(JournalRangeConcat(
              blocks[loc1].journal, blocks[loc2].journal))
        )
  }

  predicate ClosedUnderLogConcatenation(blocks: imap<Location, Sector>)
  {
    forall loc1, loc2, loc3 ::
        ClosedUnderLogConcatenationLocs(blocks, loc1, loc2, loc3)
  }

  predicate ProcessWrite(k: Constants, s: Variables, s': Variables, id: ReqId)
  {
    && id in s.reqWrites
    && var req := s.reqWrites[id];
    && s' == s.(reqWrites := MapRemove1(s.reqWrites, id))
              .(respWrites := s.respWrites[id := RespWrite])
              .(blocks := s'.blocks)

    // It would be easier to say s'.blocks == s.blocks[req.loc := req.sector]
    // but to make the refinement from AsyncDiskModel easier, we only require that
    // the map preserves every location not intersecting the given region. We don't
    // have to say anything about potential intervals which could intersect this one.
    && req.loc in s'.blocks
    && s'.blocks[req.loc] == req.sector
    && (forall loc | loc in s.blocks && !overlap(loc, req.loc) :: loc in s'.blocks && s'.blocks[loc] == s.blocks[loc])
    && ClosedUnderLogConcatenation(s'.blocks)
  }

  predicate NextInternalStep(k: Constants, s: Variables, s': Variables, step: InternalStep)
  {
    match step {
      case ProcessReadStep(id) => ProcessRead(k, s, s', id)
      case ProcessReadFailureStep(id) => ProcessReadFailure(k, s, s', id)
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

abstract module AsyncSectorDiskMachine {
  import D = AsyncSectorDisk
  import UI

  type Variables
  type Constants
  type Location(==)
  type Sector
  type UIOp = UI.Op

  type DiskOp = D.DiskOp
  type ReqRead = D.ReqRead
  type ReqWrite = D.ReqWrite
  type RespRead = D.RespRead
  type RespWrite = D.RespWrite

  predicate Init(k: Constants, s: Variables)
  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
}

// A disk attached to a program ("Machine"), modeling the nondeterministic crashes that reset the
// program. Designed to look like the AsyncDiskModel, which we want to show refines to this.
// TODO(jonh): Rename this to a "System"?
abstract module AsyncSectorDiskModel {
  import D = AsyncSectorDisk
  import M : AsyncSectorDiskMachine
  import AsyncSectorDiskModelTypes
  import opened SectorType

  type DiskOp = M.DiskOp
  type Constants = AsyncSectorDiskModelTypes.AsyncSectorDiskModelConstants<M.Constants, D.Constants>
  type Variables = AsyncSectorDiskModelTypes.AsyncSectorDiskModelVariables<M.Variables, D.Variables>
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
