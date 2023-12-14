// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Spec/MapSpec.s.dfy"
include "../lib/Base/MapRemove.s.dfy"
include "../lib/Checksums/CRC32C.s.dfy"
include "AsyncDisk.s.dfy"
include "AsyncDiskProgram.s.dfy"
include "DiskTypes.s.dfy"


// The Specification for the entire IOSystem (Disk + Program)
abstract module IOSystem {
  import DiskTypesMod
  import D = AsyncDisk
  import P : AsyncDiskProgram
  import opened NativeTypes
  import AsyncMapSpecMod = CrashTolerantMapSpecMod.async

  type DiskOp = P.DiskOp
  datatype Variables = Variables(program: P.Variables, disk: D.Variables, requests: set<AsyncMapSpecMod.Request>, replies: set<AsyncMapSpecMod.Reply>)
  type UIOp = P.UIOp

  datatype Step =
    | MachineStep(dop: DiskOp)
    | DiskInternalStep(step: D.InternalStep)
    | CrashStep
    | AcceptRequestStep
    | DeliverReplyStep


  predicate AcceptRequest(s: Variables, s': Variables, uiop: UIOp)
  {
    && uiop.OperateOp?
    && uiop.baseOp.RequestOp?
    && s' == s.(requests := s.requests + {uiop.baseOp.req})
  }

  predicate DeliverReply(s: Variables, s': Variables, uiop: UIOp)
  {

    && uiop.OperateOp?
    && uiop.baseOp.ReplyOp?
    && uiop.baseOp.reply in s.replies
    && s' == s.(replies := s.replies - {uiop.baseOp.reply})
  }

  predicate Machine(s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  {
    && !uiop.CrashOp?
    && (
      if uiop.OperateOp? then
        && uiop.baseOp.ExecuteOp?
        && uiop.baseOp.req in s.requests
        && uiop.baseOp.req.id == uiop.baseOp.reply.id
        && s'.requests == s.requests - {uiop.baseOp.req}
        && s'.replies == s.replies + {uiop.baseOp.reply}
      else
        && s'.requests == s.requests
        && s'.replies == s.replies
      )
    && P.Next(s.program, s'.program, uiop, dop)
    && D.Next(s.disk, s'.disk, dop)

  }

  predicate DiskInternal(s: Variables, s': Variables, uiop: UIOp, step: D.InternalStep)
  {
    && uiop.NoopOp?
    && s.program == s'.program
    && D.NextInternalStep(s.disk, s'.disk, step)
    && s'.requests == s.requests
    && s'.replies == s.replies
  }

  predicate Crash(s: Variables, s': Variables, uiop: UIOp)
  {
    && uiop.CrashOp?
    && P.Init(s'.program)
    && D.Crash(s.disk, s'.disk)
    && s'.requests == {}
    && s'.replies == {}
  }

  predicate NextStep(s: Variables, s': Variables, uiop: UIOp, step: Step)
  {
    match step {
      case MachineStep(dop) => Machine(s, s', uiop, dop)
      case DiskInternalStep(step) => DiskInternal(s, s', uiop, step)
      case CrashStep => Crash(s, s', uiop)
      case AcceptRequestStep => AcceptRequest(s, s', uiop)
      case DeliverReplyStep => DeliverReply(s, s', uiop)
    }
  }

  predicate Init(v: Variables) {
    && P.Init(v.program)
    && var dv:DiskTypesMod.DiskView :| true; // TODO: AsyncDisk has wrong type!
    //&& P.Mkfs(v.disk.dv)
    && P.Mkfs(dv) // this init is only true once
  }

  predicate Next(s: Variables, s': Variables, uiop: UIOp) {
    exists step :: NextStep(s, s', uiop, step)
  }
}
