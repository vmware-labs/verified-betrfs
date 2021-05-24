// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Spec.s.dfy"
include "../lib/Base/MapRemove.s.dfy"
include "../lib/Checksums/CRC32C.s.dfy"
include "AsyncDisk.s.dfy"
include "AsyncDiskProgram.s.dfy"

// The Specification for the entire IOSystem (Disk + Program)
abstract module IOSystem {
  import D = AsyncDisk
  import P : AsyncDiskProgram
  import opened NativeTypes

  type DiskOp = P.DiskOp
  datatype Variables = Variables(program: P.Variables, disk: D.Variables)
  type UIOp = P.UIOp

  datatype Step =
    | MachineStep(dop: DiskOp)
    | DiskInternalStep(step: D.InternalStep)
    | CrashStep

  predicate Machine(s: Variables, s': Variables, uiop: UIOp, dop: DiskOp)
  {
    && P.Next(s.program, s'.program, uiop, dop)
    && D.Next(s.disk, s'.disk, dop)
  }

  predicate DiskInternal(s: Variables, s': Variables, uiop: UIOp, step: D.InternalStep)
  {
    && uiop.NoopOp?
    && s.program == s'.program
    && D.NextInternalStep(s.disk, s'.disk, step)
  }

  predicate Crash(s: Variables, s': Variables, uiop: UIOp)
  {
    && uiop.CrashOp?
    && P.Init(s'.program)
    && D.Crash(s.disk, s'.disk)
  }

  predicate NextStep(s: Variables, s': Variables, uiop: UIOp, step: Step)
  {
    match step {
      case MachineStep(dop) => Machine(s, s', uiop, dop)
      case DiskInternalStep(step) => DiskInternal(s, s', uiop, step)
      case CrashStep => Crash(s, s', uiop)
    }
  }

  predicate Next(s: Variables, s': Variables, uiop: UIOp) {
    exists step :: NextStep(s, s', uiop, step)
  }

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

abstract module ProofObligations {
  import CrashTolerantMapSpecMod
  import ConcreteSystem : IOSystem

  // Your interpretation function
  function I(v: ConcreteSystem.Variables) : CrashTolerantMapSpecMod.Variables

  // Your system invariant
  predicate Inv(v: ConcreteSystem.Variables)

  lemma InitRefines(v: ConcreteSystem.Variables)
    ensures CrashTolerantMapSpecMod.Init(I(v))

  lemma InvInductive(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp)
    requires Inv(v)
    requires ConcreteSystem.Next(v, v', uiop)
    ensures Inv(v')

  lemma NextRefines(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp)
    requires Inv(v)
    requires ConcreteSystem.Next(v, v', uiop)
    ensures CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop)
}
