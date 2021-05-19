include "Allocation.i.dfy"
include "StateMachine.s.dfy"
include "Spec.s.dfy"

module Disk {
  import opened AllocationMod
  datatype Variables = Variables(dv: DiskView)

  predicate Init(v: Variables)
  {
    true  // TODO fill in
  }
}

abstract module IOSystem {
  import Disk
  import ProgramParam : StateMachine // abstract import -- to be filled in by final theorem

  datatype Variables = Variables(
    program: ProgramParam.Variables,
    disk: Disk.Variables)

  predicate Init(v: Variables)
  {
    && Disk.Mkfs(v.disk)
    && ProgramParam.Init(v.program)
  }

  predicate Crash(v: Variables, v': Variables)
  {
    && v'.disk == v.disk
    // TODO cancel in-flight I/Os -- when we add disk asynchrony
    && ProgramParam.Init(v.program)
  }

  predicate Normal(v: Variables, v': Variables, diskOps: DiskOps)
  {
    && Disk.Next(v, v', diskOps)
    && ProgramParam.Next(v, v', diskOps)
  }

  datatype Step = CrashStep | NormalStep(diskOps: DiskOps)

  predicate NextStep(v: Variables, v': Variables, step: Step)
  {
    match step {
      CrashStep => Crash(v, v')
      NormalStep(diskOps) => Normal(v, v', diskOps)
    }
  }

  predicate Next(v: Variables, v': Variables)
  {
    exists step :: NextStep(v, v', step)
  }
}

abstract module ProofObligations {
  import DeferredWriteMapSpecMod
  import ConcreteSystem : IOSystem

  // Your interpretation function
  function I(v: ConcreteSystem.Variables) : DeferredWriteMapSpecMod.Variables

  // Your system invariant
  predicate Inv(v: ConcreteSystem.Variables)

  lemma InitRefines(v: ConcreteSystem.Variables)
    ensures DeferredWriteMapSpecMod.Init(I(v))

  lemma InvInductive(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables)
    requires Inv(v)
    requires ConcreteSystem.Next(v, v')
    ensures Inv(v')

  lemma NextRefines(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables)
    requires Inv(v)
    requires ConcreteSystem.Next(v, v')
    ensures DeferredWriteMapSpecMod.Next(I(v), I(v'))
}
