include "IOSystem.s.dfy"
include "ProgramInterp.i.dfy"

module VeribetrIOSystem refines IOSystem {
  import P = ProgramMachineMod
}

module Proof refines ProofObligations {
  import AllocationMod
  import MapSpecMod
  import InterpMod
  import ProgramInterpMod
  import ConcreteSystem = VeribetrIOSystem

  function I(v: ConcreteSystem.Variables) : CrashTolerantMapSpecMod.Variables
  {
    if v.program.phase.Running?
    then
      // TODO this is borked because somehow ProgramInterpMod magically has the whole disk
      ProgramInterpMod.IM(v.program /*, v.disk*/)
        // requires Running?
    else
      var disk:AllocationMod.DiskView :| true;
      // TODO v.disk is AsyncDisk's seq<byte>, which we need to change to map<CU,...>.
      ProgramInterpMod.INotRunning(disk)
  }

  predicate Inv(v: ConcreteSystem.Variables)
  {
    true
  }

  lemma InitRefines(v: ConcreteSystem.Variables)
//    ensures CrashTolerantMapSpecMod.Init(ConcreteSystem.I(v))
  {}

  lemma InvInductive(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp)
//    requires ConcreteSystem.Inv(v)
//    requires ConcreteSystem.Next(v, v')
//    ensures ConcreteSystem.Inv(v')
  {}

  lemma NextRefines(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp)
//    requires ConcreteSystem.Inv(v)
//    requires ConcreteSystem.Next(v, v')
//    ensures CrashTolerantMapSpecMod.Next(ConcreteSystem.I(v), ConcreteSystem.I(v'))
  {}
}
