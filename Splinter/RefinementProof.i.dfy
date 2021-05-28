include "IOSystem.s.dfy"
include "ProgramInterp.i.dfy"
include "ProofObligations.s.dfy"

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
    ProgramInterpMod.IM(v.program)
  }

  predicate Inv(v: ConcreteSystem.Variables)
  {
    true
  }

  lemma InitRefines(v: ConcreteSystem.Variables)
//    requires ConcreteSystem.Init(v)
    ensures CrashTolerantMapSpecMod.Init(I(v))
  {
    //assert !v.program.phase.Running?;
    //var sb := ProgramInterpMod.ISuperblock(v.program.cache.dv);
    //assert !sb.Some?;
    //assert I(v) == CrashTolerantMapSpecMod.Empty();
  }

  lemma InvInductive(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp)
//    requires ConcreteSystem.Inv(v)
//    requires ConcreteSystem.Next(v, v')
//    ensures ConcreteSystem.Inv(v')
  {}

  lemma NextRefines(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp)
//    requires ConcreteSystem.Inv(v)
//    requires ConcreteSystem.Next(v, v')
//    ensures CrashTolerantMapSpecMod.Next(ConcreteSystem.I(v), ConcreteSystem.I(v'))
  {

  }
}
