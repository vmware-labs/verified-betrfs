include "IOSystem.s.dfy"
include "Program.i.dfy"

module VeribetrIOSystem refines IOSystem {
  import P = ProgramMachineMod
}

module Proof refines ProofObligations {
  import MapSpecMod
  import InterpMod
  import ConcreteSystem = VeribetrIOSystem

  function I(v: ConcreteSystem.Variables) : CrashTolerantMapSpecMod.Variables
  {
    if v.Running?
    then
      ProgramInterp.IM(v.program, v.disk)
        // requires v.Running?
    else
      ProgramInterp.INotRunning(v.disk)
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
