include "IOSystem.s.dfy"
include "Program.i.dfy"

module BetreeIOSystem refines IOSystem {
  import ProgramParam = ProgramMachineMod
}

module Proof refines ProofObligations {
  import MapSpecMod
  import InterpMod
  import ConcreteSystem = BetreeIOSystem

  function I(v: ConcreteSystem.Variables) : DeferredWriteMapSpecMod.Variables
  {
    var version0 := DeferredWriteMapSpecMod.Version(MapSpecMod.Variables(InterpMod.Empty()), /*syncReqs*/ {});
    DeferredWriteMapSpecMod.Variables([version0], 0)
  }

  predicate Inv(v: ConcreteSystem.Variables)
  {
    true
  }

  lemma InitRefines(v: ConcreteSystem.Variables)
//    ensures DeferredWriteMapSpecMod.Init(ConcreteSystem.I(v))
  {}

  lemma InvInductive(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables)
//    requires ConcreteSystem.Inv(v)
//    requires ConcreteSystem.Next(v, v')
//    ensures ConcreteSystem.Inv(v')
  {}

  lemma NextRefines(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables)
//    requires ConcreteSystem.Inv(v)
//    requires ConcreteSystem.Next(v, v')
//    ensures DeferredWriteMapSpecMod.Next(ConcreteSystem.I(v), ConcreteSystem.I(v'))
  {}
}

