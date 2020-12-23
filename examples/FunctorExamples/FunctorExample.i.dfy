abstract module TIfc {
  type TransitionLabel(==)
}

abstract module StateMachine(Ifc:TIfc) {
  type Vars(==, !new)
  predicate Init(s:Vars)
  predicate Next(s:Vars, s':Vars, transition:Ifc.TransitionLabel)
}

module IncrementIfc refines TIfc {
  datatype TransitionLabel = Inc(amt: int)
}

module IncrementSM refines StateMachine(IncrementIfc) {
  datatype Vars = Vars(v: int)
  import IncrementIfc
  predicate Init(s:Vars) {
    s.v == 0
  }
  predicate Next(s:Vars, s':Vars, transition:IncrementIfc.TransitionLabel) {
    s'.v == s.v + transition.amt
  }
}

abstract module StateMachinesRefine(L:StateMachine, H:StateMachine)
  requires L.Ifc == H.Ifc  // XXX not yet supported
{

  // Implementation must supply an interpretation function.
  function I(s:L.Vars) : H.Vars

  // Implementation provides an invariant to support induction.
  predicate Inv(s:L.Vars)

  lemma InterpPreservesInit(s:L.Vars)
      requires L.Init(s)
      ensures H.Init(I(s))

  lemma InvInit(s:L.Vars)
      requires L.Init(s)
      ensures Inv(s)

  lemma InvNext(s:L.Vars, s':L.Vars, transition:L.Ifc.TransitionLabel)
      requires Inv(s)
      requires L.Next(s, s', transition)
      ensures Inv(s')
      ensures H.Next(I(s), I(s'), transition)
}

abstract module StateMachinesRefineTransitive(LR:StateMachinesRefine, HR:StateMachinesRefine)
  refines StateMachinesRefine(LR.L, HR.H)
  requires LR.H == HR.L  // XXX not yet supported
{
  // Implementation must supply an interpretation function.
  function I(s:LR.L.Vars) : HR.H.Vars {
    HR.I(LR.I(s))
  }
}


