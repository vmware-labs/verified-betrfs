abstract module TIfc {
  type TransitionLabel(==)
}

abstract module UIStateMachine(Ifc:TIfc) {
  type Vars(==, !new)
  predicate Init(s:Vars)
  predicate Next(s:Vars, s':Vars, transition:Ifc.TransitionLabel)
}

abstract module StateMachinesRefine(
    Ifc: TIfc,
    L:UIStateMachine(Ifc),
    H:UIStateMachine(Ifc)) {

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

  lemma InvNext(s:L.Vars, s':L.Vars, transition:Ifc.TransitionLabel)
      requires Inv(s)
      requires L.Next(s, s', transition)
      ensures Inv(s')
      ensures H.Next(I(s), I(s'), transition)
}
