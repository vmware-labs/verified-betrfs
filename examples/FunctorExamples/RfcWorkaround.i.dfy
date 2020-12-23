abstract module TIfc {
  type TransitionLabel(==)
}
abstract module UIStateMachine {
  import Ifc : TIfc
  type Vars(==, !new)
  predicate Init(s:Vars)
  predicate Next(s:Vars, s':Vars, transition:Ifc.TransitionLabel)
}

abstract module UIParam refines TIfc {}

abstract module LParam refines UIStateMachine {
  import UIParam
  import Ifc = UIParam
}

abstract module HParam refines UIStateMachine {
  import UIParam
  import Ifc = UIParam
}

abstract module StateMachinesRefine
{
  import L : LParam
  import H : HParam

  function I(s:L.Vars) : H.Vars
  predicate Inv(s:L.Vars)
  /* ... */
  lemma InvNext(s:L.Vars, s':L.Vars, transition:L.Ifc.TransitionLabel)
      requires Inv(s)
      requires L.Next(s, s', transition)
      ensures Inv(s')
      ensures H.Next(I(s), I(s'), transition)
}
