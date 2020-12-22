abstract module UIfc {
  type UIOp(==)
}

abstract module UIStateMachine/*(Ifc:UIfc)*/ {
  import Ifc : UIfc

  type Vars(==, !new)
  predicate Init(s:Vars)
  predicate Next(s:Vars, s':Vars, uiop:Ifc.UIOp)
}

// The "unwinding condition" necessary to prove the TLA expression:
// L.Init && []L.Next ==> H.Init && []H.Next
abstract module StateMachinesRefine/*(Ifc: UIfc, L:UIStateMachine(Ifc), H:UIStateMachine(Ifc))*/ {
  import Ifc : UIfc

  // Error: module Ifc does not exist
//  module UIStateMachineIfc refines UIStateMachine {
//    import Ifc = Ifc
//  }
//  import L : UIStateMachineIfc
//  import H : UIStateMachineIfc

// Error: type mismatch for argument 2 (function expects Ifc.UIOp, got Ifc.UIOp)
// There are now three unbound Ifcs floating around, not one.
  import L : UIStateMachine
  import H : UIStateMachine

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

  lemma InvNext(s:L.Vars, s':L.Vars, uiop:Ifc.UIOp)
      requires Inv(s)
      requires L.Next(s, s', uiop)
      ensures Inv(s')
      ensures H.Next(I(s), I(s'), uiop)
}

