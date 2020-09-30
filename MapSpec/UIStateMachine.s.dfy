include "../MapSpec/UI.s.dfy"

abstract module UIStateMachine {
  import _UI = UI
  type UIOp = _UI.Op

  type Variables(!new)
  predicate Init(s: Variables)
  predicate Next(s: Variables, s': Variables, uiop: UIOp)

  predicate Inv(s: Variables)

  lemma InitImpliesInv(s: Variables)
  requires Init(s)
  ensures Inv(s)

  lemma NextPreservesInv(s: Variables, s': Variables, uiop: UIOp)
  requires Inv(s)
  requires Next(s, s', uiop)
  ensures Inv(s')
}
