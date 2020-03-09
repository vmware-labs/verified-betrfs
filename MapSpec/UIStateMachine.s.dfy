include "../MapSpec/UI.s.dfy"

abstract module UIStateMachine {
  import _UI = UI
  type UIOp = _UI.Op

  type Constants(!new)
  type Variables(!new)
  predicate Init(k: Constants, s: Variables)
  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp)
}
