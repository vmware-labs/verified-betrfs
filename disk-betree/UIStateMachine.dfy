include "UI.dfy"

abstract module UIStateMachine {
  import UI
  type UIOp = UI.Op

  type Constants
  type Variables
  predicate Init(k: Constants, s: Variables)
  predicate Next(k: Constants, s: Variables, s': Variables, uiop: UIOp)
}
