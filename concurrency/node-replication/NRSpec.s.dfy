include "../framework/StateMachines.s.dfy"

abstract module NRIfc refines InputOutputIfc {
  type NRState
  type UpdateOp
  type ReadonlyOp
  type ReturnType

  function update(s: NRState, op: UpdateOp) : (NRState, ReturnType)
  function read(s: NRState, op: ReadonlyOp) : ReturnType

  /*
  method do_update(linear s: NRState, op: UpdateOp)
  returns (s' linear NRstate)
  ensures s' == update(s, op)
  */
}
