include "../framework/StateMachines.s.dfy"

abstract module NRIfc refines InputOutputIfc {
  type NRState
  type UpdateOp
  type ReadonlyOp
  type ReturnType

  datatype UpdateResult = UpdateResult(new_state: NRState, return_value: ReturnType)

  function init_state() : NRState
  function update(s: NRState, op: UpdateOp) : UpdateResult
  function read(s: NRState, op: ReadonlyOp) : ReturnType

  /*
  method do_update(linear s: NRState, op: UpdateOp)
  returns (s' linear NRstate)
  ensures s' == update(s, op)
  */
}
