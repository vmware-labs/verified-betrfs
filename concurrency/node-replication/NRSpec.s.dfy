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

  datatype Input =
    | ROp(readonly_op: ReadonlyOp)
    | UOp(update_op: UpdateOp)

  type Output = ReturnType

  method do_update(linear s: NRState, op: UpdateOp)
  returns (linear s': NRState, ret: ReturnType)
  ensures UpdateResult(s', ret) == update(s, op)

  method do_readonly(shared s: NRState, op: ReadonlyOp)
  returns (ret: ReturnType)
  ensures ret == read(s, op)
}

module NR(nrifc: NRIfc) refines StateMachine(nrifc)
{
  datatype Variables = Variables(state: nrifc.NRState)

  predicate Next(s: Variables, s': Variables, op: ifc.Op) {
    match op {
      case Op(ROp(readonly_op), ret) =>
        && s' == s
        && ret == nrifc.read(s.state, readonly_op)
      case Op(UOp(update_op), ret) =>
        && nrifc.update(s.state, update_op) == nrifc.UpdateResult(s'.state, ret)
    }
  }
}
