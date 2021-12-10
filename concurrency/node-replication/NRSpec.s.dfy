include "../framework/StateMachines.s.dfy"

abstract module NRIfc refines InputOutputIfc {
  type NRState(!new,0)
  type UpdateOp(!new,0,00)
  type ReadonlyOp(!new,0,00)
  type ReturnType(!new,0,00)

  datatype UpdateResult = UpdateResult(new_state: NRState, return_value: ReturnType)

  function init_state() : NRState
  function update(s: NRState, op: UpdateOp) : UpdateResult
  function read(s: NRState, op: ReadonlyOp) : ReturnType

  datatype Input =
    | ROp(readonly_op: ReadonlyOp)
    | UOp(update_op: UpdateOp)

  type Output = ReturnType

  // Implementation stuff:

  type DataStructureType(!new)
  function I(ds: DataStructureType) : NRState

  method initialize()
  returns (linear s: DataStructureType)
  ensures I(s) == init_state()

  method do_update(linear s: DataStructureType, op: UpdateOp)
  returns (linear s': DataStructureType, ret: ReturnType)
  ensures UpdateResult(I(s'), ret) == update(I(s), op)

  method do_readonly(shared s: DataStructureType, op: ReadonlyOp)
  returns (ret: ReturnType)
  ensures ret == read(I(s), op)
}

module NROne(nrifc: NRIfc) refines StateMachine(nrifc) {
  type Variables = nrifc.NRState

  predicate Init(s: Variables) { s == nrifc.init_state() }

  predicate Next(s: Variables, s': Variables, op: ifc.Op) {
    match op.input {
      case ROp(readonly_op) =>
        && op.output == nrifc.read(s, readonly_op)
        && s' == s
      case UOp(update_op) =>
        && nrifc.update(s, update_op) == nrifc.UpdateResult(s', op.output)
    }
  }
}
