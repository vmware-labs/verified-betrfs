include "../framework/StateMachines.s.dfy"
include "NRSpec.s.dfy"

module Behavior(ifc: Ifc, sm: StateMachine(ifc)) {
  datatype Behavior =
    | Stepped(s: sm.Variables, op: sm.ifc.Op, tail: Behavior)
    | Inited(s: sm.Variables)
  {
    predicate WF() {
      match this {
        case Stepped(s', op, tail) =>
          && tail.WF()
          && sm.Next(tail.s, s', op)
        case Inited(s) =>
          && sm.Init(s)
      }
    }
  }
}

abstract module Linearizer(nrifc: NRIfc, simple: StateMachine(AsyncIfc(nrifc))) {
  import one = AsyncStateMachine(nrifc, NROne(nrifc))

  import SimpleB = Behavior(AsyncIfc(nrifc), simple)
  import OneB = Behavior(AsyncIfc(nrifc), AsyncStateMachine(nrifc, NROne(nrifc)))

  predicate equiv(a: SimpleB.Behavior, b: OneB.Behavior)
  decreases a, b
  {
    || (a.Inited? && b.Inited?)
    || (a.Stepped? && a.op.InternalOp? && equiv(a.tail, b))
    || (b.Stepped? && b.op.InternalOp? && equiv(a, b.tail))
    || (a.Stepped? && b.Stepped? && a.op == b.op && equiv(a.tail, b.tail))
  }

  lemma ExistsEquivBehavior(a: SimpleB.Behavior)
  returns (b: OneB.Behavior)
  requires a.WF()
  ensures b.WF()
  ensures equiv(a, b)
}
