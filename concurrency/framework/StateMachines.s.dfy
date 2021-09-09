// Ifc, StateMachine

abstract module Ifc {
  type Op(!new)
}

abstract module StateMachine(ifc: Ifc) {
  type Variables(!new)
  predicate Init(s: Variables)
  predicate Next(s: Variables, s': Variables, op: ifc.Op)
}

// Async state machines

abstract module InputOutputIfc refines Ifc {
  type Input(!new)
  type Output(!new)

  datatype Op = Op(input: Input, output: Output)
}

module RequestIds {
  type RequestId = nat
}

module AsyncIfc(ifc: InputOutputIfc) refines Ifc {
  import opened RequestIds

  datatype Op =
    | Start(ghost rid: RequestId, input: ifc.Input)
    | End(ghost rid: RequestId, output: ifc.Output)
    | InternalOp
}

module AsyncStateMachine(IOIfc: InputOutputIfc, SM: StateMachine(IOIfc))
    refines StateMachine(AsyncIfc(IOIfc))
{
  import opened RequestIds

  datatype Variables = Variables(
      ghost s: SM.Variables,
      ghost reqs: map<RequestId, IOIfc.Input>,
      ghost resps: map<RequestId, IOIfc.Output>)

  predicate Init(s: Variables)
  {
    && SM.Init(s.s)
    && s.reqs == map[]
    && s.resps == map[]
  }

  predicate InteralNext(rid: RequestId, input: IOIfc.Input, output: IOIfc.Output, s: Variables, s': Variables)
  {
    && rid in s.reqs
    && s.reqs[rid] == input
    && s'.reqs == s.reqs - {rid}
    && s'.resps == s.resps[rid := output]
    && SM.Next(s.s, s'.s, IOIfc.Op(input, output))
  }

  predicate Next(s: Variables, s': Variables, op: ifc.Op)
  {
    match op {
      case Start(rid, input) =>
        // add 'input' to 'reqs'
        && s' == s.(reqs := s.reqs[rid := input])
        && rid !in s.reqs
      case InternalOp => (
        // stutter step
        || (s' == s)
        // resolve request step
        // serialization point: remove 'input' from 'reqs',
        // add 'output' to 'resps'
        || exists rid, input, output :: InteralNext(rid, input, output, s, s')
      )
      case End(rid, output) =>
        // remove from 'resps'
        && s == s'.(resps := s'.resps[rid := output])
        && rid !in s'.resps
    }
  }
}

abstract module Refinement(ifc: Ifc, A: StateMachine(ifc), B: StateMachine(ifc)) {
  predicate Inv(s: A.Variables)

  lemma InitImpliesInv(s: A.Variables)
  requires A.Init(s)
  ensures Inv(s)

  lemma NextPreservesInv(s: A.Variables, s': A.Variables, op: ifc.Op)
  requires Inv(s)
  requires A.Next(s, s', op)
  ensures Inv(s')

  function I(s: A.Variables) : B.Variables
  requires Inv(s)

  lemma InitRefinesInit(s: A.Variables)
  requires A.Init(s)
  requires Inv(s)
  ensures B.Init(I(s))

  lemma NextRefinesNext(s: A.Variables, s': A.Variables, op: ifc.Op)
  requires Inv(s)
  requires Inv(s')
  requires A.Next(s, s', op)
  ensures B.Next(I(s), I(s'), op)
}

/*abstract module IfcRefinement(ifc: Ifc, A: StateMachine(ifc), B: StateMachine(ifc)) {
  // Can be either a finite or infinite sequence
  codatatype Behavior<S, L> =
    | BState(s: S, l: L, b: Behavior<S, L>)
    | BEnd(s: S)


}*/
