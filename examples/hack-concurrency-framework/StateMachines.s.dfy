// Async state machines

module InputOutputIfc {
  type Input(!new)
  type Output(!new)

  datatype Op = Op(input: Input, output: Output)
}

module CookieIfc refines InputOutputIfc {
  datatype Input = Input(butter: nat, sugar: nat)
  datatype Output = Output(cookies: nat)
}


module AsyncIfc {
  import Ifc = CookieIfc
  type {:extern} RequestId(==,!new)

  datatype Op =
    | Start(rid: RequestId, input: Ifc.Input)
    | End(rid: RequestId, output: Ifc.Output)
    | InternalOp
}

/*
module AsyncSpec(InnerIfc: InputOutputIfc, SM: StateMachine(InnerIfc))
    refines StateMachine(AsyncIfc(InnerIfc))
{
  type Variables = Variables(
      s: SM.Variables,
      reqs: map<RequestId, InnerIfc.Input>,
      resps: map<RequestId, InnerIfc.Output>)

  predicate Init(s: Variables)
  {
    && SM.Init(s.s)
    && s.reqs == map[]
    && s.resps == map[]
  }

  predicate Next(s: Variables, s': Variables, op: Ifc.Op)
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
        || (exists rid, input, output ::
          && rid in s.reqs
          && s.reqs[rid] == input
          && s'.reqs == MapRemove1(s.reqs, rid)
          && s'.resps == s.resps[rid := output]
          && SM.Next(s.s, s'.s, Ifc.Op(input, output))
        )
      )
      case End(rid, output) =>
        // remove from 'resps'
        && s == s'.(resps := s'.resps[rid := output])
        && rid !in s'.resps
    }
  }
}
*/
