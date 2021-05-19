include "AppSpec.s.dfy"

module AsyncIfc {
  import Ifc = MapIfc
    // PLACEHOLDER for not having module application. Would be prettier to
    // describe asyncrony and plug in the particular ifc/spec at the end.

  //type {:extern} RequestId(==,!new)
  type RequestId = int

  datatype Op =
    | Start(rid: RequestId, input: Ifc.Input)
    | End(rid: RequestId, output: Ifc.Output)
    | InternalOp
}

module AsyncSpec {
  // TODO module system sucks: would prefer to define this thing,
  // then instantiate it later with AsyncSpec(MapSpec)
  import InnerIfc = MapIfc
  import SM = MapSpec
    // PLACEHOLDER for not having module application. Would be prettier to
    // describe asyncrony and plug in the particular ifc/spec at the end.

  import Ifc = AsyncIfc

  type RequestId = Ifc.RequestId

  datatype Req = Req(rid: RequestId, input: InnerIfc.Input)
  datatype Resp = Resp(rid: RequestId, output: InnerIfc.Output)

  datatype Variables = Variables(
      s: SM.Variables,
      reqs: multiset<Req>,
      resps: multiset<Resp>)

  predicate Init(s: Variables)
  {
    && SM.Init(s.s)
    && s.reqs == multiset{}
    && s.resps == multiset{}
  }

  predicate LinearizationPoint(s: Variables, s': Variables,
      rid: RequestId, input: InnerIfc.Input, output: InnerIfc.Output)
  {
    // resolve request step
    // serialization point: remove 'input' from 'reqs',
    // add 'output' to 'resps'
    && Req(rid, input) in s.reqs
    && s.reqs == s'.reqs + multiset{Req(rid, input)}
    && s'.resps == s.resps + multiset{Resp(rid, output)}
    && SM.Next(s.s, s'.s, InnerIfc.Op(input, output))
  }

  predicate Next(s: Variables, s': Variables, op: Ifc.Op)
  {
    match op {
      case Start(rid, input) =>
        // add 'input' to 'reqs'
        && s' == s.(reqs := s.reqs + multiset{Req(rid, input)})
      case InternalOp => (
        // stutter step
        || (s' == s)

        // resolve request step
        || (exists rid, input, output ::
          LinearizationPoint(s, s', rid, input, output)
        )
      )
      case End(rid, output) =>
        // remove from 'resps'
        && Resp(rid, output) in s.resps
        && s' == s.(resps := s.resps - multiset{Resp(rid, output)})
    }
  }
}
