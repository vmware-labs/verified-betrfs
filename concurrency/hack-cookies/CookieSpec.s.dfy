include "../hack-concurrency-framework/StateMachines.s.dfy"
include "../../lib/Base/Maps.i.dfy"

// disallowed:

// thread 1 : 4 butter, 2 sugar
// thread 2 : 2 butter, 4 sugar

// thread 1 : 3 batches returned
// thread 2 : 3 batches returned

module CookieSpec {
  import Ifc = CookieIfc
  datatype Variables = Variables(butter: nat, sugar: nat)

  predicate Init(s: Variables) {
    && s.butter == 0
    && s.sugar == 0
  }

  predicate Next(s: Variables, s': Variables, op: Ifc.Op) {
    match op {
      case Op(input, output) => (
        exists num_batches: nat ::
          && num_batches <= s.butter + input.butter
          && num_batches <= s.sugar + input.sugar
          && s'.butter == s.butter + input.butter - num_batches
          && s'.sugar == s.sugar + input.sugar - num_batches
          && output == Ifc.Output(6 * num_batches)
      )
    }
  }
}

module AsyncSpec {
  import opened Maps

  import InnerIfc = CookieIfc
  import SM = CookieSpec
  import Ifc = AsyncIfc

  type RequestId = Ifc.RequestId

  datatype Variables = Variables(
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
          && SM.Next(s.s, s'.s, InnerIfc.Op(input, output))
        )
      )
      case End(rid, output) =>
        // remove from 'resps'
        && s == s'.(resps := s'.resps[rid := output])
        && rid !in s'.resps
    }
  }
}
