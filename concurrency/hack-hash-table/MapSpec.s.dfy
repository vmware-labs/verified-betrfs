module KeyValueType {
  type Key = uint64
  type Value(==)
}

module InputOutputIfc {
  type Input(!new)
  type Output(!new)

  datatype Op = Op(input: Input, output: Output)
}

module MapIfc refines InputOutputIfc {
  import opened KeyValueType

  datatype Input =
    | QueryInput(key: Key)
    | InsertInput(key: Key, value: Value)

  datatype Output =
    | QueryOutput(value: Value)
    | InsertOutput
}

module AsyncIfc {
  import Ifc = MapIfc
  type {:extern} RequestId(==,!new)

  datatype Op =
    | Start(rid: RequestId, input: Ifc.Input)
    | End(rid: RequestId, output: Ifc.Output)
    | InternalOp
}

// disallowed:

// thread 1 : 4 butter, 2 sugar
// thread 2 : 2 butter, 4 sugar

// thread 1 : 3 batches returned
// thread 2 : 3 batches returned

module MapSpec {
  import Ifc = MapIfc
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
  import InnerIfc = CookieIfc
  import SM = CookieSpec
  import Ifc = AsyncIfc

  type RequestId = Ifc.RequestId

  datatype Req = Req(rid: RequestId, input: InnerIfc.Input)
  datatype Resp = Req(rid: RequestId, input: InnerIfc.Input)

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
        // serialization point: remove 'input' from 'reqs',
        // add 'output' to 'resps'
        || (exists rid, input, output ::
          && Req(rid, input) in s.reqs
          && s'.reqs == s.reqs - multiset{Req(rid, input)}
          && s'.resps == s.resps + multiset{Resp(rid, output)}
          && SM.Next(s.s, s'.s, InnerIfc.Op(input, output))
        )
      )
      case End(rid, output) =>
        // remove from 'resps'
        && Resp(rid, output) in s.resps
        && s' == s.(resps := s'.resps - multiset{Resp(rid, output)})
    }
  }
}
