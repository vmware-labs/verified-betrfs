include "../../lib/Lang/NativeTypes.s.dfy"

module KeyValueType {
  import opened NativeTypes

  type Key = uint64
  type Value(==)

  datatype QueryResult = Found(val: Value) | NotFound
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
    | RemoveInput(key: Key)

  datatype Output =
    | QueryOutput(res: QueryResult)
    | InsertOutput
    | RemoveOutput
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

module MapSpec {
  import opened KeyValueType

  import Ifc = MapIfc
  datatype Variables = Variables(m: map<Key, Value>)

  predicate Init(s: Variables) {
    s.m == map[]
  }

  predicate Next(s: Variables, s': Variables, op: Ifc.Op) {
    match op {
      case Op(input, output) => (
        match input {
          case QueryInput(key) => 
            && s' == s
            && (key in s.m ==> output == Ifc.QueryOutput(Found(s.m[key])))
            && (key !in s.m ==> output == Ifc.QueryOutput(NotFound))
          case InsertInput(key, value) =>
            && s'.m == s.m[key := value]
            && output == Ifc.InsertOutput
        }
      )
    }
  }
}

module AsyncSpec {
  import InnerIfc = MapIfc
  import SM = MapSpec
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
