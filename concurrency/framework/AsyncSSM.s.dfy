include "PCM.s.dfy"
include "StateMachines.s.dfy"

abstract module TicketStubSSM(IOIfc: InputOutputIfc) {
  import opened RequestIds

  type M(!new)

  function dot(x: M, y: M) : M
  function unit() : M

  function Ticket(rid: RequestId, input: IOIfc.Input) : M
  function Stub(rid: RequestId, output: IOIfc.Output) : M

  // By returning a set of request ids "in use", we enforce that
  // there are only a finite number of them (i.e., it is always possible to find
  // a free one).
  function request_ids_in_use(m: M) : set<RequestId>

  predicate Init(s: M)
  predicate Internal(shard: M, shard': M)

  predicate NewTicket(whole: M, whole': M, rid: RequestId, input: IOIfc.Input) {
    && rid !in request_ids_in_use(whole)
    && whole' == dot(whole, Ticket(rid, input))
  }

  predicate ConsumeStub(whole: M, whole': M, rid: RequestId, output: IOIfc.Output) {
    && whole == dot(whole', Stub(rid, output))
  }

  predicate Inv(s: M)

  lemma InitImpliesInv(s: M)
  requires Init(s)
  ensures Inv(s)

  lemma InternalPreservesInv(shard: M, shard': M, rest: M)
  requires Inv(dot(shard, rest))
  requires Internal(shard, shard')
  ensures Inv(dot(shard', rest))

  lemma NewTicketPreservesInv(whole: M, whole': M, rid: RequestId, input: IOIfc.Input)
  requires Inv(whole)
  requires NewTicket(whole, whole', rid, input)
  ensures Inv(whole')

  lemma ConsumeStubPreservesInv(whole: M, whole': M, rid: RequestId, output: IOIfc.Output)
  requires Inv(whole)
  requires ConsumeStub(whole, whole', rid, output)
  ensures Inv(whole')

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x

  lemma commutative(x: M, y: M)
  ensures dot(x, y) == dot(y, x)

  lemma associative(x: M, y: M, z: M)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)

  lemma exists_inv_state()
  returns (s: M)
  ensures Inv(s)
}

module TicketStubStateMachine(IOIfc: InputOutputIfc, ssm: TicketStubSSM(IOIfc))
    refines StateMachine(AsyncIfc(IOIfc))
{
  import AsyncIfc = AsyncIfc(IOIfc)

  type Variables = ssm.M

  predicate Init(s: Variables) {
    ssm.Init(s)
  }

  predicate InternalNext(s: Variables, s': Variables,
      shard: Variables, shard': Variables, rest: Variables)
  {
    && s == ssm.dot(shard, rest)
    && s' == ssm.dot(shard', rest)
    && ssm.Internal(shard, shard')
  }

  predicate Next(s: Variables, s': Variables, op: ifc.Op) {
    match op {
      case Start(rid, input) => ssm.NewTicket(s, s', rid, input)
      case End(rid, output) => ssm.ConsumeStub(s, s', rid, output)
      case InternalOp =>
        exists shard, shard', rest :: InternalNext(s, s', shard, shard', rest)
    }
  }
}

module Obligations(
    IOIfc: InputOutputIfc,
    ssm: TicketStubSSM(IOIfc),
    spec: StateMachine(IOIfc),
    ref: Refinement(
          AsyncIfc(IOIfc),
          TicketStubStateMachine(IOIfc, ssm),
          AsyncStateMachine(IOIfc, spec)
       )
  )
{ }
