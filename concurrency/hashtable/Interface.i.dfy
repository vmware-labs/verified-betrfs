include "Interface.s.dfy"
include "Impl.i.dfy"
include "HashTableRefinement.i.dfy"

module FilledInInterface refines Interface(
  HashTableStubSSM,
  HashTableRefinement)
{
  import opened Impl

  type SharedVars = IVariables

  predicate SharedWF(s: SharedVars)

  method init(glinear in_token: T.Token)
  returns (linear s: SharedVars)
  //requires in_token.loc == TicketStubSingletonLoc.loc()
  //requires in_token.val == ssm.Init()
  ensures SharedWF(s)

  method do_operation(shared s: SharedVars,
      ghost rid: nat, input: MapIfc.Input, glinear ticket: T.Token)
  returns (output: MapIfc.Output, glinear stub: T.Token)
  //requires ticket.loc == TicketStubSingletonLoc.loc()
  //requires ticket.val == ssm.Ticket(rid, input)
  ensures stub.loc == TicketStubSingletonLoc.loc()
  ensures ssm.IsStub(rid, output, stub.val)
}
