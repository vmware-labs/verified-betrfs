include "Interface.s.dfy"
include "Impl.i.dfy"
include "ShardedHashTable_Refines_AsyncMapSpec.i.dfy"

module FilledInInterface refines Interface(
  ShardedHashTable,
  ResourceStateMachine_Refines_AsyncMapSpec)
{
  import opened Impl
  import opened Limits
  import opened Mutexes

  type SharedVars = IVariables

  predicate SharedWF(s: SharedVars)
  {
    s.Inv(TicketStubSingletonLoc.loc())
  }

  method init(glinear in_token: T.Token)
  returns (linear s: SharedVars)
  //requires in_token.loc == TicketStubSingletonLoc.loc()
  //requires in_token.val == ssm.Init()
  ensures SharedWF(s)
  {
    glinear var token;

    token, s := Impl.init(in_token);
    
    T.dispose(token);
  }

  method do_operation(shared s: SharedVars,
      ghost rid: nat, input: MapIfc.Input, glinear ticket: T.Token)
  returns (output: MapIfc.Output, glinear stub: T.Token)
  //requires ticket.loc == TicketStubSingletonLoc.loc()
  //requires ticket.val == ssm.Ticket(rid, input)
  ensures stub.loc == TicketStubSingletonLoc.loc()
  ensures ssm.IsStub(rid, output, stub.val)
  decreases *
  {
    if input.InsertInput? {
      output, stub := doInsert(s, input, rid, ticket);
    } else if input.RemoveInput? {
      output, stub := doRemove(s, input, rid, ticket);
    } else {
      output, stub := doQuery(s, input, rid, ticket);
    }
  }
}
