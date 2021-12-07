include "Interface.s.dfy"
include "Impl.i.dfy"
include "HashTableRefinement.i.dfy"

module FilledInInterface refines Interface(
  HashTableStubSSM,
  HashTableRefinement)
{
  import opened Impl
  import opened CircularRange
  import opened Limits
  import opened GlinearMap

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
    linear var v: Variables;
    v, s := Impl.init(in_token);
    
    forall i: Index 
      ensures i !in v.handles
    {
      assert !v.HasRowHandle(i);
    }

    linear var Variables(
      token, handles) := v;

    glmap_delete(handles);
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
    glinear var fresh_handles := glmap_empty<Index, MutexHandle<Row>>();
    linear var v := Variables(ticket, fresh_handles);

    output := inout v.call(s, rid, input);

    forall i: Index 
      ensures i !in v.handles
    {
      assert !v.HasRowHandle(i);
    }

    linear var Variables(
      token, handles) := v;

    stub := token;
    
    glmap_delete(handles);
  }
}
