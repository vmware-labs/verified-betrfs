include "../hashtable/MapSpec.s.dfy"
include "../framework/AsyncSSM.s.dfy"
include "../framework/StateMachines.s.dfy"

abstract module Interface(
  ssm: TicketStubSSM(MapIfc),
  refinement: Refinement(
      AsyncIfc(MapIfc),
      TicketStubStateMachine(MapIfc, ssm),
      AsyncStateMachineWithMultisets(MapIfc, MapSpec)
  )
)
{
  import TicketStubSingletonLoc
  import PCM = TicketStubPCM(MapIfc, ssm)
  import T = Tokens(PCM)
  import MapIfc
  import opened GhostLoc

  type SharedVars

  predicate SharedWF(s: SharedVars)

  method init(glinear in_token: T.Token)
  returns (linear s: SharedVars)
  requires in_token.loc == TicketStubSingletonLoc.loc()
  requires in_token.val == ssm.Init()
  ensures SharedWF(s)

  method do_operation(shared s: SharedVars,
      ghost rid: nat, input: MapIfc.Input, glinear ticket: T.Token)
  returns (output: MapIfc.Output, glinear stub: T.Token)
  decreases *
  requires SharedWF(s)
  requires ticket.loc == TicketStubSingletonLoc.loc()
  requires ticket.val == ssm.Ticket(rid, input)
  ensures stub.loc == TicketStubSingletonLoc.loc()
  ensures ssm.IsStub(rid, output, stub.val)
  ensures SharedWF(s)
}
