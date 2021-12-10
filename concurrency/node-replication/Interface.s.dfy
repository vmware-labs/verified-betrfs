include "NRSpec.s.dfy"
include "Linearize.s.dfy"
include "../framework/AsyncSSM.s.dfy"
include "../framework/StateMachines.s.dfy"
include "../../lib/Lang/LinearSequence.s.dfy"

abstract module NRInterface(
  nrifc: NRIfc,
  ssm: TicketStubSSM(nrifc),
  X: StateMachine(AsyncIfc(nrifc)),
  refinement: Refinement(
      AsyncIfc(nrifc),
      TicketStubStateMachine(nrifc, ssm),
      X)
  //refinement2: Linearizer(nrifc, X)
)
{
  import TicketStubSingletonLoc
  import PCM = TicketStubPCM(nrifc, ssm)
  import T = Tokens(PCM)
  import opened GhostLoc
  import opened LinearSequence_s
  import opened LinearMaybe

  type GlobalState
  type NodeState
  type ThreadState
  type NodeInitToken

  predicate WFGlobalState(gs: GlobalState)
  predicate WFNodeInitToken(nit: NodeInitToken, gs: GlobalState)
  predicate WFNode(node: NodeState, gs: GlobalState)
  predicate WFThread(t: ThreadState, node: NodeState, gs: GlobalState)

  method init(glinear in_token: T.Token)
  returns (linear gs: GlobalState, linear nodeCreationTokens: lseq<NodeInitToken>)
  requires in_token.loc == TicketStubSingletonLoc.loc()
  requires in_token.val == ssm.Init()
  ensures WFGlobalState(gs)
  ensures forall i | 0 <= i < |lseqs_raw(nodeCreationTokens)| ::
      lseq_has(nodeCreationTokens)[i]
        && WFNodeInitToken(read(lseqs_raw(nodeCreationTokens)[i]), gs)

  method initNode(shared gs: GlobalState, linear nit: NodeInitToken)
  returns (linear node: NodeState, linear threads: lseq<ThreadState>)
  requires WFGlobalState(gs)
  requires WFNodeInitToken(nit, gs)
  ensures WFGlobalState(gs)
  ensures forall i | 0 <= i < |lseqs_raw(threads)| ::
      lseq_has(threads)[i] && WFThread(read(lseqs_raw(threads)[i]), node, gs)

  method do_operation(shared gs: GlobalState, shared node: NodeState,
        linear inout t: ThreadState,
        ghost rid: nat, input: nrifc.Input, glinear ticket: T.Token)
  returns (output: nrifc.Output, glinear stub: T.Token)
  decreases *
  requires WFGlobalState(gs)
  requires WFNode(node, gs)
  requires WFThread(old_t, node, gs)
  requires ticket.loc == TicketStubSingletonLoc.loc()
  requires ticket.val == ssm.Ticket(rid, input)
  ensures WFThread(t, node, gs)
  ensures stub.loc == TicketStubSingletonLoc.loc()
  ensures ssm.IsStub(rid, output, stub.val)
}
