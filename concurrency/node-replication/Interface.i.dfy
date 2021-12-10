include "Interface.s.dfy"
include "Init.i.dfy"
include "InfiniteLog_Refines_NRSimple.i.dfy"
include "Linearize.i.dfy"

module FilledInInterface(nifc: NRIfc)
  refines Interface(
    nifc,
    InfiniteLogSSM(nifc),
    NRSimple(nifc),
    InfiniteLog_Refines_NRSimple(nifc)
    //NRSimple_Refines_NRSingle(nifc) // XXX module system bug?
  )
{
  import Impl = NRImpl(nifc)
  import Init = Init(nifc)
  import ILT = InfiniteLogTokens(nifc)
  import IL = InfiniteLogSSM(nifc)
  import opened LinearSequence_i`T

  type GlobalState = Impl.NR
  type NodeState = Impl.Node
  type ThreadState = Impl.ThreadOwnedContext
  type NodeInitToken = Init.NodeCreationToken

  predicate WFGlobalState(gs: GlobalState) {
    gs.WF()
  }

  predicate WFNodeInitToken(nit: NodeInitToken, gs: GlobalState) {
    nit.WF(gs)
  }

  predicate WFNode(node: NodeState, gs: GlobalState) {
    node.WF(gs)
  }

  predicate WFThread(t: ThreadState, node: NodeState, gs: GlobalState) {
    t.WF(node, gs)
  }

  method init(glinear in_token: T.Token)
  returns (linear gs: GlobalState, linear nodeCreationTokens: lseq<NodeInitToken>)
  //requires in_token.loc == TicketStubSingletonLoc.loc()
  //requires in_token.val == ssm.Init()
  ensures WFGlobalState(gs)
  ensures forall i | 0 <= i < |lseqs_raw(nodeCreationTokens)| ::
      lseq_has(nodeCreationTokens)[i]
        && WFNodeInitToken(read(lseqs_raw(nodeCreationTokens)[i]), gs)
  {
    gs, nodeCreationTokens := Init.initNR(in_token);
    forall i | 0 <= i < |lseqs_raw(nodeCreationTokens)|
        ensures lseq_has(nodeCreationTokens)[i]
          && WFNodeInitToken(read(lseqs_raw(nodeCreationTokens)[i]), gs)
    {
      assert read(lseqs_raw(nodeCreationTokens)[i]) == nodeCreationTokens[i];
      assert nodeCreationTokens[i].WF(gs);
      assert read(lseqs_raw(nodeCreationTokens)[i]).WF(gs);
    }
  }

  method initNode(shared gs: GlobalState, linear nit: NodeInitToken)
  returns (linear node: NodeState, linear threads: lseq<ThreadState>)
  //requires WFGlobalState(gs)
  //requires WFNodeInitToken(nit, gs)
  ensures WFGlobalState(gs)
  ensures forall i | 0 <= i < |lseqs_raw(threads)| ::
      lseq_has(threads)[i] && WFThread(read(lseqs_raw(threads)[i]), node, gs)
  {
    node, threads := Init.initNode(gs, nit);
    forall i | 0 <= i < |lseqs_raw(threads)|
    ensures lseq_has(threads)[i] && WFThread(read(lseqs_raw(threads)[i]), node, gs)
    {
      assert threads[i].WF(node, gs);
    }
  }

  method do_operation(shared gs: GlobalState, shared node: NodeState,
        linear inout t: ThreadState,
        ghost rid: nat, input: nrifc.Input, glinear ticket: T.Token)
  returns (output: nrifc.Output, glinear stub: T.Token)
  decreases *
  /*requires WFGlobalState(gs)
  requires WFNode(node, gs)
  requires WFThread(old_t, node, gs)
  requires ticket.loc == TicketStubSingletonLoc.loc()
  requires ticket.val == ssm.Ticket(rid, input)*/
  ensures WFThread(t, node, gs)
  ensures stub.loc == TicketStubSingletonLoc.loc()
  ensures ssm.IsStub(rid, output, stub.val)
  {
    match input {
      case ROp(rop) => {
        glinear var folded_stub;
        glinear var folded_ticket := ILT.Readonly_fold(ILT.Readonly(rid, IL.ReadonlyInit(rop)), ticket);
        output, folded_stub, t := Impl.do_read(gs, node, rop, t, folded_ticket);
        stub := ILT.Readonly_unfold(folded_stub);
      }
      case UOp(uop) => {
        glinear var folded_stub;
        glinear var folded_ticket := ILT.Update_fold(ILT.Update(rid, IL.UpdateInit(uop)), ticket);
        output, folded_stub, t := Impl.do_update(gs, node, uop, folded_ticket, t);
        stub := ILT.Update_unfold(folded_stub);
      }
    }
  }
}
