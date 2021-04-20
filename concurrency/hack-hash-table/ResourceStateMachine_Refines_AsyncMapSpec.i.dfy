include "MapSpec.s.dfy"
include "ResourceStateMachine.i.dfy"
include "Interpretation.i.dfy"

module ResourceStateMachine_Refines_AsyncMapSpec {
  import A = ResourceStateMachine
  import B = AsyncSpec // AsyncMapSpec

  import HT = HTResource
  import opened Interpretation
  import Multisets
  import MapSpec
  import Ifc = AsyncIfc

  function req_of_ticket(t: HT.Ticket) : B.Req {
    B.Req(t.rid, t.input)
  }

  function resp_of_stub(t: HT.Stub) : B.Resp {
    B.Resp(t.rid, t.output)
  }

  function reqs_of_tickets(t: multiset<HT.Ticket>) : multiset<B.Req> {
    Multisets.Apply(req_of_ticket, t)
  }

  function resps_of_stubs(t: multiset<HT.Stub>) : multiset<B.Resp> {
    Multisets.Apply(resp_of_stub, t)
  }

  function I(s: A.Variables) : B.Variables
  requires A.Inv(s)
  {
    var t := interp(s.table);
    B.Variables(
      MapSpec.Variables(map_remove_nones(t.ops)),
      reqs_of_tickets(s.tickets),
      resps_of_stubs(t.stubs)
          + resps_of_stubs(apply_to_query_stub(t.queries))
          + resps_of_stubs(apply_to_remove_stub(t.removes))
    )
  }
 
  lemma Internal_RefinesMap(s: A.Variables, s': A.Variables)
    requires A.Inv(s)
    requires A.Internal(s, s')
    ensures A.Inv(s')
    ensures B.Next(I(s), I(s'), Ifc.InternalOp)
  {
    var step :| HT.UpdateStep(s, s', step);
    match step {
      case InsertSkipStep(pos) => {
        InsertSkip_PreservesInterp(s, s', pos);
      }
      case InsertSwapStep(pos) => {
        InsertSwap_PreservesInterp(s, s', pos);
      }
      case InsertDoneStep(pos) => {
        InsertDone_PreservesInterp(s, s', pos);
      }
      case InsertUpdateStep(pos) => {
        InsertUpdate_PreservesInterp(s, s', pos);
      }
      case RemoveSkipStep(pos) => {
        RemoveSkip_PreservesInterp(s, s', pos);
      }
      case RemoveFoundItStep(pos) => {
        RemoveFoundIt_PreservesInterp(s, s', pos);
      }
      case RemoveNotFoundStep(pos) => {
        RemoveNotFound_PreservesInterp(s, s', pos);
      }
      case RemoveTidyStep(pos) => {
        RemoveTidy_PreservesInterp(s, s', pos);
      }
      case RemoveDoneStep(pos) => {
        RemoveDone_PreservesInterp(s, s', pos);
      }
      case QuerySkipStep(pos) => {
        QuerySkip_PreservesInterp(s, s', pos);
      }
      case QueryDoneStep(pos) => {
        QueryDone_PreservesInterp(s, s', pos);
      }
      case QueryNotFoundStep(pos) => {
        QueryNotFound_PreservesInterp(s, s', pos);
      }

      case ProcessInsertTicketStep(insert_ticket) => {
        ProcessInsertTicket_ChangesInterp(s, s', insert_ticket);
      }
      case ProcessRemoveTicketStep(remove_ticket) => {
        ProcessRemoveTicket_ChangesInterp(s, s', remove_ticket);
      }
      case ProcessQueryTicketStep(query_ticket) => {
        ProcessQueryTicket_ChangesInterp(s, s', query_ticket);
      }
    }
  }
}
