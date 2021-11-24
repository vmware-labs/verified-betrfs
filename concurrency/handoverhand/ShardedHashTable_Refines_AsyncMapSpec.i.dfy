include "Interpretation.i.dfy"
include "../framework/StateMachines.s.dfy"

module ResourceStateMachine_Refines_AsyncMapSpec
  refines Refinement(
      AsyncIfc(MapIfc),
      TicketStubStateMachine(MapIfc, ShardedHashTable),
      AsyncStateMachine(MapIfc, MapSpec)
  )
{
  import HT = ShardedHashTable
  import opened Interpretation
  import Multisets
  import MapSpec
  import Ifc = AsyncIfc
  import MapIfc
  import opened KeyValueType

  function req_of_ticket(t: HT.Request) : B.Req {
    B.Req(t.rid, t.input)
  }

  function resp_of_stub(t: HT.Response) : B.Resp {
    B.Resp(t.rid, t.output)
  }

  function reqs_of_tickets(t: multiset<HT.Request>) : multiset<B.Req> {
    Multisets.Apply(req_of_ticket, t)
  }

  function resps_of_stubs(t: multiset<HT.Response>) : multiset<B.Resp> {
    Multisets.Apply(resp_of_stub, t)
  }

  function I(s: A.Variables) : B.Variables
  requires A.Inv(s)
  {
    var t := interp(s.table);
    B.Variables(
      MapSpec.Variables(map_remove_nones(t.ops)),
      reqs_of_tickets(s.tickets),
      resps_of_stubs(s.stubs)
          + resps_of_stubs(t.stubs)
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
    MultisetLemmas.MultisetSimplificationTriggers<HT.Request, B.Req>();
    MultisetLemmas.MultisetSimplificationTriggers<HT.Response, B.Resp>();
    MultisetLemmas.MultisetSimplificationTriggers<S.QueryRes, HT.Response>();

    var step :| HT.NextStep(s, s', step);
    match step {
      case InsertSkipStep(pos) => {
        InsertSkip_PreservesInterp(s, s', pos);
      }
      case InsertSwapStep(pos) => {
        InsertSwap_PreservesInterp(s, s', pos);
      }
      case InsertDoneStep(pos) => {
        InsertDone_PreservesInterp(s, s', pos);
        //assert I(s).resps == I(s').resps;
        //assert I(s) == I(s');
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

        /*assert resps_of_stubs(s.stubs) + multiset{B.Resp(s.table[pos].value.state.rid, MapIfc.RemoveOutput(true))}
            == resps_of_stubs(s'.stubs);
        assert resps_of_stubs(apply_to_remove_stub(interp(s.table).removes))
            == resps_of_stubs(apply_to_remove_stub(interp(s'.table).removes)) + multiset{B.Resp(s.table[pos].value.state.rid, MapIfc.RemoveOutput(true))};
        assert resps_of_stubs(s.stubs)
                + resps_of_stubs(apply_to_remove_stub(interp(s.table).removes))
            == resps_of_stubs(s'.stubs)
                + resps_of_stubs(apply_to_remove_stub(interp(s'.table).removes));
        assert I(s).resps == I(s').resps;
        assert I(s) == I(s');*/
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
        var I_s := I(s);
        var I_s' := I(s');
        var rid := insert_ticket.rid;
        var input := insert_ticket.input;
        var output := MapIfc.InsertOutput(true);

        assert s.tickets == s'.tickets + multiset{insert_ticket};
        /*assert resps_of_stubs(interp(s'.table).stubs)
            == resps_of_stubs(interp(s.table).stubs) + multiset{B.Resp(rid, output)};
        assert B.Req(rid, input) in I_s.reqs;
        assert I_s.reqs == I_s'.reqs + multiset{B.Req(rid, input)};
        assert I_s'.resps == I_s.resps + multiset{B.Resp(rid, output)};
        assert MapSpec.Next(I_s.s, I_s'.s, MapIfc.Op(input, output));*/
        assert B.LinearizationPoint(I_s, I_s', rid, input, output);
      }
      case ProcessRemoveTicketStep(remove_ticket) => {
        ProcessRemoveTicket_ChangesInterp(s, s', remove_ticket);
        assert s.tickets == s'.tickets + multiset{remove_ticket};
        assert B.LinearizationPoint(I(s), I(s'), remove_ticket.rid, remove_ticket.input,
            MapIfc.RemoveOutput(remove_ticket.input.key in I(s).s.m));
      }
      case ProcessQueryTicketStep(query_ticket) => {
        ProcessQueryTicket_ChangesInterp(s, s', query_ticket);

        assert s.tickets == s'.tickets + multiset{query_ticket};

        if query_ticket.input.key in I(s).s.m {
          assert B.LinearizationPoint(I(s), I(s'), query_ticket.rid, query_ticket.input,
              MapIfc.QueryOutput(Found(I(s).s.m[query_ticket.input.key])));
        } else {
          assert B.LinearizationPoint(I(s), I(s'), query_ticket.rid, query_ticket.input,
              MapIfc.QueryOutput(NotFound));
        }
      }
    }
  }

  lemma NewTicket_RefinesMap(s: A.Variables, s': A.Variables, rid: int, input: MapIfc.Input)
    requires A.Inv(s)
    requires A.NewTicket(s, s', rid, input)
    ensures A.Inv(s')
    ensures B.Next(I(s), I(s'), Ifc.Start(rid, input))
  {
    assert s'.table == s.table;
    assert s'.stubs == s.stubs;
    MultisetLemmas.MultisetSimplificationTriggers<HT.Request, B.Req>();
    //assert s'.tickets == s.tickets + multiset{HT.Request(rid, input)};
    //assert I(s').reqs == I(s).reqs + multiset{B.Req(rid, input)};
    //assert I(s').s == I(s).s;
  }

  // lemma ConsumeStub_RefinesMap(s: A.Variables, s': A.Variables, rid: int, output: MapIfc.Output)
  //   requires A.Inv(s)
  //   requires A.ConsumeStub(s, s', rid, output)
  //   ensures A.Inv(s')
  //   ensures B.Next(I(s), I(s'), Ifc.End(rid, output))
  // {
  //   assert s'.table == s.table;
  //   assert s'.tickets == s.tickets;
  //   assert s.stubs == s'.stubs + multiset{HT.Response(rid, output)};
  //   MultisetLemmas.MultisetSimplificationTriggers<HT.Response, B.Resp>();
  //   /*assert s.stubs == s'.stubs + multiset{HT.Response(rid, output)};
  //   assert I(s).resps == I(s').resps + multiset{B.Resp(rid, output)};
  //   assert I(s').resps == I(s).resps - multiset{B.Resp(rid, output)};
  //   assert I(s').s == I(s).s;
  //   assert I(s').reqs == I(s).reqs;
  //   assert B.Resp(rid, output) in I(s).resps;*/
  // }

}
