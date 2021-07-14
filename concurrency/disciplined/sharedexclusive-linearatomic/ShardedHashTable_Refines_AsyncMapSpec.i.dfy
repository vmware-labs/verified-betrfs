include "../common/AppSpec.s.dfy"
include "../common/AsyncAppSpec.s.dfy"
include "ShardedHashTable.i.dfy"
include "../common/MultisetLemmas.i.dfy"
// include "Interpretation.i.dfy"

module ResourceStateMachine_Refines_AsyncMapSpec {
  import A = ShardedHashTable
  import B = AsyncSpec // AsyncMapSpec
  import CircularTable

  // import HT = 
  // import opened Interpretation
  import Multisets
  import MapSpec
  import Ifc = AsyncIfc
  import MapIfc
  import opened KeyValueType
  import MultisetLemmas

  function req_of_ticket(t: A.Ticket) : B.Req {
    B.Req(t.rid, t.input)
  }

  function resp_of_stub(t: A.Stub) : B.Resp {
    B.Resp(t.rid, t.output)
  }

  function reqs_of_tickets(t: multiset<A.Ticket>) : multiset<B.Req> {
    Multisets.Apply(req_of_ticket, t)
  }

  function resps_of_stubs(t: multiset<A.Stub>) : multiset<B.Resp> {
    Multisets.Apply(resp_of_stub, t)
  }

  function I(s: A.Variables) : B.Variables
  requires A.Inv(s)
  {
    var t := CircularTable.I(s.table);
    B.Variables(
      MapSpec.Variables(t),
      reqs_of_tickets(s.tickets),
      resps_of_stubs(s.stubs))
  }
 
  lemma InsertRefinesMap(s: A.Variables, s': A.Variables, step: A.Step)
    requires A.Inv(s) && A.Inv(s')
    requires step.InsertStep? && A.NextStep(s, s', step)
    // ensures Next(s: Variables, s': Variables, op: Ifc.Op)
  {
    var si, si' := I(s), I(s');
    var m, m' := si.s.m, si'.s.m;
    var key, value :=  step.ticket.input.key, step.ticket.input.value;

    forall k : Key
      ensures k != key ==> 
        (k in m' <==> k in m) && (k in m' ==> m[k] == m'[k])
      ensures k == step.ticket.input.key ==>
        (k in m' && m'[k] == value)
    {
      if k == key {
        CircularTable.KeyExists(s'.table, step.start, key, value);
      } else {
        if k in m' {
          assert 
        }
        // assume false;
      }
    }
    
    assert m' == m[key := value];
  }


  lemma Internal_RefinesMap(s: A.Variables, s': A.Variables)
    requires A.Inv(s)
    requires A.Internal(s, s')
    ensures A.Inv(s')
    ensures B.Next(I(s), I(s'), Ifc.InternalOp)
  {

    MultisetLemmas.MultisetSimplificationTriggers<A.Ticket, B.Req>();
    MultisetLemmas.MultisetSimplificationTriggers<A.Stub, B.Resp>();
    // MultisetLemmas.MultisetSimplificationTriggers<S.QueryRes, A.Stub>();

    var step: A.Step :| A.NextStep(s, s', step); 
    A.NextPreservesInv(s, s');

    if step.InsertStep? {
      var ticket := step.ticket;

      assert B.LinearizationPoint(I(s), I(s'), ticket.rid, ticket.input, MapIfc.InsertOutput(true));
    } else {
      assume false;
    }
    // InsertEnable(v, step)


    // else if step.OverwriteStep? then OverwriteEnable(v, step)
    // else if step.QueryFoundStep? then QueryFoundEnable(v, step)
    // else if step.QueryNotFoundStep? then QueryNotFoundEnable(v, step)
    // else if step.RemoveStep? then RemoveEnable(v, step)
    // else if step.RemoveNotFoundStep? then RemoveNotFoundEnable(v, step)    
  
  }

  // lemma NewTicket_RefinesMap(s: A.Variables, s': A.Variables, rid: int, input: MapIfc.Input)
  //   requires A.Inv(s)
  //   requires A.NewTicket(s, s', rid, input)
  //   ensures A.Inv(s')
  //   ensures B.Next(I(s), I(s'), Ifc.Start(rid, input))
  // {
  //   assert s'.table == s.table;
  //   assert s'.stubs == s.stubs;
  //   MultisetLemmas.MultisetSimplificationTriggers<HT.Ticket, B.Req>();
  //   //assert s'.tickets == s.tickets + multiset{HT.Ticket(rid, input)};
  //   //assert I(s').reqs == I(s).reqs + multiset{B.Req(rid, input)};
  //   //assert I(s').s == I(s).s;
  // }

  // lemma ConsumeStub_RefinesMap(s: A.Variables, s': A.Variables, rid: int, output: MapIfc.Output)
  //   requires A.Inv(s)
  //   requires A.ConsumeStub(s, s', rid, output)
  //   ensures A.Inv(s')
  //   ensures B.Next(I(s), I(s'), Ifc.End(rid, output))
  // {
  //   assert s'.table == s.table;
  //   assert s'.tickets == s.tickets;
  //   assert s.stubs == s'.stubs + multiset{HT.Stub(rid, output)};
  //   MultisetLemmas.MultisetSimplificationTriggers<HT.Stub, B.Resp>();
  //   /*assert s.stubs == s'.stubs + multiset{HT.Stub(rid, output)};
  //   assert I(s).resps == I(s').resps + multiset{B.Resp(rid, output)};
  //   assert I(s').resps == I(s).resps - multiset{B.Resp(rid, output)};
  //   assert I(s').s == I(s).s;
  //   assert I(s').reqs == I(s).reqs;
  //   assert B.Resp(rid, output) in I(s).resps;*/
  // }

}
