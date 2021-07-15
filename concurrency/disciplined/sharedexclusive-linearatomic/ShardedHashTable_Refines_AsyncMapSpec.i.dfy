include "../common/AppSpec.s.dfy"
include "../common/AsyncAppSpec.s.dfy"
include "ShardedHashTable.i.dfy"
include "../common/MultisetLemmas.i.dfy"
// include "Interpretation.i.dfy"

module ResourceStateMachine_Refines_AsyncMapSpec {
  import A = ShardedHashTable
  import B = AsyncSpec // AsyncMapSpec
  import opened CircularTable

  // import HT = 
  // import opened Interpretation
  import Multisets
  import MapSpec
  import Ifc = AsyncIfc
  import MapIfc
  import opened KeyValueType
  import MultisetLemmas
  import opened CircularRange

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
    returns (output: MapIfc.Output)
    requires A.Inv(s) && A.Inv(s')
    requires step.InsertStep? && A.NextStep(s, s', step)
    ensures MapSpec.Next(
      MapSpec.Variables(I(s).s.m),
      MapSpec.Variables(I(s').s.m),
      MapIfc.Op(step.ticket.input, output));
  {
    var InsertStep(ticket, start, end) := step;
    var InsertInput(key, value) := ticket.input;
    var table, table' := s.table, s'.table;
    var inserted := Full(key, value);

    ProbeRangeSufficient(table, key, start);
    ContainmentEquivalent(table, key);
    RightShiftPreservesMapping(table, table', inserted);

    var si, si' := I(s), I(s');
    var m, m' := si.s.m, si'.s.m;

    assert m' == m[key := value];
    output := MapIfc.InsertOutput(true);
  }

  lemma OverwriteRefinesMap(s: A.Variables, s': A.Variables, step: A.Step)
    returns (output: MapIfc.Output)
    requires A.Inv(s) && A.Inv(s')
    requires step.OverwriteStep? && A.NextStep(s, s', step)
    ensures MapSpec.Next(
      MapSpec.Variables(I(s).s.m),
      MapSpec.Variables(I(s').s.m),
      MapIfc.Op(step.ticket.input, output))
  {
    var OverwriteStep(ticket, end) := step;
    var InsertInput(key, value) := ticket.input;
    var table, table' := s.table, s'.table;
    var inserted := Full(key, value);

    ContainmentEquivalent(table, key);
    OverwritePreservesMapping(table, table', end, inserted);

    var si, si' := I(s), I(s');
    var m, m' := si.s.m, si'.s.m;

    assert m' == m[key := value];

    output := MapIfc.InsertOutput(true);
  }

  lemma RemoveRefinesMap(s: A.Variables, s': A.Variables, step: A.Step)
    returns (output: MapIfc.Output)
    requires A.Inv(s) && A.Inv(s')
    requires step.RemoveStep? && A.NextStep(s, s', step)
    ensures MapSpec.Next(
      MapSpec.Variables(I(s).s.m),
      MapSpec.Variables(I(s').s.m),
      MapIfc.Op(step.ticket.input, output))
  {
    var RemoveStep(ticket, start, end) := step;
    var key := ticket.input.key;
    var table, table' := s.table, s'.table;

    ContainmentEquivalent(table, key);
    LeftShiftPreservesMapping(table, table', key);

    var si, si' := I(s), I(s');
    var m, m' := si.s.m, si'.s.m;

    assert m' == m - {key};
    output := MapIfc.RemoveOutput(true);
  }

  lemma RemoveNotFoundRefinesMap(s: A.Variables, s': A.Variables, step: A.Step)
    returns (output: MapIfc.Output)
    requires A.Inv(s) && A.Inv(s')
    requires step.RemoveNotFoundStep? && A.NextStep(s, s', step)
    ensures MapSpec.Next(
      MapSpec.Variables(I(s).s.m),
      MapSpec.Variables(I(s').s.m),
      MapIfc.Op(step.ticket.input, output))
  {
    var RemoveNotFoundStep(ticket, end) := step;
    var key := ticket.input.key;
    var table, table' := s.table, s'.table;
    ProbeRangeSufficient(table, key, end);

    ContainmentEquivalent(table, key);

    var si, si' := I(s), I(s');
    var m, m' := si.s.m, si'.s.m;
    assert key !in m;

    output := MapIfc.RemoveOutput(false);
  }

  lemma QueryNotFoundRefinesMap(s: A.Variables, s': A.Variables, step: A.Step)
    returns (output: MapIfc.Output)
    requires A.Inv(s) && A.Inv(s')
    requires step.QueryNotFoundStep? && A.NextStep(s, s', step)
    ensures MapSpec.Next(
      MapSpec.Variables(I(s).s.m),
      MapSpec.Variables(I(s').s.m),
      MapIfc.Op(step.ticket.input, output))
  {
    var QueryNotFoundStep(ticket, end) := step;
    var key := ticket.input.key;
    var table, table' := s.table, s'.table;
    ProbeRangeSufficient(table, key, end);

    ContainmentEquivalent(table, key);

    var si, si' := I(s), I(s');
    var m, m' := si.s.m, si'.s.m;
    assert key !in m;

    output := MapIfc.QueryOutput(QueryResult.NotFound);
  }

  lemma QueryFoundRefinesMap(s: A.Variables, s': A.Variables, step: A.Step)
    returns (output: MapIfc.Output)
    requires A.Inv(s) && A.Inv(s')
    requires step.QueryFoundStep? && A.NextStep(s, s', step)
    ensures MapSpec.Next(
      MapSpec.Variables(I(s).s.m),
      MapSpec.Variables(I(s').s.m),
      MapIfc.Op(step.ticket.input, output))
  {
    var QueryFoundStep(ticket, end) := step;
    var key := ticket.input.key;
    var table := s.table;

    ContainmentEquivalent(table, key);

    var si, si' := I(s), I(s');
    var m := si.s.m;

    assert key in m && m[key] == table[end].value.value;
    output := MapIfc.QueryOutput(QueryResult.Found(m[key]));
  }

  lemma InternalRefinesMap(s: A.Variables, s': A.Variables)
    requires A.Inv(s)
    requires A.Internal(s, s')
    ensures A.Inv(s')
    ensures B.Next(I(s), I(s'), Ifc.InternalOp)
  {
    // MultisetLemmas.MultisetSimplificationTriggers<A.Ticket, B.Req>();
    // MultisetLemmas.MultisetSimplificationTriggers<A.Stub, B.Resp>();

    var step: A.Step :| A.NextStep(s, s', step); 
    A.NextPreservesInv(s, s');

    var si, si' := I(s), I(s');

    var ticket := step.ticket;
    var rid, input := ticket.rid, ticket.input;

    var output;

    if step.InsertStep? {
      output := InsertRefinesMap(s, s', step);
    } else if step.OverwriteStep? {
      output := OverwriteRefinesMap(s, s', step);
    } else if step.QueryFoundStep? {
      output := QueryFoundRefinesMap(s, s', step);
    } else if step.QueryNotFoundStep? {
      output := QueryNotFoundRefinesMap(s, s', step);
    } else if step.RemoveStep? {
      output := RemoveRefinesMap(s, s', step);
    } else if step.RemoveNotFoundStep? {
      output := RemoveNotFoundRefinesMap(s, s', step);
    } else {
      assert false;
    }

    assume si.reqs == si'.reqs + multiset{B.Req(rid, input)};
    assume si'.resps == si.resps + multiset{B.Resp(rid, output)};

    assert B.LinearizationPoint(si, si', rid, input, output);
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
