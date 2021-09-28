include "NRSimple.i.dfy"
include "InfiniteLog.i.dfy"

abstract module InfiniteLog_Refines_NRSimple(nrifc: NRIfc) refines
  Refinement(
    AsyncIfc(nrifc),
    TicketStubStateMachine(nrifc, InfiniteLogSSM(nrifc)), // A
    NRSimple(nrifc) // B
  )
{
  import opened IL = InfiniteLogSSM(nrifc)
  import opened RequestIds

  predicate Inv(s: A.Variables) {
    IL.Inv(s)
  }

  lemma InitImpliesInv(s: A.Variables)
  //requires A.Init(s)
  ensures Inv(s)
  {
    IL.InitImpliesInv(s);
  }

  lemma NextPreservesInv(s: A.Variables, s': A.Variables, op: ifc.Op)
  //requires Inv(s)
  //requires A.Next(s, s', op)
  ensures Inv(s')
  {
    match op {
      case Start(rid, input) => {
        IL.NewTicketPreservesInv(s, s', rid, input);
      }
      case End(rid, output) => {
        var stub :| IL.ConsumeStub(s, s', rid, output, stub);
        IL.ConsumeStubPreservesInv(s, s', rid, output, stub);
      }
      case InternalOp => {
        var shard, shard', rest :| A.InternalNext(s, s', shard, shard', rest);
        IL.InternalPreservesInv(shard, shard', rest);
      }
    }
  }

  // updates map m1 with map m2, where all values of m2 aree added to m1, and existing values updated
  // can we just have one definition of this somewhere?
  // see: https://stackoverflow.com/questions/52610402/updating-a-map-with-another-map-in-dafny
  function {:opaque} map_update<K(!new), V>(m1: map<K, V>, m2: map<K, V>): map<K, V>
    ensures forall k :: k in m1 || k in m2 ==> k in map_update(m1, m2)
    ensures forall k :: k in m2 ==> map_update(m1, m2)[k] == m2[k]
    ensures forall k :: !(k in m2) && k in m1 ==> map_update(m1, m2)[k] == m1[k]
    ensures forall k :: !(k in m2) && !(k in m1) ==> !(k in map_update(m1, m2))
    ensures m1 == map[] ==> map_update(m1, m2) == m2
    ensures m2 == map[] ==> map_update(m1, m2) == m1
  {
    map k | k in (m1.Keys + m2.Keys) :: if k in m2 then m2[k] else m1[k]
  }

  // predicate to filter the in-progress read requests
  predicate ReadReq_InProgress(rid: RequestId, reqs: map<RequestId, ReadonlyState>)
  {
    && rid in reqs
    && (reqs[rid].ReadonlyCtail? || reqs[rid].ReadonlyReadyToRead? || reqs[rid].ReadonlyInit?)
  }

  // construction of the read requests for InfiniteLog -> NRSimple
  function {:opaque} I_ReadRequests(reqs: map<RequestId, ReadonlyState>) : (res :map<RequestId, B.ReadReq>)
    ensures forall rid | rid in res:: rid in reqs
    ensures forall rid | rid in reqs && reqs[rid].ReadonlyInit? :: rid in res && res[rid].ReadInit?;
    ensures forall rid | rid in reqs && reqs[rid].ReadonlyCtail? :: rid in res && res[rid].ReadReq?;
    ensures forall rid | rid in reqs && reqs[rid].ReadonlyReadyToRead? :: rid in res && res[rid].ReadReq?;
  {
    map rid | rid in reqs && ReadReq_InProgress(rid, reqs) ::
      if reqs[rid].ReadonlyInit? then B.ReadInit(reqs[rid].op) else B.ReadReq(reqs[rid].ctail, reqs[rid].op)
  }

  // predicate to filter in-progress update requests
  predicate UpdateRequests_InProgress(rid: RequestId, lupd: map<RequestId, UpdateState>)
  {
    && rid in lupd
    && (lupd[rid].UpdateInit? || lupd[rid].UpdatePlaced?)
  }

  // construction of the update requests for InfiniteLog -> NRSimple
  function {:opaque} I_UpdateRequests(lupd: map<RequestId, UpdateState>,  log: map<nat, LogEntry>) : (res : map<RequestId, nrifc.UpdateOp>)
    requires forall rid | rid in lupd && lupd[rid].UpdatePlaced? :: lupd[rid].idx in log
    ensures forall rid | rid in res :: rid in lupd
    ensures forall rid | rid in lupd && lupd[rid].UpdateInit? :: rid in res
    ensures forall rid | rid in lupd && lupd[rid].UpdatePlaced? :: rid in res
  {
    map rid | rid in lupd && UpdateRequests_InProgress(rid, lupd) ::
      (if lupd[rid].UpdateInit? then lupd[rid].op else log[lupd[rid].idx].op)
  }

  // predicate to filter completed update requests
  predicate UpdateRequests_Done(rid: RequestId, lupd: map<RequestId, UpdateState>)
  {
    && rid in lupd
    && (lupd[rid].UpdateApplied?)
  }

  // construction of the update responses for InfiniteLog -> NRSimple
  function {:opaque} I_UpdateResponses(lupd: map<RequestId, UpdateState>) :  map<RequestId, B.UpdateResp>
    ensures forall rid | rid in I_UpdateResponses(lupd) :: rid in lupd
    ensures forall rid | rid in I_UpdateResponses(lupd) :: lupd[rid].UpdateApplied?
  {
    map rid | rid in lupd && UpdateRequests_Done(rid, lupd) :: B.UpdateResp(lupd[rid].idx, lupd[rid].ret)
  }

  function {:opaque} I_Log(gtail: nat, log: map<nat, LogEntry>) : seq<nrifc.UpdateOp>
    requires forall i | 0 <= i < gtail :: i in log
    ensures forall i:nat | 0 <= i < |I_Log(gtail, log)| :: i in log
    ensures |I_Log(gtail, log)| == gtail
  {
    seq(gtail, i requires 0 <= i < gtail => log[i].op)
  }

  function I(s: A.Variables) : B.Variables
  //requires Inv(s)
  {
    B.Variables(
      I_Log(s.global_tail.value, s.log),
      // [], Inv_LogEntriesGlobalTail
      s.ctail.value,
      // readonly_reqs - ReadReq(ctail_at_start: nat, op: nrifc.ReadonlyOp)
      // TODO(travis): change NRCtail so it has states without ctail (corresponds to NrInfinite)
      I_ReadRequests(s.localReads),
      // update_reqs - UpdateResp(idx_in_log: nat, ret: nrifc.ReturnType)
      I_UpdateRequests(s.localUpdates, s.log),
      // update_resps - UpdateResp(idx_in_log: nat, ret: nrifc.ReturnType)
      I_UpdateResponses(s.localUpdates)
    )
  }

  lemma I_ReadRequests_Update_is(s: A.Variables, s': A.Variables, rid: RequestId, input: nrifc.Input)
    requires Inv(s)
    requires Inv(s')
    requires input.ROp?
    requires s'.localReads == s.localReads[rid := ReadonlyInit(input.readonly_op)]
    ensures I(s').readonly_reqs == I(s).readonly_reqs[rid := B.ReadInit(input.readonly_op)]
  {
     reveal_I_ReadRequests();
  }

  lemma I_UpdateRequests_Update_is(s: A.Variables, s': A.Variables, rid: RequestId, input: nrifc.Input)
    requires Inv(s)
    requires Inv(s')
    requires input.UOp?
    requires s'.localUpdates == s.localUpdates[rid :=  UpdateInit(input.update_op)]
    ensures I(s').update_reqs == I(s).update_reqs[rid := input.update_op]
    ensures I(s').update_resps == I(s).update_resps
  {
    assume false;
    //  reveal_I_UpdateResponses();
    //  reveal_I_UpdateRequests();
  }


  lemma InitRefinesInit(s: A.Variables)
  //requires A.Init(s)
  //requires Inv(s)
  ensures B.Init(I(s))

  // s: some previous thing with a missing piece
  // s': some next thing
  // "stub": the missing piece in s
  // s' = s + ticket
  lemma NewTicket_Refines_Start(s: A.Variables, s': A.Variables,
      rid: RequestId, input: nrifc.Input)
  requires IL.NewTicket(s, s', rid, input)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.Start(rid, input))
  {
    // construct the ticket
    var ticket := Ticket(rid, input);
    // establish that s' is the dot of the s and the new ticket.
    assert s' == dot(s, ticket);
    // assert the ticket values
    assert ticket.log == map[];
    assert !ticket.global_tail.Some?;
    assert ticket.replicas == map[];
    assert ticket.localTails == map[];
    assert !ticket.ctail.Some?;
    assert ticket.combiner == map[];
    // assert the unchanged things for both branches
    assert s'.replicas == s.replicas;
    assert s'.localTails == s.localTails;
    assert s'.ctail == s.ctail;
    assert s'.combiner == s.combiner;
    assert s'.log == s.log;
    assert s'.global_tail == s.global_tail;
    // create the lifted state machines
    var IS := I(s);
    var IS' := I(s');
    // nothing should have changed in the ctail and the log
    assert IS'.ctail == IS.ctail;
    assert IS'.log == IS.log;




    // now branch off depending up the update type
    if input.ROp? {
      // now assert the ROp ticket
      assert ticket.localUpdates == map[];
      assert ticket.localReads == map[rid := ReadonlyInit(input.readonly_op)];

      // rid is not there before
      assert rid !in s.localReads;
      assert rid !in IS.readonly_reqs;

      assert s'.localUpdates == s.localUpdates;
      assert IS'.update_reqs == IS.update_reqs;
      assert IS'.update_resps == IS.update_resps;

      // the next assert take a little while...
      assert s'.localReads == s.localReads[rid := ReadonlyInit(input.readonly_op)];

      I_ReadRequests_Update_is(s, s', rid, input);
      assert IS'.readonly_reqs == IS.readonly_reqs[rid := B.ReadInit(input.readonly_op)];

      assert B.NextStep(IS, IS', ifc.Start(rid, input), B.StartReadonly_Step(rid, input.readonly_op));
    } else {
      // it has to be an UOp;
      assert input.UOp?;
      assert ticket.localReads == map[];
      assert ticket.localUpdates == map[rid :=  UpdateInit(input.update_op)];

      assert rid !in s.localUpdates;
      assert rid !in IS.update_reqs;

      assert s'.localReads == s.localReads;
      assert IS'.readonly_reqs == IS.readonly_reqs;
      // that step takes a little while
      assert s'.localUpdates == s.localUpdates[rid :=  UpdateInit(input.update_op)];

      I_UpdateRequests_Update_is(s, s', rid, input);
      assert IS'.update_reqs == IS.update_reqs[rid := input.update_op];
      assert IS'.update_resps == IS.update_resps;

      assert B.NextStep(IS, IS', ifc.Start(rid, input), B.StartUpdate_Step(rid, input.update_op));
    }
  }



  lemma ConsumeStub_Refines_End(s: A.Variables, s': A.Variables,
      rid: RequestId, output: nrifc.Output, stub: M)
  requires IL.ConsumeStub(s, s', rid, output, stub)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.End(rid, output))
  {
    // refine EndUpdate or EndReadonly


    if rid in s.localUpdates {
      assert s.localUpdates[rid].UpdateDone?;
      assert B.EndUpdate(I(s), I(s'), rid, output);
    } else {
      // TODO(gz): why doesn't this hold?
      assert rid in s.localReads && (rid !in s'.localReads && rid in stub.localReads);
      assert s'.localReads[rid].ReadonlyDone?;
      //assert B.FinishReadonly(I(s), I(s'), rid, _, output);
    }

  }

  lemma GoToCombinerReady_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId)
  requires IL.GoToCombinerReady(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    reveal_I_ReadRequests();
    reveal_I_UpdateRequests();
    reveal_I_UpdateResponses();
    reveal_I_Log();
    assert I(s) == I(s');
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma ExecLoadLtail_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId)
  requires IL.ExecLoadLtail(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
  }

  lemma ExecLoadGlobalTail_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId)
  requires IL.ExecLoadGlobalTail(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
  }

  lemma ExecDispatchLocal_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId)
  requires IL.ExecDispatchLocal(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
  }

  lemma ExecDispatchRemote_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId)
  requires IL.ExecDispatchRemote(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
  }

  lemma TransitionReadonlyReadCtail_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId, rid: RequestId)
  requires IL.TransitionReadonlyReadCtail(s, s', nodeId, rid)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert s'.replicas == s.replicas;
    assert s'.localTails == s.localTails;
    assert s'.ctail == s.ctail;
    assert s'.combiner == s.combiner;
    assert s'.log == s.log;
    assert s'.global_tail == s.global_tail;

    var IS := I(s);
    var IS' := I(s');

    assert IS.ctail == IS'.ctail;
    assert IS.log == IS'.log;
    assert IS.update_resps == IS'.update_resps;
    
    assert IS'.ctail == s'.ctail.value;
    assert IS.ctail == s.ctail.value;

    assert s'.localUpdates == s.localUpdates;

    assert rid in s.localReads;
    assert rid in s'.localReads;
    assert s.localReads[rid].ReadonlyInit?;
    assert s'.localReads[rid].ReadonlyCtail?;

    assert rid in IS.readonly_reqs;
    assert rid in IS'.readonly_reqs;
    assert IS.readonly_reqs[rid].ReadInit?;
    assert IS'.readonly_reqs[rid].ReadReq?;

    assert s.ctail.Some?;
    assert s'.localReads == s.localReads[rid := ReadonlyCtail(s.localReads[rid].op, s.ctail.value)];    
    assert IS.update_reqs == IS'.update_reqs;


    //assert s'.localReads[rid].op == IS.readonly_reqs[rid].op;
    assert s'.localReads[rid].op == s.localReads[rid].op;
    //assert s'.localReads[rid].op == IS'.readonly_reqs[rid].op;

    assert IS'.readonly_reqs == IS.readonly_reqs[rid := B.ReadReq(IS.ctail, IS.readonly_reqs[rid].op) ];
    assert IS'.readonly_reqs == IS.readonly_reqs[rid := B.ReadReq(s.ctail.value, s.localReads[rid].op) ];
  }

  lemma TransitionReadonlyReadyToRead_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId, rid: RequestId)
  requires IL.TransitionReadonlyReadyToRead(s, s', nodeId, rid)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
  }

  lemma TransitionReadonlyDone_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId, rid: RequestId)
  requires IL.TransitionReadonlyDone(s, s', nodeId, rid)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
  }

  lemma AdvanceTail_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId, request_ids: seq<RequestId>)
  requires IL.AdvanceTail(s, s', nodeId, request_ids)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
  }

  lemma UpdateCompletedTail_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId)
  requires IL.UpdateCompletedTail(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
  }

  lemma Internal_Refines_Internal(s: A.Variables, s': A.Variables)
  requires IL.Internal(s, s')
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var step :| NextStep(s, s', step);
    match step {
      case GoToCombinerReady_Step(nodeId) => { GoToCombinerReady_Refines(s, s', nodeId); }
      case ExecLoadLtail_Step(nodeId) => { ExecLoadLtail_Refines(s, s', nodeId); }
      case ExecLoadGlobalTail_Step(nodeId) => { ExecLoadGlobalTail_Refines(s, s', nodeId); }
      case ExecDispatchLocal_Step(nodeId) => { ExecDispatchLocal_Refines(s, s',nodeId); }
      case ExecDispatchRemote_Step(nodeId) => { ExecDispatchRemote_Refines(s, s',nodeId); }
      case TransitionReadonlyReadCtail_Step(nodeId, rid) => { TransitionReadonlyReadCtail_Refines(s, s', nodeId, rid); }
      case TransitionReadonlyReadyToRead_Step(nodeId, rid) => { TransitionReadonlyReadyToRead_Refines(s, s', nodeId, rid); }
      case TransitionReadonlyDone_Step(nodeId, rid) => { TransitionReadonlyDone_Refines(s, s', nodeId, rid); }
      case AdvanceTail_Step(nodeId, request_ids) => { AdvanceTail_Refines(s, s', nodeId, request_ids); }
      case UpdateCompletedTail_Step(nodeId) => { UpdateCompletedTail_Refines(s, s',nodeId); }
    }
  }

  lemma NextRefinesNext(s: A.Variables, s': A.Variables, op: ifc.Op)
  //requires Inv(s)
  //requires Inv(s')
  //requires A.Next(s, s', op)
  ensures B.Next(I(s), I(s'), op)
  {
    match op {
      case Start(rid, input) => {
        NewTicket_Refines_Start(s, s', rid, input);
      }
      case End(rid, output) => {
        var stub :| IL.ConsumeStub(s, s', rid, output, stub);
        ConsumeStub_Refines_End(s, s', rid, output, stub);
      }
      case InternalOp => {
        var shard, shard', rest :| A.InternalNext(s, s', shard, shard', rest);
        InternalMonotonic(shard, shard', rest);
        Internal_Refines_Internal(s, s');
      }
    }
  }
}
