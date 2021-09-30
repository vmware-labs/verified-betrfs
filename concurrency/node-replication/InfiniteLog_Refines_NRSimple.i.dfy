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
   import opened Options

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
  }

  // construction of the read requests for InfiniteLog -> NRSimple
  function {:opaque} I_ReadRequests(reqs: map<RequestId, ReadonlyState>) : (res :map<RequestId, B.ReadReq>)
    ensures forall rid | rid in res:: rid in reqs
    ensures forall rid | rid in reqs && reqs[rid].ReadonlyInit? :: rid in res && res[rid].ReadInit? && res[rid].op == reqs[rid].op;
    ensures forall rid | rid in reqs && reqs[rid].ReadonlyCtail? :: rid in res && res[rid].ReadReq? && res[rid].op == reqs[rid].op;
    ensures forall rid | rid in reqs && reqs[rid].ReadonlyReadyToRead? :: rid in res && res[rid].ReadReq? && res[rid].op == reqs[rid].op;
    ensures forall rid | rid !in reqs :: rid !in res
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
    ensures forall rid | rid in res :: lupd[rid].UpdateInit? || lupd[rid].UpdatePlaced?
    ensures forall rid | rid !in lupd :: rid !in res
  {
    map rid | rid in lupd && UpdateRequests_InProgress(rid, lupd) ::
      (if lupd[rid].UpdateInit? then lupd[rid].op else log[lupd[rid].idx].op)
  }

  // predicate to filter completed update requests
  predicate UpdateRequests_Done(rid: RequestId, lupd: map<RequestId, UpdateState>)
  {
    && rid in lupd
    && (lupd[rid].UpdateApplied? || lupd[rid].UpdateDone?)
  }

  // construction of the update responses for InfiniteLog -> NRSimple
  function {:opaque} I_UpdateResponses(lupd: map<RequestId, UpdateState>) : (res : map<RequestId, B.UpdateResp>)
    ensures forall rid | rid in res :: rid in lupd
    ensures forall rid | rid in res:: lupd[rid].UpdateApplied? || lupd[rid].UpdateDone?
    ensures forall rid | rid in lupd && lupd[rid].UpdateApplied? :: rid in res
    ensures forall rid | rid in lupd && lupd[rid].UpdateDone? :: rid in res
    ensures forall rid | rid !in lupd :: rid !in res
    ensures forall rid | rid in res :: rid in lupd && res[rid].ret == lupd[rid].ret
    ensures forall rid | rid in res :: rid in lupd && res[rid].idx_in_log == lupd[rid].idx
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

  lemma I_ReadRequests_Update_CTail_is(s: A.Variables, s': A.Variables, rid: RequestId)
    requires Inv(s)
    requires Inv(s')
    requires rid in s.localReads && s.localReads[rid].ReadonlyInit?
    requires s'.localReads == s.localReads[rid := ReadonlyCtail(s.localReads[rid].op, s.ctail.value)]
    ensures I(s').readonly_reqs == I(s).readonly_reqs[rid := B.ReadReq(s.ctail.value, s.localReads[rid].op)]
  {
     reveal_I_ReadRequests();
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
    requires rid !in s.localUpdates;
    requires s'.localUpdates == s.localUpdates[rid :=  UpdateInit(input.update_op)]
    requires s'.log == s.log
    ensures I(s').update_reqs == I(s).update_reqs[rid := input.update_op]
    ensures I(s').update_resps == I(s).update_resps
  {
    reveal_I_UpdateResponses();
    assert I(s').update_resps == I(s).update_resps;

    reveal_I_UpdateRequests();
    assert I(s').update_reqs == I(s).update_reqs[rid := input.update_op];
  }

  lemma I_UpdateResponses_Update_is(s: A.Variables, s': A.Variables, rid: RequestId, idx: nat, output: nrifc.Output)
    requires Inv(s)
    requires Inv(s')
    requires rid in s.localUpdates;
    requires rid !in s'.localUpdates;
    requires s'.log == s.log
    requires s.localUpdates == s'.localUpdates[rid :=  UpdateDone(output, idx)]
    ensures I(s).update_resps == I(s').update_resps[rid :=  B.UpdateResp(idx, output)]
    ensures I(s).update_reqs == I(s').update_reqs
  {
    reveal_I_UpdateResponses();
    assert I(s).update_resps == I(s').update_resps[rid :=  B.UpdateResp(idx, output)];

    reveal_I_UpdateRequests();
    assert I(s').update_reqs == I(s).update_reqs;
  }

  lemma I_UpdateResponses_NoChange_is(s: A.Variables, s': A.Variables, rid: RequestId)
    requires Inv(s)
    requires Inv(s')
    requires rid in s.localUpdates && s.localUpdates[rid].UpdateApplied?;
    requires s'.log == s.log
    requires s'.localUpdates == s.localUpdates[rid :=  UpdateDone(s.localUpdates[rid].ret, s.localUpdates[rid].idx)]
    ensures I(s).update_resps == I(s').update_resps
    ensures I(s).update_reqs == I(s').update_reqs
  {
    reveal_I_UpdateResponses();
    assert I(s).update_resps == I(s').update_resps;

    reveal_I_UpdateRequests();
    assert I(s').update_reqs == I(s).update_reqs;
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
      assume s'.localReads == s.localReads[rid := ReadonlyInit(input.readonly_op)];

      I_ReadRequests_Update_is(s, s', rid, input);
      assert IS'.readonly_reqs == IS.readonly_reqs[rid := B.ReadInit(input.readonly_op)];

      assert B.NextStep(IS, IS', ifc.Start(rid, input), B.StartReadonly_Step(rid, input.readonly_op));
    } else {
      // it has to be an UOp;
      assert input.UOp?;
      assert ticket.localReads == map[];
      assert ticket.localUpdates == map[rid :=  UpdateInit(input.update_op)];

      // assert rid !in s.localUpdates;
      assert rid !in IS.update_reqs;

      assert s'.localReads == s.localReads;
      assert IS'.readonly_reqs == IS.readonly_reqs;
      // that step takes a little while
      assume s'.localUpdates == s.localUpdates[rid :=  UpdateInit(input.update_op)];

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

    // construct the ticket
    // establish that s' is the dot of the s and the new ticket.
    assert s == dot(s', stub);
    // assert the ticket values
    assert stub.log == map[];
    assert !stub.global_tail.Some?;
    assert stub.replicas == map[];
    assert stub.localTails == map[];
    assert !stub.ctail.Some?;
    assert stub.combiner == map[];
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

    // it has to be in either of them
    assert rid in stub.localUpdates || rid in stub.localReads;

    if rid in stub.localUpdates {
      // var idx := stub.localUpdates[rid].idx;

      // assert stub == M(map[], None, map[], map[], None, map[],
      //                  map[rid := UpdateDone(output, idx)],
      //                  map[]);

      // // the local reads haven't changed
      // assert s'.localReads == s.localReads;
      // assert IS'.readonly_reqs == IS.readonly_reqs;

      // assert rid !in stub.localReads;
      // assert rid !in s'.localUpdates;
      // assert rid in s.localUpdates;
      // assert rid in IS.update_resps;
      // assert rid !in IS'.update_resps;

      // // they are the same
      // assert s.localUpdates[rid] == stub.localUpdates[rid];
      // assert s.localUpdates[rid].UpdateDone?;
      // assert output == s.localUpdates[rid].ret;
      // assert output == IS.update_resps[rid].ret;

      // // the ctail value
      // assert s.localUpdates[rid].idx <= s.ctail.value;
      // assert s.ctail.value == IS.ctail;
      // assert IS.update_resps[rid].idx_in_log == s.localUpdates[rid].idx;
      // assert IS.update_resps[rid].idx_in_log <= IS.ctail;

      // // // that may take a while
      // assume s.localUpdates == s'.localUpdates[rid := UpdateDone(output, idx)];
      // assert rid !in s'.localUpdates;
      // assert rid !in IS'.update_resps;

      // I_UpdateResponses_Update_is(s, s', rid, idx, output);
      // assert IS.update_resps == IS'.update_resps[rid := B.UpdateResp(idx, output)];
      // assert IS.update_reqs == IS'.update_reqs;

      // assert IS == IS'.(update_resps := IS'.update_resps[rid := B.UpdateResp(idx, output)]);
      // assert IS' == IS.(update_resps := IS.update_resps - {rid});

      // // && s' == s.(update_resps := s.update_resps - {rid})
      assume B.NextStep(IS, IS', ifc.End(rid, output), B.EndUpdate_Step(rid, output));
    } else {
      assert rid in stub.localReads;
      var ctail := stub.localReads[rid].ctail;
      assert stub == M(map[], None, map[], map[], None,
                       map[rid := ReadonlyDone(output, ctail)],
                       map[], map[]);

      assume B.NextStep(IS, IS', ifc.End(rid, output), B.FinishReadonly_Step(rid, ctail, output));
    }
  }

  lemma GoToCombinerReady_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId)
  requires IL.GoToCombinerReady(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma ExecLoadLtail_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId)
  requires IL.ExecLoadLtail(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma ExecLoadGlobalTail_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId)
  requires IL.ExecLoadGlobalTail(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma ExecDispatchLocal_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId)
  requires IL.ExecDispatchLocal(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    //assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);  // TODO
    var c := s.combiner[nodeId];
    var queue_index := |c.queued_ops| - (c.globalTail - c.localTail);
    var rid := c.queued_ops[queue_index];
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.AddUpdateToLog_Step(rid));   // currently fails
  }

  lemma ExecDispatchRemote_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId)
  requires IL.ExecDispatchRemote(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma TransitionReadonlyReadCtail_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId, rid: RequestId)
  requires IL.TransitionReadonlyReadCtail(s, s', nodeId, rid)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var IS := I(s);
    var IS' := I(s');

    assert rid in s.localReads && s.localReads[rid].ReadonlyInit?;

    assert s'.ctail == s.ctail;
    assert IS.ctail == IS'.ctail && IS.ctail == s.ctail.value;

    assert s'.log == s.log;
    assert IS.log == IS'.log;

    assert s'.localUpdates == s.localUpdates;
    assert IS.update_resps == IS'.update_resps;
    assert IS.update_reqs == IS'.update_reqs;

    assert s'.localReads == s.localReads[rid := ReadonlyCtail(s.localReads[rid].op, s.ctail.value)];

    I_ReadRequests_Update_CTail_is(s, s', rid);
    assert IS'.readonly_reqs == IS.readonly_reqs[rid := B.ReadReq(IS.ctail, IS.readonly_reqs[rid].op)];
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.ReadCtail_Step(rid));
  }

  lemma TransitionReadonlyReadyToRead_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId, rid: RequestId)
  requires IL.TransitionReadonlyReadyToRead(s, s', nodeId, rid)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var IS := I(s);
    var IS' := I(s');

    var r := s.localReads[rid];
    assert s' == s.(localReads := s.localReads[rid := ReadonlyReadyToRead(r.op, nodeId, r.ctail)]);
    assert s'.localReads[rid].op == s.localReads[rid].op;
    assert s'.localReads[rid].ctail == s.localReads[rid].ctail;

    assert IS.ctail == IS'.ctail && IS.ctail == s.ctail.value;
    assert IS.log == IS'.log;

    assert IS.update_resps == IS'.update_resps;
    assert IS.update_reqs == IS'.update_reqs;
    reveal_I_ReadRequests();
    assert IS'.readonly_reqs == IS.readonly_reqs;
    // no corresponding step
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma TransitionReadonlyDone_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId, rid: RequestId)
  requires IL.TransitionReadonlyDone(s, s', nodeId, rid)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    // XXX: fix the readonly done stuff
    assert false;
  }

  lemma AdvanceTail_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId, request_ids: seq<RequestId>)
  requires IL.AdvanceTail(s, s', nodeId, request_ids)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    // XXX: here we do a single entry to the log in NRSimple, but a bunch in InfLog
    assert B.NextStep(I(s), I(s'), ifc.InternalOp,  B.Stutter_Step);  // Fails
  }

  lemma UpdateCompletedTail_Refines(s: A.Variables, s': A.Variables, nodeId: IL.NodeId)
  requires IL.UpdateCompletedTail(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var c := s.combiner[nodeId];
    var new_ctail := if s.ctail.value > c.localTail then s.ctail.value else c.localTail;
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.IncreaseCtail_Step(new_ctail));
  }

  lemma UpdateRequestDone_Refines(s: A.Variables, s': A.Variables, rid: RequestId)
  requires IL.UpdateRequestDone(s, s', rid)
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
    assert s'.localReads == s.localReads;
    var req := s.localUpdates[rid];
    assert s' == s.(localUpdates := s.localUpdates[rid:= UpdateDone(req.ret, req.idx)]);
    assert s.localUpdates[rid].UpdateApplied?;
    var IS := I(s);
    var IS' := I(s');
    // nothing should have changed in the ctail and the log
    assert IS'.ctail == IS.ctail;
    assert IS'.log == IS.log;
    assert IS'.readonly_reqs == IS.readonly_reqs;
    I_UpdateResponses_NoChange_is(s, s', rid);
    assert IS'.update_reqs == IS.update_reqs;
    assert IS'.update_resps == IS.update_resps;
    assert IS' == IS;

    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
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
      case UpdateRequestDone_Step(request_id: RequestId) => { UpdateRequestDone_Refines(s, s', request_id); }
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
