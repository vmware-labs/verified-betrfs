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
    ensures (m1.Keys !! m2.Keys) ==> map_update(m1, m2).Keys == m1.Keys + m2.Keys
    ensures (m1.Keys !! m2.Keys) ==> (forall k | k in m1 :: map_update(m1, m2)[k] == m1[k])
    ensures (m1.Keys !! m2.Keys) ==> (forall k | k in m2 :: map_update(m1, m2)[k] == m2[k])
  {
    map k | k in (m1.Keys + m2.Keys) :: if k in m2 then m2[k] else m1[k]
  }

  lemma map_update_commutative<K(!new), V>(m1: map<K, V>, m2: map<K, V>)
    requires m1.Keys !! m2.Keys
    ensures map_update(m1, m2) == map_update(m2, m1)
  {
  }

  lemma map_update_associative<K(!new), V>(m1: map<K, V>, m2: map<K, V>, m3: map<K, V>)
    requires m1.Keys !! m2.Keys && m2.Keys !! m3.Keys && m3.Keys !! m1.Keys
    ensures map_update(m1, map_update(m2, m3)) == map_update(map_update(m1, m2), m3)
  {
  }

  // construction of the read requests for InfiniteLog -> NRSimple
  function {:opaque} I_ReadRequests(reqs: map<RequestId, ReadonlyState>) : (res :map<RequestId, B.ReadReq>)
  {
    map rid | rid in reqs ::
      if reqs[rid].ReadonlyInit? then B.ReadInit(reqs[rid].op) else B.ReadReq(reqs[rid].ctail, reqs[rid].op)
  }

  // predicate to filter in-progress update requests
  predicate UpdateRequests_InProgress(rid: RequestId, lupd: map<RequestId, UpdateState>)
  {
    && rid in lupd
    && (lupd[rid].UpdateInit? )
  }

  // construction of the update requests for InfiniteLog -> NRSimple
  function {:opaque} I_UpdateRequests(lupd: map<RequestId, UpdateState>,  log: map<nat, LogEntry>) : (res : map<RequestId, nrifc.UpdateOp>)
    requires forall rid | rid in lupd && (lupd[rid].UpdatePlaced? || lupd[rid].UpdateApplied?) :: lupd[rid].idx in log
  {
    map rid | rid in lupd && UpdateRequests_InProgress(rid, lupd) ::
      (if lupd[rid].UpdateInit? then lupd[rid].op else log[lupd[rid].idx].op)
  }

  // predicate to filter completed update requests
  predicate UpdateRequests_Done(rid: RequestId, lupd: map<RequestId, UpdateState>)
  {
    && rid in lupd
    && (lupd[rid].UpdateDone? || lupd[rid].UpdatePlaced? || lupd[rid].UpdateApplied?)
  }

  // construction of the update responses for InfiniteLog -> NRSimple
  function {:opaque} I_UpdateResponses(lupd: map<RequestId, UpdateState>) : (res : map<RequestId, B.UpdateResp>)
  {
    map rid | rid in lupd && UpdateRequests_Done(rid, lupd) :: B.UpdateResp(lupd[rid].idx)
  }

  function {:opaque} I_Log(gtail: nat, log: map<nat, LogEntry>) : seq<nrifc.UpdateOp>
    requires forall i | 0 <= i < gtail :: i in log
  {
    seq(gtail, i requires 0 <= i < gtail => log[i].op)
  }


  lemma I_Added_LocalRead_is(s: A.Variables, s': A.Variables, rid: RequestId, input: nrifc.Input)
    requires Inv(s)
    requires input.ROp?
    requires s' == s.(localReads := s.localReads[rid := ReadonlyInit(input.readonly_op)])
    ensures I(s') == I(s).(readonly_reqs := I(s).readonly_reqs[rid := B.ReadInit(input.readonly_op)])
  {
    reveal_I_ReadRequests();
    assert I(s').readonly_reqs == I(s).readonly_reqs[rid := B.ReadInit(input.readonly_op)];
  }

  lemma I_Removed_LocalReads_is(s: A.Variables, s': A.Variables, rid: RequestId)
    requires Inv(s)
    requires s' == s.(localReads := s.localReads - {rid})
    ensures I(s') == I(s).(readonly_reqs := I(s).readonly_reqs - {rid})
  {
    reveal_I_ReadRequests();
    assert I(s').readonly_reqs == I(s).readonly_reqs - {rid};
  }

  lemma I_LocalReads_CtailRead(s: A.Variables, s': A.Variables, rid: RequestId, op: nrifc.ReadonlyOp)
    requires Inv(s)
    requires s' == s.(localReads := s.localReads[rid := ReadonlyCtail(op, s.ctail.value)])
    ensures I(s') == I(s).(readonly_reqs := I(s).readonly_reqs[rid := B.ReadReq(I(s).ctail, op)])
  {
    reveal_I_ReadRequests();
    assert I(s').readonly_reqs == I(s).readonly_reqs[rid := B.ReadReq(I(s).ctail, op)];
  }

  lemma I_LocalReads_ReadOnlyDone(s: A.Variables, s': A.Variables, rid: RequestId, ret: nrifc.ReturnType)
    requires Inv(s)
    requires Inv(s')
    requires rid in s.localReads && s.localReads[rid].ReadonlyReadyToRead?
    requires s' == s.(localReads := s.localReads[rid := ReadonlyDone(s.localReads[rid].op, ret, s.localReads[rid].nodeId, s.localReads[rid].ctail)])
    ensures I(s').readonly_reqs == I(s).readonly_reqs
  {
    reveal_I_ReadRequests();
  }

  lemma I_Removed_LocalUpdates_is(s: A.Variables, s': A.Variables, rid: RequestId)
    requires Inv(s)
    requires Inv(s')
    requires s' == s.(localUpdates := s.localUpdates - {rid})
    requires rid in s.localUpdates && s.localUpdates[rid].UpdateDone?
    ensures I(s') == I(s).(update_resps := I(s).update_resps - {rid})
  {
    reveal_I_UpdateRequests();
    assert I(s').update_reqs == I(s).update_reqs;
    reveal_I_UpdateResponses();
    assert I(s').update_resps == I(s).update_resps - {rid};
  }

  lemma I_Added_LocalUpdate_is(s: A.Variables, s': A.Variables, rid: RequestId, input: nrifc.Input)
    requires Inv(s)
    requires Inv(s')
    requires rid !in s.localUpdates;
    requires input.UOp?
    requires s' == s.(localUpdates := s.localUpdates[rid := UpdateInit(input.update_op)])
    ensures I(s') == I(s).(update_reqs := I(s).update_reqs[rid := input.update_op])
  {
    reveal_I_UpdateRequests();
    assert I(s').update_reqs == I(s).update_reqs[rid := input.update_op];
    reveal_I_UpdateResponses();
    assert I(s').update_resps == I(s).update_resps;
  }

  lemma I_LocalUpdates_UpdateApplied(lupd: map<RequestId, UpdateState>, lupd': map<RequestId, UpdateState>, log: map<nat, LogEntry>, rid: RequestId, idx: nat, ret: nrifc.ReturnType)
    requires lupd' == lupd[rid := UpdateApplied(ret, idx)];
    requires rid in lupd && lupd[rid].UpdatePlaced? && lupd[rid].idx == idx;

    // to make I_Update_Responses Happy
    requires forall rid | rid in lupd && (lupd[rid].UpdatePlaced? || lupd[rid].UpdateApplied?) :: lupd[rid].idx in log
    requires forall rid | rid in lupd && (lupd'[rid].UpdatePlaced? || lupd'[rid].UpdateApplied?) :: lupd'[rid].idx in log
    ensures I_UpdateResponses(lupd) == I_UpdateResponses(lupd')
    ensures I_UpdateRequests(lupd, log) == I_UpdateRequests(lupd', log)
  {
    assert I_UpdateResponses(lupd) == I_UpdateResponses(lupd') by {
      reveal_I_UpdateResponses();
    }

    assert I_UpdateRequests(lupd, log) == I_UpdateRequests(lupd', log) by {
      reveal_I_UpdateRequests();
    }
  }

  lemma I_LocalUpdates_UpdateDone(s: A.Variables, s': A.Variables, rid: RequestId, idx: nat, ret: nrifc.ReturnType)
    requires Inv(s)
    requires Inv(s')
    requires rid in s.localUpdates && s.localUpdates[rid].UpdateApplied?
    requires s.localUpdates[rid].idx == idx;
    requires s' == s.(localUpdates := s.localUpdates[rid:= UpdateDone(ret, idx)]);
    ensures I(s').update_reqs == I(s).update_reqs;
    ensures I(s').update_resps == I(s).update_resps;
  {
      assert I(s').update_reqs == I(s).update_reqs  by {
        reveal_I_UpdateRequests();
      }
      assert I(s').update_resps == I(s).update_resps by {
        assert UpdateRequests_Done(rid, s.localUpdates);
        assert s.localUpdates[rid].idx == idx;
        reveal_I_UpdateResponses();
      }
  }

  lemma I_UpdateResponses_update_map_commute(lupd_old : map<RequestId, UpdateState>, lupd_new: map<RequestId, UpdateState>)
    requires forall r | r in lupd_new :: lupd_new[r].UpdatePlaced?
    ensures I_UpdateResponses(map_update(lupd_old, lupd_new))
              == map_update(I_UpdateResponses(lupd_old), I_UpdateResponses(lupd_new))
  {
    assert forall r | r in lupd_new :: r in I_UpdateResponses(lupd_new) by {
      reveal_I_UpdateResponses();
    }
    reveal_map_update();
    reveal_I_UpdateResponses();
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

  lemma NewTicket_Refines_Start_read(
      s: A.Variables, s': A.Variables, rid: RequestId, input: nrifc.Input)
  requires Inv(s)
  requires input.ROp?
  requires s' == s.(localReads := s.localReads[rid := ReadonlyInit(input.readonly_op)])
  requires rid !in s.localReads
  requires rid !in s.localUpdates
  requires rid !in CombinerRequestIds(s)
  ensures Inv(s')
  ensures B.Next(I(s), I(s'), ifc.Start(rid, input))
  {
    reveal_I_ReadRequests();
    reveal_I_UpdateRequests();
    reveal_I_UpdateResponses();

    var step := B.StartReadonly_Step(rid, input.readonly_op);
    assert B.NextStep(I(s), I(s'), ifc.Start(rid, input), step) by {
      assert B.StartReadonly(I(s), I(s'), rid,  input.readonly_op);
    }
  }


  lemma NewTicket_Refines_Start_update(
      s: A.Variables, s': A.Variables, rid: RequestId, input: nrifc.Input)
  requires Inv(s)
  requires input.UOp?
  requires s' == s.(localUpdates := s.localUpdates[rid := UpdateInit(input.update_op)])
  requires rid !in s.localReads
  requires rid !in s.localUpdates
  requires rid !in CombinerRequestIds(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.Start(rid, input))
  {
    reveal_I_ReadRequests();
    reveal_I_UpdateRequests();
    reveal_I_UpdateResponses();
    I_Added_LocalUpdate_is(s, s', rid, input);

    var step := B.StartUpdate_Step(rid, input.update_op);
    assert B.NextStep(I(s), I(s'), ifc.Start(rid, input), step) by {
      assert B.StartUpdate(I(s), I(s'), rid,  input.update_op);
    }
  }

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
    if input.ROp? {
      NewTicket_Refines_Start_read(s, s', rid, input);
    } else {
      NewTicket_Refines_Start_update(s, s', rid, input);
    }
  }

  lemma ConsumeStub_Refines_End_LocalReads(s: A.Variables, s': A.Variables,
      rid: RequestId, output: nrifc.Output, stub: M)
    requires IL.ConsumeStub(s, s', rid, output, stub)
    requires rid in stub.localReads
    requires s.M?
    ensures s' == s.(localReads := s.localReads - {rid})
  {
  }

  lemma ConsumeStub_Refines_End_LocalUpdates(s: A.Variables, s': A.Variables,
      rid: RequestId, output: nrifc.Output, stub: M)
    requires IL.ConsumeStub(s, s', rid, output, stub)
    requires rid in stub.localUpdates
    requires s.M?
    ensures s' == s.(localUpdates := s.localUpdates - {rid})
  {
  }

  predicate VersionInLog(log: map<nat, LogEntry>, version: nat)
  {
    forall i | 0 <= i < version :: i in log
  }

  predicate OutputMatch(log: map<nat, LogEntry>,  output: nrifc.Output, version: nat, op: nrifc.ReadonlyOp)
    requires VersionInLog(log, version)
  {
     output == nrifc.read(state_at_version(log, version), op)
  }

  lemma {:induction true} ConsumeStub_Refines_End_state_at_version(s_log: seq<nrifc.UpdateOp>, i_log: map<nat, LogEntry>, gtail: nat, idx:nat)
    requires forall i | 0 <= i < gtail :: i in i_log
    requires 0 <= idx <= |s_log|
    requires idx <= gtail
    requires s_log == I_Log(gtail, i_log);
    ensures B.state_at_version(s_log, idx) == state_at_version(i_log, idx)
  {
    reveal_I_Log();
  }

  lemma ConsumeStub_Refines_End(s: A.Variables, s': A.Variables,
      rid: RequestId, output: nrifc.Output, stub: M)
  requires IL.ConsumeStub(s, s', rid, output, stub)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.End(rid, output))
  {
    if rid in stub.localUpdates {

      assert I(s') == I(s).(update_resps := I(s).update_resps - {rid}) by {
        ConsumeStub_Refines_End_LocalUpdates(s, s', rid, output, stub);
        I_Removed_LocalUpdates_is(s, s', rid);
      }

      assert rid in I(s).update_resps by {
        reveal_I_UpdateResponses();
      }
      var idx := I(s).update_resps[rid].idx_in_log;

      assert idx == s.localUpdates[rid].idx by {
        reveal_I_UpdateResponses();
      }

      assert idx < |I(s).log| by {
        reveal_I_Log();
      }

      assert output == nrifc.update(B.state_at_version(I(s).log, idx), I(s).log[idx]).return_value by {
        assert output == nrifc.update(state_at_version(s.log, idx), s.log[idx].op).return_value;
        reveal_I_Log();
        assert s.log[idx].op ==  I(s).log[idx];
        ConsumeStub_Refines_End_state_at_version(I(s).log, s.log, s.global_tail.value, idx);
      }

      assert exists step :: B.NextStep(I(s), I(s'), ifc.End(rid, output), step) by {
        var step := B.EndUpdate_Step(rid, output);
        assert B.NextStep(I(s), I(s'), ifc.End(rid, output), step) by {
          assert B.EndUpdate(I(s), I(s'), rid,  output);
        }
      }

    } else {

      assert rid in stub.localReads;
      assert rid in s.localReads;

      assert I(s') == I(s).(readonly_reqs := I(s).readonly_reqs - {rid}) by {
        ConsumeStub_Refines_End_LocalReads(s, s', rid, output, stub);
        I_Removed_LocalReads_is(s, s', rid);
      }


      assert rid in I(s).readonly_reqs && I(s).readonly_reqs[rid].ReadReq? by {
        reveal_I_ReadRequests();
      }

      assert I(s).readonly_reqs[rid].ctail_at_start == s.localReads[rid].ctail by {
        reveal_I_ReadRequests();
      }

      assert exists version : nat | s.localReads[rid].ctail <= version <= s.ctail.value
        :: VersionInLog(s.log, version) && OutputMatch(s.log, output, version,  s.localReads[rid].op) by {
        assert output ==  s.localReads[rid].ret;
        var v :| s.localReads[rid].ctail <= v <= s.ctail.value && (s.localReads[rid].ret == nrifc.read(state_at_version(s.log, v),  s.localReads[rid].op));
        assert OutputMatch(s.log, output, v,  s.localReads[rid].op);
      }
      var version : nat :| s.localReads[rid].ctail<= version <= s.ctail.value  && VersionInLog(s.log, version) && OutputMatch(s.log, output, version,  s.localReads[rid].op);

      assert version <= I(s).ctail;

      assert I(s).readonly_reqs[rid].ctail_at_start <= version <= |I(s).log| by {
          reveal_I_Log();
          assert |I(s).log| == s.global_tail.value;
          reveal_I_ReadRequests();
          assert I(s).readonly_reqs[rid].ctail_at_start <= I(s).ctail;
          assert I(s).ctail <= |I(s).log|;
          assert version <= |I(s).log|;
      }

      assert output == nrifc.read(B.state_at_version(I(s).log, version), I(s).readonly_reqs[rid].op) by {
          // assert version <= s.ctail.value;
          assert output == nrifc.read(state_at_version(s.log, version),s.localReads[rid].op);
          reveal_I_Log();
          assert I(s).readonly_reqs[rid].op == s.localReads[rid].op by {
            reveal_I_ReadRequests();
          }
          ConsumeStub_Refines_End_state_at_version(I(s).log, s.log, s.global_tail.value, version);
      }

      assert exists step :: B.NextStep(I(s), I(s'), ifc.End(rid, output), step) by {
        var step := B.FinishReadonly_Step(rid, version, output);
        assert B.NextStep(I(s), I(s'), ifc.End(rid, output), step) by {
          assert B.FinishReadonly(I(s), I(s'), rid, version, output);
        }
      }
    }
  }

  lemma GoToCombinerReady_Refines(s: A.Variables, s': A.Variables, nodeId: nat)
  requires IL.GoToCombinerReady(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma ExecLoadLtail_Refines(s: A.Variables, s': A.Variables, nodeId: nat)
  requires IL.ExecLoadLtail(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma ExecLoadGlobalTail_Refines(s: A.Variables, s': A.Variables, nodeId: nat)
  requires IL.ExecLoadGlobalTail(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma ExecDispatchLocal_Refines(s: A.Variables, s': A.Variables, nodeId: nat)
  requires IL.ExecDispatchLocal(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var c := s.combiner[nodeId];
    var UpdateResult(nr_state', ret) := nrifc.update(s.replicas[nodeId], s.log[c.localTail].op);
    var queue_index := c.queueIndex;
    var request_id := c.queued_ops[queue_index];
    var idx :=  s.localUpdates[request_id].idx;

    I_LocalUpdates_UpdateApplied(s.localUpdates, s'.localUpdates, s.log, request_id, idx, ret);
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma ExecDispatchRemote_Refines(s: A.Variables, s': A.Variables, nodeId: nat)
  requires IL.ExecDispatchRemote(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma TransitionReadonlyReadCtail_Refines(s: A.Variables, s': A.Variables, rid: RequestId)
  requires IL.TransitionReadonlyReadCtail(s, s', rid)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {

    var op := s.localReads[rid].op;

    assert rid in I(s).readonly_reqs && I(s).readonly_reqs[rid].ReadInit? by {
      reveal_I_ReadRequests();
    }

    assert op == I(s).readonly_reqs[rid].op by {
      reveal_I_ReadRequests();
    }

    assert s' == s.(localReads := s.localReads[rid := ReadonlyCtail(op, s.ctail.value)]);
    I_LocalReads_CtailRead(s, s', rid, op);
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.ReadCtail_Step(rid));
  }

  lemma TransitionReadonlyReadyToRead_Refines(s: A.Variables, s': A.Variables, nodeId: nat, rid: RequestId)
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

  lemma TransitionReadonlyDone_Refines(s: A.Variables, s': A.Variables, nodeId: nat, rid: RequestId)
  requires IL.TransitionReadonlyDone(s, s', nodeId, rid)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var req := s.localReads[rid];
    var ret := nrifc.read(s.replicas[req.nodeId], req.op);
    I_LocalReads_ReadOnlyDone(s, s', rid, ret);
    assert B.NextStep(I(s), I(s'), ifc.InternalOp,  B.Stutter_Step);
  }

  lemma TrivialStart_Refines(s: A.Variables, s': A.Variables, nodeId: nat)
   requires IL.TrivialStart(s, s', nodeId)
   requires Inv(s)
   requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert I(s) == I(s');
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }

  lemma AdvanceTail_Refines(s: A.Variables, s': A.Variables, nodeId: nat, request_ids: seq<RequestId>)
   requires IL.AdvanceTail(s, s', nodeId, request_ids)
   requires Inv(s)
   requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    // establish the pre-condition
    assert B.RequestIdsValid(request_ids, I(s).update_reqs) by {
      reveal_I_UpdateRequests();
    }

    var new_log_entries := B.ConstructNewLogEntries(request_ids, I(s).update_reqs);
    assert I(s').log == I(s).log + new_log_entries by {
      var updated_log := ConstructNewLogEntries(request_ids, nodeId, s.global_tail.value, s.localUpdates);

      assert forall r | r in request_ids :: I(s).update_reqs[r] == s.localUpdates[r].op by {
        reveal_I_UpdateRequests();
      }

      assert forall i | 0 <= i < |request_ids| :: new_log_entries[i] == updated_log[LogIdx(s.global_tail.value, i)].op
      by {
        reveal_ConstructNewLogEntries();
      }

      assert I(s').log == I_Log(s'.global_tail.value, map_update(s.log, updated_log)) by {
        reveal_I_Log();
      }

      ConstructNewLogEntries_InMap(request_ids, nodeId, s.global_tail.value, s.localUpdates, updated_log);
      reveal_I_Log();
    }

    assert I(s').update_reqs == B.map_filter(I(s).update_reqs, request_ids) by {
      var local_updates_new := ConstructLocalUpdateMap(request_ids, nodeId, s.global_tail.value);
      assert s'.localUpdates == map_update(s.localUpdates, local_updates_new);
      ConstructLocalUpdateMap_InMap(request_ids, nodeId, s.global_tail.value, local_updates_new);

      reveal_I_UpdateRequests();
      B.reveal_map_filter();
    }

    var new_responses := B.ConstructUpdateResponses(request_ids, |I(s).log|);
    assert I(s').update_resps == B.map_update(I(s).update_resps, new_responses) by {
      var local_updates_new := ConstructLocalUpdateMap(request_ids, nodeId, s.global_tail.value);
      assert s'.localUpdates == map_update(s.localUpdates, local_updates_new);

      assert I(s').update_resps  == I_UpdateResponses(s'.localUpdates) by {
        reveal_I_UpdateResponses();
      }

      assert |I(s).log| == s.global_tail.value by {
          reveal_I_Log();
        }

      assert new_responses == I_UpdateResponses(local_updates_new) by {
        reveal_I_UpdateResponses();
        B.ConstructUpdateResponses_in_map(request_ids, |I(s).log|, new_responses);
        ConstructLocalUpdateMap_InMap(request_ids, nodeId, s.global_tail.value, local_updates_new);
      }

      assert I_UpdateResponses(map_update(s.localUpdates, local_updates_new))
                == map_update(I_UpdateResponses(s.localUpdates), I_UpdateResponses(local_updates_new))
      by {
        ConstructLocalUpdateMap_InMap(request_ids, nodeId, s.global_tail.value, local_updates_new);
        I_UpdateResponses_update_map_commute(s.localUpdates, local_updates_new);
      }

      assert map_update(I(s).update_resps, new_responses) == B.map_update(I(s).update_resps, new_responses) by {
        reveal_map_update();
        B.reveal_map_update();
      }
    }

    assert exists step :: B.NextStep(I(s), I(s'), ifc.InternalOp, step) by {
      assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.AddUpdateToLog_Step(request_ids)) by {
        assert B.AddUpdateToLog(I(s), I(s'), request_ids);
      }
    }
  }

  lemma UpdateCompletedTail_Refines(s: A.Variables, s': A.Variables, nodeId: nat)
  requires IL.UpdateCompletedTail(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var c := s.combiner[nodeId];
    var new_ctail := if s.ctail.value > c.localTail then s.ctail.value else c.localTail;

    assert I(s).ctail <= new_ctail <= |I(s).log| by {
      reveal_I_Log();
    }
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.IncreaseCtail_Step(new_ctail));
  }

  lemma UpdateCompletedNoChange_Refines(s: A.Variables, s': A.Variables, nodeId: nat)
  requires IL.UpdateCompletedNoChange(s, s', nodeId)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    assert B.NextStep(I(s), I(s'), ifc.InternalOp, B.Stutter_Step);
  }


  lemma UpdateRequestDone_Refines(s: A.Variables, s': A.Variables, rid: RequestId)
  requires IL.UpdateRequestDone(s, s', rid)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.InternalOp)
  {
    var req := s.localUpdates[rid];
    assert s' == s.(localUpdates := s.localUpdates[rid:= UpdateDone(req.ret, req.idx)]);
    I_LocalUpdates_UpdateDone(s, s', rid, req.idx, req.ret);
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
      case TransitionReadonlyReadCtail_Step(rid) => { TransitionReadonlyReadCtail_Refines(s, s', rid); }
      case TransitionReadonlyReadyToRead_Step(nodeId, rid) => { TransitionReadonlyReadyToRead_Refines(s, s', nodeId, rid); }
      case TransitionReadonlyDone_Step(nodeId, rid) => { TransitionReadonlyDone_Refines(s, s', nodeId, rid); }
      case TrivialStart_Step(nodeId) => { TrivialStart_Refines(s, s', nodeId); }
      case AdvanceTail_Step(nodeId, request_ids) => { AdvanceTail_Refines(s, s', nodeId, request_ids); }
      case UpdateCompletedTail_Step(nodeId) => { UpdateCompletedTail_Refines(s, s',nodeId); }
      case UpdateRequestDone_Step(request_id: RequestId) => { UpdateRequestDone_Refines(s, s', request_id); }
      case UpdateCompletedNoChange_Step(nodeId) => { UpdateCompletedNoChange_Refines(s, s',nodeId); }
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
