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

  // TODO(gz): reuse map_update from InfiniteLog.i.dfy
  function map_union<K,V>(m1: map<K,V>, m2: map<K,V>) : map<K,V> {
    map k | k in m1.Keys + m2.Keys ::
        (if k in m1.Keys then m1[k] else m2[k])
  }

  function I(s: A.Variables) : B.Variables
  //requires Inv(s) 
  {
    B.Variables(
      seq(s.global_tail.value, i requires 0 <= i && i < s.global_tail.value => s.log[i].op), 
      // [], Inv_LogEntriesGlobalTail
      s.ctail.value,
      // readonly_reqs - ReadReq(ctail_at_start: nat, op: nrifc.ReadonlyOp)
      // TODO(travis): change NRCtail so it has states without ctail (corresponds to NrInfinite)
      map rid | && rid in s.localReads
                && (s.localReads[rid].ReadonlyCtail? || s.localReads[rid].ReadonlyReadyToRead?)
        :: B.ReadReq(s.localReads[rid].ctail, s.localReads[rid].op),
      // update_reqs - UpdateResp(idx_in_log: nat, ret: nrifc.ReturnType)
      map_union(
        (map rid: nat | && rid in s.localUpdates 
                   && s.localUpdates[rid].UpdateInit?
        :: s.localUpdates[rid].op),
        (map rid: nat | && rid in s.localUpdates 
                   && s.localUpdates[rid].UpdatePlaced?
        :: s.log[s.localUpdates[rid].idx].op)
      ),
      // update_resps - UpdateResp(idx_in_log: nat, ret: nrifc.ReturnType)
      map rid | && rid in s.localUpdates
          && s.localUpdates[rid].UpdateApplied?
          :: B.UpdateResp(s.localUpdates[rid].idx, s.localUpdates[rid].ret)
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
    if input.ROp? {
      assert s'.replicas == s.replicas;
      assert s'.localTails == s.localTails;
      assert s'.ctail == s.ctail;
      assert s.ctail.Some?;

      assert rid in s'.localReads;
      assert rid !in s.localReads;

      assert s'.combiner == s.combiner;
      assert s'.localUpdates == s.localUpdates;

      // Some attempts at trying to convince dafny to believe me:
      assert (forall r | r in s.localReads && r != rid :: r in s'.localReads);
      assert (forall k | k in s.localReads && k != rid :: k in s'.localReads && s.localReads[k] == s'.localReads[k]);
      assert (forall k | k in s'.localReads && k != rid :: k in s.localReads && s.localReads[k] == s'.localReads[k]);

      // TODO: Doesn't believe this:
      assert |s'.localReads| == |s.localReads| + 1;
      assert s'.localReads == s.localReads[rid := ReadonlyCtail(input.readonly_op, s.ctail.value)];
    }
    else {
      assume false;
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
