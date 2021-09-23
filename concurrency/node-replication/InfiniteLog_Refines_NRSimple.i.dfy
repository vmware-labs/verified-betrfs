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
        IL.ConsumeStubPreservesInv(s, s', rid, output);
      }
      case InternalOp => {
        var shard, shard', rest :| A.InternalNext(s, s', shard, shard', rest);
        IL.InternalPreservesInv(shard, shard', rest);
      }
    }
  }

  function map_union<K,V>(m1: map<K,V>, m2: map<K,V>) : map<K,V> {
    map k | k in m1.Keys + m2.Keys ::
        (if k in m1.Keys then m1[k] else m2[k])
  }

  function I(s: A.Variables) : B.Variables
  //requires Inv(s) 
  {
    B.Variables(
      seq(s.global_tail.value, i requires 0 <= i && i < s.global_tail.value => s.log[i].op), 
      // [], TODO(travis): add this to Inv()
      s.ctail.value,
      // readonly_reqs - ReadReq(ctail_at_start: nat, op: nrifc.ReadonlyOp)
      // TODO(travis): change NRCtail so it has states without ctail (corresponds to NrInfinite)
      map rid | && rid in s.localReads
                && (s.localReads[rid].ReadonlyCtail? || s.localReads[rid].ReadonlyReadyToRead?)
        :: B.ReadReq(s.localReads[rid].ctail, s.localReads[rid].op),
      // update_reqs - UpdateResp(idx_in_log: nat, ret: nrifc.ReturnType)
      map_union(
        (map rid | && rid in s.localUpdates 
                   && s.localUpdates[rid].UpdateInit?
        :: s.localUpdates[rid].op),
        (map rid | && rid in s.localUpdates 
                   && s.localUpdates[rid].UpdatePlaced?
        :: s.log[s.localUpdates[rid].idx].op)
      ),
      // update_resps - UpdateResp(idx_in_log: nat, ret: nrifc.ReturnType)
      // TODO(travis): add idx_in_log here too?
      map rid | && rid in s.localUpdates
                && s.localUpdates[rid].UpdateDone?
        :: B.UpdateResp(0, s.localUpdates[rid].ret)
    )
  }

  lemma InitRefinesInit(s: A.Variables)
  //requires A.Init(s)
  //requires Inv(s)
  ensures B.Init(I(s))

  lemma NewTicket_Refines_Start(s: A.Variables, s': A.Variables,
      rid: RequestId, input: nrifc.Input)
  requires IL.NewTicket(s, s', rid, input)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.Start(rid, input))
  {
    // refine StartUpdate or StartReadonly
  }

  lemma ConsumeStub_Refines_End(s: A.Variables, s': A.Variables,
      rid: RequestId, output: nrifc.Output)
  requires IL.ConsumeStub(s, s', rid, output)
  requires Inv(s)
  requires Inv(s')
  ensures B.Next(I(s), I(s'), ifc.End(rid, output))
  {
    // refine EndUpdate or EndReadonly
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
        ConsumeStub_Refines_End(s, s', rid, output);
      }
      case InternalOp => {
        var shard, shard', rest :| A.InternalNext(s, s', shard, shard', rest);
        InternalMonotonic(shard, shard', rest);
        Internal_Refines_Internal(s, s');
      }
    }
  }
}
