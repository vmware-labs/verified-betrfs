include "../framework/AsyncSSM.s.dfy"
include "NRSpec.s.dfy"
include "../../lib/Base/Option.s.dfy"

module InfiniteLogSSM(nrifc: NRIfc) refines TicketStubSSM(nrifc) {
  import opened Options

  // Read (node i):
  //
  //   c <- Read ctail
  //   while tail(i) <= c:
  //      advance replica i (or wait)
  //   read from replica
  //
  // Write (node i):
  //
  //   reserve entries, add them to log
  //   apply all entries (update replica) (update local tail to the end of the entries)
  //   update ctail

  type NodeId = nat

  // `ReadonlyState` and `UpdateState` tokens can appear at any point time
  // (corresponding to a client beginning a read or an update, respectively).
  //
  // Note that an `UpdateState` may start on one thread (the thread making the
  // update request), and then transfer to another thread on the same node
  // (the combining thread), and then transfer back once it is done.

  datatype ReadonlyState =
    | ReadonlyInit(op: nrifc.ReadonlyOp)
        // read the ctail
    | ReadonlyCtail(op: nrifc.ReadonlyOp, nodeId: NodeId, ctail: nat)
        // wait until localTail >= (the ctail value we just read)
    | ReadonlyReadyToRead(op: nrifc.ReadonlyOp, nodeId: NodeId)
        // read the op off the replica
    | ReadonlyDone(ret: nrifc.ReturnType)

  datatype UpdateState =
    | UpdateInit(op: nrifc.UpdateOp)
    | UpdatePlaced(nodeId: NodeId) //, idx: nat)
    | UpdateDone(ret: nrifc.ReturnType)

  // There is only one 'combiner' for a given node.
  // You can't enter the combining phase whenever you want. You must
  // start from the 'CombinerReady' state.

  // TODOs: CombinerState should have transitions for:
  //    * reading the global tail during exec
  //    * updating the ctail at the end of exec
  // global tail should be reflected in the M state

  datatype CombinerState =
    | CombinerReady(queued_ops: seq<RequestId>)
    | CombinerInProgress(localTail: nat, queued_ops: seq<RequestId>, queue_index: nat)

  datatype ReplicaState = ReplicaState(state: nrifc.NRState)
  datatype LogEntry = LogEntry(op: nrifc.UpdateOp, node_id: NodeId)

  datatype M = M(
    // the 'log' entries are shared via the circular buffer
    // (out of scope for this file)
    log: map<nat, LogEntry>,
    global_tail: Option<nat>,

    replicas: map<NodeId, nrifc.NRState>, // replicas protected by rwlock
    localTails: map<NodeId, nat>,         // localTail (atomic ints)
    ctail: Option<nat>,                   // ctail (atomic int)

    localReads: map<RequestId, ReadonlyState>,
    localUpdates: map<RequestId, UpdateState>,
    combiner: map<NodeId, CombinerState>
  ) | Fail

  // read the ctail

  predicate ReadonlyReadCtail(m: M, m': M, rid: RequestId, nodeId: NodeId) {
    && m.M?

    // We have access to the ctail
    && m.ctail.Some?

    // We have some ReadonlyState with request id `rid` in the `ReadonlyInit` state
    && rid in m.localReads
    && m.localReads[rid].ReadonlyInit?

    // Update the rid to the `ReadonlyCtail` state
    && m' == m.(localReads := m.localReads[rid :=
        ReadonlyCtail(
          m.localReads[rid].op,
          nodeId,
          m.ctail.value)
         ]
       )
  }

  predicate TransitionReadonlyReadyToRead(m: M, m': M, rid: RequestId) {
    && m.M?
    && rid in m.localReads
    && var readRequest := m.localReads[rid];
    && readRequest.ReadonlyCtail?
    && readRequest.nodeId in m.localTails
    && var localTail := m.localTails[readRequest.nodeId];
    && readRequest.ctail >= localTail
    && m' == m.(localReads := m.localReads[rid :=
        ReadonlyReadyToRead(
          m.localReads[rid].op,
          m.localReads[rid].nodeId)
         ]
       )
  }

  predicate TransitionReadonlyDone(m: M, m': M, rid: RequestId) {
    && m.M?
    && rid in m.localReads
    && var readRequest := m.localReads[rid];
    && readRequest.ReadonlyReadyToRead?
    && readRequest.nodeId in m.replicas
    && var ret := nrifc.read(m.replicas[readRequest.nodeId], readRequest.op);
    && m' == m.(localReads := m.localReads[rid :=
        ReadonlyDone(ret)]
       )
  }

  predicate TransitionCombine(m: M, m': M, nodeId: NodeId, rid: RequestId, op: nrifc.UpdateOp) {
    && m.M?
    && nodeId in m.combiner
    && m.combiner[nodeId].CombinerReady?

    //&& forall rid in rids ==> !m.localUpdates[rid]
    && !(rid in m.localUpdates)

    // TODO(gz): Don't conserve client
    && m' == m.(localUpdates := m.localUpdates[rid :=
        UpdateInit(op)]
       )
  }

  predicate AdvanceTail(m: M, m': M, nodeId: NodeId, request_ids: seq<RequestId>)
  {
    && m.M?
    && m.global_tail.Some?
    && var global_tail_var := m.global_tail.value;
    && (set x:RequestId | x in request_ids :: x)  <= m.localUpdates.Keys
    // Convert Updates to UpdatePlaced
    && m' == m.(localUpdates := (map rid | rid in m.localUpdates :: if rid in request_ids then 
      UpdatePlaced(nodeId) else m.localUpdates[rid])
    )
    && m'.global_tail.value == m.global_tail.value + |request_ids|


    // Add Log(tail-3, op1) ; Log(tail-2, op2) ; Log(tail-1, op1) ...
    && m' == m.(log := (map idx | idx in m.log :: if idx >= global_tail_var && idx < (global_tail_var+|request_ids|) then 
      LogEntry(UpdatePlaced(nodeId), nodeId) else m.localUpdates[idx])
    )


    //&& |request_ids| > 0
    //&& m' == m.(log := m.log[global_tail_var := LogEntry(m.localUpdates[request_ids[0]].op, nodeId)])
  }

  function dot(x: M, y: M) : M
  function unit() : M

  function Ticket(rid: RequestId, input: IOIfc.Input) : M
  function Stub(rid: RequestId, output: IOIfc.Output) : M

  // By returning a set of request ids "in use", we enforce that
  // there are only a finite number of them (i.e., it is always possible to find
  // a free one).
  function request_ids_in_use(m: M) : set<RequestId>

  predicate Init(s: M)
  predicate Internal(shard: M, shard': M)

  predicate Inv(s: M)

  lemma InitImpliesInv(s: M)
  //requires Init(s)
  ensures Inv(s)

  lemma InternalPreservesInv(shard: M, shard': M, rest: M)
  //requires Inv(dot(shard, rest))
  //requires Internal(shard, shard')
  ensures Inv(dot(shard', rest))

  lemma NewTicketPreservesInv(whole: M, whole': M, rid: RequestId, input: IOIfc.Input)
  //requires Inv(whole)
  //requires NewTicket(whole, whole', rid, input)
  ensures Inv(whole')

  lemma ConsumeStubPreservesInv(whole: M, whole': M, rid: RequestId, output: IOIfc.Output)
  //requires Inv(whole)
  //requires ConsumeStub(whole, whole', rid, output)
  ensures Inv(whole')

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x

  lemma commutative(x: M, y: M)
  ensures dot(x, y) == dot(y, x)

  lemma associative(x: M, y: M, z: M)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)

  lemma exists_inv_state()
  returns (s: M)
  ensures Inv(s)
}
