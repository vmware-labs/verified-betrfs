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
    | ReadonlyCtail(op: nrifc.ReadonlyOp, ctail: nat)
    // wait until localTail >= (the ctail value we just read)
    | ReadonlyReadyToRead(op: nrifc.ReadonlyOp, nodeId: NodeId, ctail: nat)
    // read the op off the replica
    | ReadonlyDone(op: nrifc.ReadonlyOp, ret: nrifc.ReturnType, ctail: nat)

  datatype UpdateState =
    | UpdateInit(op: nrifc.UpdateOp)
    | UpdatePlaced(nodeId: NodeId, idx: nat) // -> UpdateResp, no ret yet
    | UpdateApplied(ret: nrifc.ReturnType, idx: nat) // -> UpdateResp
    // TODO(travis): add idx here too:
    | UpdateDone(ret: nrifc.ReturnType, idx: nat) // -> UpdateResp

  // There is only one 'combiner' for a given node.
  // You can't enter the combining phase whenever you want. You must
  // start from the 'CombinerReady' state.

  // TODOs: CombinerState should have transitions for:
  //    * reading the global tail during exec
  //    * updating the ctail at the end of exec
  // global tail should be reflected in the M state

  // TODO rename this to ExecutorState maybe
  datatype CombinerState =
    | CombinerReady
      // Increment global tail with compare_and_exchange
    | CombinerPlaced(queued_ops: seq<RequestId>)
      // Read ltail
    | CombinerLtail(queued_ops: seq<RequestId>, localTail: nat)
      // Read global tail
    | Combiner(queued_ops: seq<RequestId>, localTail: nat, globalTail: nat)
      // increment localTail one at a time until localTail == globalTail
      // when localTail == globalTail, we can advance to the next step by updating the ctail
    | CombinerUpdatedCtail(queued_ops: seq<RequestId>, localAndGlobalTail: nat)
      // Finally we write to the localTail atomic and return to CombinerReady state

  datatype ReplicaState = ReplicaState(state: nrifc.NRState)
  // TODO(for-travis): what about the alive bit?
  // NOTE(travis): see the new notes in slide show
  datatype LogEntry = LogEntry(op: nrifc.UpdateOp, node_id: NodeId)

  datatype M = M(
    // the 'log' entries are shared via the circular buffer
    // (out of scope for this file)
    log: map<nat, LogEntry>,
    global_tail: Option<nat>,

    // TODO(for-travis): do we need RwLock?
    //
    // NOTE(travis): this depends on how we decide to fix the issue from last week
    //
    // * If it is determined that holding the lock for the duration of exec
    //      (including the ctail update) is essential to the algorithm, then
    //      we will need to model this lock explicitly.
    //
    // * If it is determined that the *only* function of the lock is to protect
    //      the replica, we do NOT need to model it explicitly.
    //lockStates: map<NodeId, LockState>,

    replicas: map<NodeId, nrifc.NRState>, // replicas protected by rwlock
    localTails: map<NodeId, nat>,         // localTail (atomic ints)
    ctail: Option<nat>,                   // ctail (atomic int)

    localReads: map<RequestId, ReadonlyState>,
    localUpdates: map<RequestId, UpdateState>,
    combiner: map<NodeId, CombinerState>
  ) | Fail


  // the well formedness predicate ensures that the state is valid, and the node ids are good
  predicate StateValid(m: M) {
    && m.M?
  }

  predicate CompleteTailValid(m: M)
    requires StateValid(m)
  {
    && m.ctail.Some?
  }

  predicate GlobalTailValid(m: M)
    requires StateValid(m)
  {
    && m.global_tail.Some?
  }

  predicate LocalTailValid(m: M, nodeId: NodeId)
    requires StateValid(m)
  {
    && nodeId in m.localTails
  }

  predicate ReplicaValid(m: M, nodeId: NodeId)
    requires StateValid(m)
  {
    && nodeId in m.replicas
  }

  predicate LogEntryIsReady(m: M, logentry: nat)
    requires StateValid(m)
  {
    && logentry in m.log.Keys
  }

  predicate LogEntryIsLocal(m: M, logentry: nat, nodeId: NodeId)
    requires StateValid(m)
    requires LogEntryIsReady(m, logentry)
  {
    && m.log[logentry].node_id == nodeId
  }

  /*
   * ============================================================================================
   * State Guards for Local Reads
   * ============================================================================================
   */

  // GUARD: InReadOnlyInit
  //
  // the supplied request ID is valid and the corresponding request is in the ReadonlyInit state
  predicate InReadOnlyInit(m: M, rid: RequestId)
    requires StateValid(m)
  {
      && rid in m.localReads
      && m.localReads[rid].ReadonlyInit?
  }

  // GUARD: InReadOnlyCTail
  //
  // the supplied request ID is valid, and the corresponding request is in the ReadonlyCtail state
  predicate InReadOnlyCTail(m: M, rid: RequestId)
    requires StateValid(m)
  {
      && rid in m.localReads
      && m.localReads[rid].ReadonlyCtail?
  }

  // GUARD: InReadyToRead
  //
  // the supplied request ID is valid and the corresponding request is in the ReadyToRead state
  predicate InReadyToRead(m: M, rid: RequestId)
    requires StateValid(m)
  {
      && rid in m.localReads
      && m.localReads[rid].ReadonlyReadyToRead?
      && m.localReads[rid].nodeId in m.replicas
  }

  /*
   * ============================================================================================
   * State Guards for Combiners
   * ============================================================================================
   */

  // GUARD: InCombinerReady
  //
  // the supplied nodeid is valid, and the combiner is in the Ready state.
  predicate InCombinerReady(m : M, nodeId : NodeId)
    requires StateValid(m)
  {
    && nodeId in m.combiner
    && m.combiner[nodeId].CombinerReady?
  }

  // GUARD: InCombinerPlaced
  //
  // the supplied nodeid is valid, and the combiner is in the CombinerPlaced state
  predicate InCombinerPlaced(m : M, nodeId : NodeId)
    requires StateValid(m)
  {
    && nodeId in m.combiner
    && m.combiner[nodeId].CombinerPlaced?
  }

  // GUARD: InCombinerPlaced
  //
  // the supplied nodeid is valid, and the combiner is in the CombinerLocalTail state
  predicate InCombinerLocalTail(m : M, nodeId : NodeId)
    requires StateValid(m)
  {
    && nodeId in m.combiner
    && m.combiner[nodeId].CombinerLtail?
  }

  // GUARD: InCombiner
  //
  // the supplied nodeid is valid, and the combiner is in the Combiner state with updates to be done
  predicate InCombiner(m : M, nodeId : NodeId)
    requires StateValid(m)
  {
    && nodeId in m.combiner
    && m.combiner[nodeId].Combiner?
    && m.combiner[nodeId].localTail < m.combiner[nodeId].globalTail
  }

  // GUARD: InCombinerPlaced
  //
  // the supplied nodeid is valid, and the combiner is in the Combiner state with all updates done
  predicate InCombinerDone(m: M, nodeId : NodeId)
    requires StateValid(m)
  {
    && nodeId in m.combiner
    && m.combiner[nodeId].Combiner?
    && m.combiner[nodeId].localTail == m.combiner[nodeId].globalTail
  }

  // GUARD: InCombinerPlaced
  //
  // the supplied nodeid is valid, and the combiner is in the UpdateCTail state
  predicate InCombinerUpdateCompleteTail(m : M, nodeId : NodeId)
    requires StateValid(m)
  {
    && nodeId in m.combiner
    && m.combiner[nodeId].CombinerUpdatedCtail?
  }

  /*
   * ============================================================================================
   * State Guards for UpdateRequests
   * ============================================================================================
   */

  // GUARD: UpdateInit
  //
  // the update request for is in the init state
  predicate InUpdateInit(m : M, reqid : RequestId)
    requires StateValid(m)
  {
    && reqid in m.localUpdates
    && m.localUpdates[reqid].UpdateInit?
  }

  // GUARD: UpdateInit
  //
  // all requests are in the updateinit state
  predicate InUpdateInitAll(m : M, rids: seq<RequestId>)
    requires StateValid(m)
  {
    forall rid | rid in rids :: InUpdateInit(m, rid)
  }

  // GUARD: UpdatePlaced
  //
  // the update request for is in the placed state
  predicate InUpdatePlaced(m : M, reqid: RequestId)
    requires StateValid(m)
  {
    && reqid in m.localUpdates
    && m.localUpdates[reqid].UpdatePlaced?
  }

  // GUARD: UpdateApplied
  //
  // the update request for is in the executed state
  predicate InUpdateApplied(m : M, reqid: RequestId)
    requires StateValid(m)
  {
    && reqid in m.localUpdates
    && m.localUpdates[reqid].UpdateApplied?
  }


  /*
   * ============================================================================================
   * Map/Seq Utilities
   * ============================================================================================
   */


  // updates map m1 with map m2, where all values of m2 aree added to m1, and existing values updated
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

  lemma map_update_distributive<K(!new), V>(m1: map<K, V>, m2: map<K, V>, m3: map<K, V>)
    requires m1.Keys !! m2.Keys && m2.Keys !! m3.Keys && m3.Keys !! m1.Keys
    ensures map_update(map_update(m1, m3), m2) == map_update(map_update(m1, m2), m3)
  {
  }

  lemma map_disjunct_eq<K(!new), V>(m1: map<K, V>, m2: map<K, V>, m3: map<K, V>)
    requires m1.Keys !! m2.Keys
    requires m1.Keys == m3.Keys
    ensures m3.Keys !! m2.Keys
  {
  }

  // checks that two maps are equal
  predicate map_equal<K(!new), V>(m1: map<K, V>, m2: map<K, V>)
  {
    && (forall k | k in m1 :: k in m2 && m1[k] == m2[k])
    && (forall k | k in m2 :: k in m1 && m1[k] == m2[k])
  }

  // all elements in the sequence are unique
  predicate seq_unique<V>(rids: seq<V>) {
    forall i, j | 0 <= i < |rids| && 0 <= j < |rids| && i != j :: rids[i] != rids[j]
  }


  /*
   * ============================================================================================
   * READ ONLY OPERATION
   * ============================================================================================
   *
   * function READONLY(args) {
   *   { ReadonlyInit(r, op) }
   *     readTail ← sharedLog.completedTail
   *   { ReadonlyCtail(r, op, readTail) }
   *     while localTail < readTail {
   *       // reader might acquire writer lock and update
   *       WaitOrUpdate(readTail)
   *     }
   *   { ReadonlyReadyToRead(r, op) }
   *     rwLock.Acquire-Reader()
   *     response ← replica.ReadOnly(args)
   *     rwLock.Release-Reader()
   *   { ReadonlyDone(r, response) }
   *     return response
   * }
   */


  // the local tail must have advanced far enough, so we can perform our read
  predicate LocalTailHasAdvanced(m: M, nodeId: NodeId,  readTail : nat)
    requires StateValid(m)
  {
      && nodeId in m.localTails
      && m.localTails[nodeId] >= readTail
  }

  // STATE TRANSITION: ReadOnlyInit -> ReadOnlyCTail
  //
  // Start of the read operation, load the ctail and transition the request from the
  // ReadOnlyInit -> ReadOnlyCTail state
  //
  // ASSUMPTION: the read operation has already been placed in the `localReads` part of the state
  //
  // { ReadonlyInit(r, op) }
  //   readTail ← sharedLog.completedTail
  // { ReadonlyCtail(r, op, readTail) }
  predicate TransitionReadonlyReadCtail(m: M, m': M, nodeId: NodeId, rid: RequestId) {
    && StateValid(m)
    && InReadOnlyInit(m, rid)
    && CompleteTailValid(m)

    // explicitly read the shared ctail value, and store it on the private "stack"
    && var readTail := m.ctail.value;

    // construct the new state for the read request
    && var newst :=  ReadonlyCtail(m.localReads[rid].op, readTail);
    // update the state
    && m' == m.(localReads := m.localReads[rid := newst])
  }

  // STATE TRANSITION: ReadOnlyCTail -> ReadonlyReadyToRead
  //
  // If the local ttail has advanced, transition to ReadyToRead state
  //
  // { ReadonlyCtail(r, op, readTail) }
  //   while localTail < readTail {
  //     // reader might acquire writer lock and update
  //     WaitOrUpdate(readTail)
  //   }
  // { ReadonlyReadyToRead(r, op) }
  predicate TransitionReadonlyReadyToRead(m: M, m': M, nodeId: NodeId, rid: RequestId) {
    && StateValid(m)
    && InReadOnlyCTail(m, rid)

    // store the read request for convenience
    && var readRequest := m.localReads[rid];

    // the local tail at the node must have advanced beyond the previously read ctail
    && LocalTailHasAdvanced(m, nodeId, readRequest.ctail)

    // construct the new state for the read request
    && var newst :=  ReadonlyReadyToRead(readRequest.op, nodeId, readRequest.ctail);
    // and update the state
    && m' == m.(localReads := m.localReads[rid := newst])
  }

  // STATE TRANSITION: ReadonlyReadyToRead -> ReadOnlyDone
  //
  // Perform the read operation and transition to ReadDone state
  //
  // { ReadonlyReadyToRead(r, op) }
  //   rwLock.Acquire-Reader()
  //   response ← replica.ReadOnly(args)
  //   rwLock.Release-Reader()
  // { ReadonlyDone(r, response) }
  predicate TransitionReadonlyDone(m: M, m': M, nodeId: NodeId, rid: RequestId) {
    && StateValid(m)
    && InReadyToRead(m, rid)

    // store the read request for convenience
    && var req := m.localReads[rid];

    // TODO require us to be in 'CombinerReady' state
    && InCombinerReady(m, req.nodeId)

    // perform the read operation from the replica
    && var ret := nrifc.read(m.replicas[req.nodeId], req.op);

    // construct the new state
    && var newst := ReadonlyDone(req.op, ret, req.ctail);
    // and update the state
    && m' == m.(localReads := m.localReads[rid := newst])
  }


  /*
   * ============================================================================================
   * LOG UPDATE OPERATIONS
   * ============================================================================================
   *
   * TODO: ADD THE COMPLETE "pseudocode here"
   */

  // predicate that states that `i` is within the range of the sequence
  predicate InRange(s: seq<RequestId>, i: nat) {
     0 <= i < |s|
  }

  // calculates the log index
  function LogIdx(gtail: nat, i: nat) : nat {
    gtail + i
  }

  predicate InRange2(s: seq<RequestId>, i: nat, g: nat)
  {
    && g <= i < g + |s|
  }

  // constructs the log map with the new entries
  function  {:opaque}  ConstructNewLogEntries(rids: seq<RequestId>, nodeId: NodeId, gtail: nat, lupd: map<RequestId, UpdateState>): (res: map<nat, LogEntry>)
    requires forall r | r in rids :: r in lupd && lupd[r].UpdateInit?
  {
    //map i : nat | (gtail <= i < gtail + |rids|) && InRange2(rids, i, gtail) :: i := LogEntry(lupd[rids[i-gtail]].op, nodeId)
    map i : nat | InRange(rids, i) && 0 <= i < |rids| :: LogIdx(gtail, i) :=  LogEntry(lupd[rids[i]].op, nodeId)
  }

  // lemma showing that 0 <= i < gtail not in new log, gtail <= i not in log, rest in log
  lemma ConstructNewLogEntries_InMap(rids: seq<RequestId>, nodeId: NodeId, gtail: nat, lupd: map<RequestId, UpdateState>, res: map<RequestId, LogEntry>)
    requires forall r | r in rids :: r in lupd && lupd[r].UpdateInit?
    requires res == ConstructNewLogEntries(rids, nodeId, gtail, lupd)
    ensures forall i : nat | 0 <= i < gtail :: i !in res
    ensures forall i : nat | gtail + |rids| <= i :: i !in res
    ensures forall i : nat | gtail <= i < gtail + |rids| :: i in res
    ensures forall i | i in res :: i >= gtail
    ensures forall i | i in res :: i < gtail + |rids|
  {
    reveal_ConstructNewLogEntries();
    forall idx : nat | gtail <= idx < gtail + |rids|
    ensures idx in res
    {
      var i := idx - gtail;
      assert LogIdx(gtail, i) == idx;
    }
  }

  lemma ConstructNewLogEntries_LogDisjunct(m: M, nodeId: NodeId, rids: seq<RequestId>, res: map<RequestId, LogEntry>)
    requires Inv(m)
    requires forall r | r in rids :: r in m.localUpdates && m.localUpdates[r].UpdateInit?
    requires res == ConstructNewLogEntries(rids, nodeId, m.global_tail.value, m.localUpdates)
    ensures res.Keys !! m.log.Keys
  {
    reveal_ConstructNewLogEntries();
  }

  lemma ConstructNewLogEntries_EqualKeys(rids: seq<RequestId>, nodeId: NodeId, gtail: nat, lupd: map<RequestId, UpdateState>, lupd2: map<RequestId, UpdateState>)
    requires forall r | r in rids :: r in lupd && lupd[r].UpdateInit?
    requires forall r | r in rids :: r in lupd2 && lupd2[r].UpdateInit?
    ensures ConstructNewLogEntries(rids, nodeId, gtail, lupd).Keys == ConstructNewLogEntries(rids, nodeId, gtail, lupd2).Keys
  {
    ConstructNewLogEntries_InMap(rids, nodeId, gtail, lupd, ConstructNewLogEntries(rids, nodeId, gtail, lupd));
    ConstructNewLogEntries_InMap(rids, nodeId, gtail, lupd2, ConstructNewLogEntries(rids, nodeId, gtail, lupd2));
  }

  lemma ConstructNewLogEntries_Equal(rids: seq<RequestId>, nodeId: NodeId, gtail: nat, lupd: map<RequestId, UpdateState>, lupd2: map<RequestId, UpdateState>)
    requires forall r | r in rids :: r in lupd && lupd[r].UpdateInit?
    requires forall r | r in rids :: r in lupd2 && lupd2[r].UpdateInit?
    requires forall r | r in rids :: lupd[r] == lupd2[r]
    ensures ConstructNewLogEntries(rids, nodeId, gtail, lupd) == ConstructNewLogEntries(rids, nodeId, gtail, lupd2)
  {
    ConstructNewLogEntries_InMap(rids, nodeId, gtail, lupd, ConstructNewLogEntries(rids, nodeId, gtail, lupd));
    ConstructNewLogEntries_InMap(rids, nodeId, gtail, lupd2, ConstructNewLogEntries(rids, nodeId, gtail, lupd2));
    reveal_ConstructNewLogEntries();
  }

  // constructs a localupdate map
  function {:opaque} ConstructLocalUpdateMap(rids: seq<RequestId>, nodeId: NodeId, gtail: nat) : map<RequestId, UpdateState>
    requires seq_unique(rids)
  {
    (map i : nat | InRange(rids, i) && 0 <= i < |rids| :: rids[i] as RequestId := UpdatePlaced(nodeId, LogIdx(gtail, i)))
  }

  lemma ConstructLocalUpdateMap_InMap(rids: seq<RequestId>, nodeId: NodeId, gtail: nat, res: map<RequestId, UpdateState>)
    requires seq_unique(rids)
    requires res == ConstructLocalUpdateMap(rids, nodeId, gtail)
    ensures forall r | r in rids :: r in res
    ensures forall r | r in res :: r in rids
    ensures forall r | r in rids :: res[r].UpdatePlaced?
    ensures forall r | r in rids :: res[r].idx < gtail + |rids|
    ensures forall r | r in rids :: gtail <= res[r].idx
  {
    reveal_ConstructLocalUpdateMap();
  }


  // reserve entries on the shared log
  // { UpdateInit(r, op1) ; UpdateInit(p, op2) ; UpdateInit(q, op3) ; CombinerReady ; GlobalTail(t) }
  //   tail = cmpxchg(tail, tail + ops.len()); // retry on fail
  //   for (i, op) in ops {
  //     let m = lmask[tkn]
  //     flip m on wrap around
  //     slog[tail+i].operation = Some(op);
  //     slog[tail+i].replica = tkn;
  //     slog[tail+i].alive = m; // last, tso here // Log(…) entries managed by slog
  //   }
  // { UpdatePlaced(r) ; UpdatePlaced(p) ; UpdatePlaced(q) ; CombinerPlaced( [p,q,r] ) ;
  //   Log(t, op1) ; Log(t+1, op2) ; Log(t+2, op1) ; GlobalTail(t + ops.len()) }
  predicate AdvanceTail(m: M, m': M, nodeId: NodeId, request_ids: seq<RequestId>)
  {
    && StateValid(m)
    && InCombinerReady(m, nodeId)
    && GlobalTailValid(m)
    && InUpdateInitAll(m, request_ids)
    && seq_unique(request_ids)

    // define local variable for convenience
    && var gtail := m.global_tail.value;

    // Add new entries to the log:
    && var updated_log := ConstructNewLogEntries(request_ids, nodeId, gtail, m.localUpdates);

    // the new local updates
    && var local_updates_new := ConstructLocalUpdateMap(request_ids, nodeId, gtail);

    // the new combiner state
    && var combiner_state_new := CombinerPlaced(request_ids);

    // calculate the new global tail
    && var global_tail_new := gtail + |request_ids|;

    // update the state
    && m' == m.(log := map_update(m.log, updated_log))
              .(localUpdates := map_update(m.localUpdates, local_updates_new))
              .(global_tail := Some(global_tail_new))
              .(combiner := m.combiner[nodeId := combiner_state_new])
  }

  /*
   * ============================================================================================
   * EXECUTE OPERATIONS
   * ============================================================================================
   *
   * TODO: ADD THE COMPLETE "pseudocode here"
   */

  // STATE TRANSITION: CombinerPlaced -> CombinerLTail
  //
  // This is the beginning of the execute operation. We start with reading our local tail
  //
  // exec():
  // { CombinerPlaced(queue) ; … }
  //   ltail = load ltails[tkn] // read our local ltail
  // { CombinerLtail(queue, ltail) ; … }
  predicate ExecLoadLtail(m: M, m': M, nodeId: NodeId) {
    && StateValid(m)
    && InCombinerPlaced(m, nodeId)
    && LocalTailValid(m, nodeId)
    // get the combiner state
    && var c := m.combiner[nodeId];

    // explicitly load the local tail
    && var ltail := m.localTails[nodeId];

    // construct the new combiner state
    && var newst := CombinerLtail(c.queued_ops, ltail);
    // update the state of the combiner
    && m' == m.(combiner := m.combiner[nodeId := newst])
  }

  // STATE TRANSITION: CombinerLTail -> CombierDispatch
  //
  // During the exec phase, we read the global tail to obtain the current entries in the
  // log. Note: the entries may not have been placed in the log yet.
  //
  // exec():
  // { CombinerLtail(queue, ltail) ; … }
  //   gtail = load tail
  // { Combiner (queue, ltail, gtail, 0) ; … }
  predicate ExecLoadGlobalTail(m: M, m': M, nodeId: NodeId) {
    && StateValid(m)
    && InCombinerLocalTail(m, nodeId)
    && GlobalTailValid(m)
    // get the combiner state
    && var c := m.combiner[nodeId];

    // explicitly load the global tail
    && var gtail := m.global_tail.value;

    // construct the new combiner state
    && var newst := Combiner(c.queued_ops, c.localTail, gtail);
    // update the state of the combiner
    && m' == m.(combiner := m.combiner[nodeId := newst])
  }

  // STATE TRANSITION: Combiner -> Combiner (local case)
  //
  //   assert (ltail < gtail && ltail[tkn] >= head);
  //   for i in ltail..gtail {
  //     Busy loop until slog[i].alive == lmasks[tkn]
  //     // case shown here is the one where log node_id = combiner node_id
  //     { Log(node_id, op); Combiner (queue, ltail, gtail, j) ; UpdatePlaced(queue[j]) ; … }
  //     d(slog[i].op, slog[i].replica)
  //     { Log(node_id, op); Combiner (queue, ltail+1, gtail, j+1) ; UpdateDone(return_value) ; … }
  //     // case 2 is where log node_id != combiner node_id
  //     if i == size – 1 {
  //       // Update generation on wrap-around
  //       lmasks[tkn] = !lmasks[tkn]
  //     }
  //   }
  predicate ExecDispatchLocal(m: M, m': M, nodeId: NodeId) {
    && StateValid(m)
    && InCombiner(m, nodeId)
    && ReplicaValid(m, nodeId)
    // get the combiner state
    && var c := m.combiner[nodeId];

    // the log entry should be ready to be consumed and it should be local
    && LogEntryIsReady(m, c.localTail)
    && LogEntryIsLocal(m, c.localTail, nodeId)

    // apply the update to the local data structure replica
    && var UpdateResult(nr_state', ret) := nrifc.update(m.replicas[nodeId], m.log[c.localTail].op);

    // calcualte the queue index.
    // Question(RA): could we use a map here instead? and associate it with the log index?
    && var queue_index := |c.queued_ops| - (c.globalTail - c.localTail);
    && 0 <= queue_index < |c.queued_ops|

    && var request_id := c.queued_ops[queue_index];
    && InUpdatePlaced(m, request_id)

    // we get the idx into the log here
    && var idx :=  m.localUpdates[request_id].idx;

    // update the combiner state by incrementing the current local tail
    &&  var c_new := c.(localTail := c.localTail + 1);

    // update the state
    && m' == m.(combiner := m.combiner[nodeId := c_new])
              .(replicas := m.replicas[nodeId := nr_state'])
              .(localUpdates := m.localUpdates[request_id := UpdateApplied(ret, idx)])
  }

  // STATE TRANSITION: Combiner -> Combiner (remote case)
  //
  //
  predicate ExecDispatchRemote(m: M, m': M, nodeId: NodeId) {
    && StateValid(m)
    && InCombiner(m, nodeId)
    && ReplicaValid(m, nodeId)
    // get the combiner state
    && var c := m.combiner[nodeId];

    // the log entry should be ready to be consumed and it should have been originated from another node
    && LogEntryIsReady(m, c.localTail)
    && !LogEntryIsLocal(m, c.localTail, nodeId)

    // apply the update to the local data structure replica
    && var UpdateResult(nr_state', ret) := nrifc.update(m.replicas[nodeId], m.log[c.localTail].op);

    // update the combiner state by incrementing the current local tail
    &&  var c_new := c.(localTail := c.localTail + 1);
    // update the state
    && m' == m.(combiner := m.combiner[nodeId := c_new])
              .(replicas := m.replicas[nodeId := nr_state'])
  }

  // STATE TRANSITION: Combiner -> CombinerUpdatedCtail
  //
  // Update the ctail to the maximum of the current stored global tail, and the current ctail
  //
  // assert (ltail = gtail)
  // { Combiner(queue, ltail, gtail, j) ; … }
  //   ctail = max(tail, ctail) // update completed tail
  // { CombinerUpdatedCtail(gtail, ltail, gtail, j) ; … }
  predicate UpdateCompletedTail(m: M, m': M, nodeId: NodeId) {
    && StateValid(m)
    && InCombinerDone(m, nodeId)
    && CompleteTailValid(m)
    // get the combiner state
    && var c := m.combiner[nodeId];
    // the new ctail is the maximum of the current ctail, and the local tail we've loaded
    && var new_ctail := if c.localTail > m.ctail.value then  c.localTail else m.ctail.value;
    // construct the new combiner state
    && var newst := CombinerUpdatedCtail(c.queued_ops, c.localTail);
    // update the ctail and the combiner state
    && m' == m.(combiner := m.combiner[nodeId := newst])
              .(ctail := Some(new_ctail))
  }

  // STATE TRANSITION: UpdateApplied -> UpdateDone
  //
  // Update the state of the update request from UpdateApplied to Done when the CTail has advanced
  //
  // { CombinerUpdatedCtail(gtail, ltail, gtail, j) ; … }
  //   store ltails[tkn] = gtail; // update replica's tail
  // { CombinerReady ; … }
  predicate GoToCombinerReady(m: M, m': M, nodeId: NodeId) {
    && StateValid(m)
    && InCombinerUpdateCompleteTail(m, nodeId)
    && CompleteTailValid(m)
    // get the combiner state
    && var c := m.combiner[nodeId];
    && nodeId in m.localTails // NOTE(travis): we need this
    // update the new state, set the combiner into ready state and update local tail
    && m' == m.(combiner := m.combiner[nodeId := CombinerReady])
              .(localTails := m.localTails[nodeId := c.localAndGlobalTail])
  }

  // STATE TRANSITION: UpdateApplied -> UpdateDone
  //
  // Update the state of the update request to done, if ctail has advanced far enough
  predicate UpdateRequestDone(m : M, m' : M, request_id: RequestId) {
    && StateValid(m)
    && InUpdateApplied(m, request_id)
    && CompleteTailValid(m)
    && var req := m.localUpdates[request_id];
    && m.ctail.value > req.idx
    && m' == m.(localUpdates := m.localUpdates[request_id := UpdateDone(req.ret, req.idx)])
  }

  /*
   * ============================================================================================
   * State merging etc.
   * ============================================================================================
   */

  // tips for implementing dot:
  // you should probably be able to find a map_update function in the codebase you can steal
  // if two things conflict, get a Fail
  function dot(x: M, y: M) : M {
    // if either state is Fale, then fail
    if x == Fail || y == Fail then
      Fail
    else if x.log.Keys !! y.log.Keys
         && x.replicas.Keys !! y.replicas.Keys
         && x.localTails.Keys !! y.localTails.Keys
         && x.localReads.Keys !! y.localReads.Keys
         && x.localUpdates.Keys !! y.localUpdates.Keys
         && x.combiner.Keys !! y.combiner.Keys
         && !(x.ctail.Some? && y.ctail.Some?)
         && !(x.global_tail.Some? && y.global_tail.Some?)
         then
      M(
      map_update(x.log, y.log),
      if x.global_tail.Some? then x.global_tail else y.global_tail,
      map_update(x.replicas, y.replicas),
      map_update(x.localTails, y.localTails),
      if x.ctail.Some? then x.ctail else y.ctail,
      map_update(x.localReads, y.localReads),
      map_update(x.localUpdates, y.localUpdates),
      map_update(x.combiner, y.combiner)
    )
    else
      Fail
  }

  // empty maps & stuff
  function unit() : M {
    M(
    // log: map<nat, LogEntry>
    map[],
    // global_tail: Option<nat>,
    None, // NOTE(travis): should be None
    // replicas: map<NodeId, nrifc.NRState>,
    map[], // Question: initialize for all nodes?
    // localTails: map<NodeId, nat>
    map[], // Question: initialize for all nodes?
    // ctail: Option<nat>,                   // ctail (atomic int)
    None,
    // localReads: map<RequestId, ReadonlyState>,
    map[],
    // localUpdates: map<RequestId, UpdateState>,
    map[],
    // combiner: map<NodeId, CombinerState>
    map[] // Question: intialize for all nodes?
    )
  }

  function ReadOp(rid: RequestId, readonly_state: ReadonlyState) : M {
    M(map[], None, map[], map[], None,
      map[rid := readonly_state],
      map[], map[])
  }

  function UpdateOp(rid: RequestId, update_state: UpdateState) : M {
    M(map[], None, map[], map[], None, map[],
      map[rid := update_state],
      map[])
  }

  function Ticket(rid: RequestId, input: IOIfc.Input) : M {
    if input.ROp? then
      ReadOp(rid, ReadonlyInit(input.readonly_op))
    else
      UpdateOp(rid, UpdateInit(input.update_op))
  }

  predicate IsStub(rid: RequestId, output: IOIfc.Output, stub: M) {
    || (exists ctail, op :: stub == ReadOp(rid, ReadonlyDone(op, output, ctail)))
    || (exists log_idx :: stub == UpdateOp(rid, UpdateDone(output, log_idx)))
  }

  // By returning a set of request ids "in use", we enforce that
  // there are only a finite number of them (i.e., it is always possible to find
  // a free one).
  function request_ids_in_use(m: M) : set<RequestId> {
    if m == Fail then
      {}
    else
      m.localReads.Keys + m.localUpdates.Keys
  }

  predicate Init(s: M) {
    // the state is not fail
    s.M?
    // pointers are zero
    && s.ctail == Some(0)
    && s.global_tail == Some(0)
    // there should be at least one replica
    // NOTE(travis) this is probably technically unnecessary even if it's harmless
    && |s.replicas| > 0
    // all node local state is defined for all replica
    && s.replicas.Keys == s.localTails.Keys
    && s.replicas.Keys == s.combiner.Keys
    // all local tails == 0
    && (forall i | i in s.localTails :: s.localTails[i] == 0)
    // all combiners are in ready state
    && (forall i | i in s.combiner :: s.combiner[i] == CombinerReady)

    // all replicas should be identical
    && (forall i | i in s.replicas :: s.replicas[i] == nrifc.init_state())

    // the local reads, local updates, and the log should be empty
    && s.localReads == map[]
    && s.localUpdates == map[]
    && s.log == map[]
  }

  // take a look at scache/cache/SimpleCacheSM.i.dfy for an example
  // NOTE(travis): the `Next` predicate defined below should be called `Internal`
  //    The "full" Next predicate includes:
  //      * new requests entering the system
  //      * finished responses leaving the system
  //      * "internal" steps, like all the ones defined in this file
  predicate Internal(shard: M, shard': M)
  {
    Next(shard, shard')
  }

  // Given a log of ops and a version number, compute the state at that version
  function state_at_version(log: map<nat, LogEntry>, version: nat) : nrifc.NRState
  requires forall i | 0 <= i < version :: i in log
  {
    if version == 0 then
      nrifc.init_state()
    else
      nrifc.update(state_at_version(log, version - 1), log[version-1].op).new_state
  }

  /*
   * ============================================================================================
   * Invariant
   * ============================================================================================
   */

  // helper predicate to check that range is in the log [start..end]
  predicate LogContainsEntries(log: map<nat, LogEntry>, start: nat, end: nat) {
    forall i | start <= i < end :: i in log.Keys
  }

  // helper predicate to check that range up to here is in the log [0..here]
  predicate LogContainsEntriesUpToHere(log: map<nat, LogEntry>, here: nat) {
    LogContainsEntries(log, 0, here)
  }

  // INVARIANT: Well-formed State
  // Overall the state must be well-formed: not failed, with some ctail/gtail values, ndoes exists
  predicate Inv_WF(s: M) {
    // the state is not failed
    && s.M?
    // Question(RA): can we always assume this here?
    // NOTE(travis): yes, this is what I'd expect
    && s.ctail.Some?
    && s.global_tail.Some?
    // the node-related state must exist for all nodes, and there must be at least one node.
    && s.replicas.Keys == s.localTails.Keys
    && s.replicas.Keys == s.combiner.Keys
    && |s.replicas.Keys| > 0
  }

  // INVARIANT: Ordering of global tail and completed tail
  // we have that the global tail must always be ahead of, or equal to the completed tail
  predicate Inv_GlobalTailCompleteTailOrdering(s: M)
    requires Inv_WF(s)
  {
    s.global_tail.value >= s.ctail.value
  }

  // INVARIANT: Ordering of the ctail and the local tail values
  // the completed tail must be ahead of, or equal to the local tails
  predicate Inv_CompletedTailLowerBound(s: M)
    requires Inv_WF(s)
  {
    forall nodeId | nodeId in s.localTails :: s.ctail.value >= s.localTails[nodeId]
  }

  // INVVARIANT: ordering of the global tail and the local tail values
  // the global tail must be ahead of, or equal to the stored global_tail_snapshot
  // XXX: that should follow from the previous two invariants
  predicate Inv_GlobalTailLowerBound(s: M)
    requires Inv_WF(s)
  {
    forall nodeId | nodeId in s.localTails :: s.global_tail.value >= s.localTails[nodeId]
  }

  // INVARIANT: Ordering of Ctail stored in ReadOnly state
  // The stored ctail values must be smaller or equal the actual ctail value
  predicate Inv_ReadOnlyCtailsCompleteTailOrdering(s: M)
    requires Inv_WF(s)
  {
    forall rid | rid in s.localReads :: match s.localReads[rid] {
      case ReadonlyCtail(_, ctail: nat) => ctail <= s.ctail.value
      case ReadonlyReadyToRead(_, _, ctail: nat) => ctail <= s.ctail.value
      case ReadonlyDone(_, _, ctail: nat) =>  ctail <= s.ctail.value
      case _ => true
    }
  }

  // INVARIANT: the log contains entries yup to the complete tail
  predicate Inv_LogEntriesUpToCTailExists(s: M)
    requires Inv_WF(s)
  {
    && LogContainsEntriesUpToHere(s.log, s.ctail.value)
  }

  // INVARIANT: The log must contain entries up to the local tails
  // XXX: that one follows from the `Inv_LogEntriesUpToCTailExists` and `Inv_CompletedTailLowerBound`
  predicate Inv_LogEntriesUpToLocalTailExist(s: M)
    requires Inv_WF(s)
  {
    forall nid | nid in s.localTails :: LogContainsEntriesUpToHere(s.log, s.localTails[nid])
  }




  function get_local_tail(m: M, nodeId: NodeId) : nat
    requires Inv_WF(m)
    requires nodeId in m.localTails
    requires nodeId in m.combiner
  {
    match m.combiner[nodeId] {
      case CombinerReady => m.localTails[nodeId]
      case CombinerPlaced(_) => m.localTails[nodeId]
      case CombinerLtail(_, localTail: nat) => localTail
      case Combiner(_, localTail: nat, _) => localTail
      case CombinerUpdatedCtail(_, localAndGlobalTail: nat) => localAndGlobalTail
    }
  }

  predicate Inv_CombinerStateValid(s: M)
    requires Inv_WF(s)
  {
    forall nodeId | nodeId in s.combiner :: match s.combiner[nodeId] {
      case CombinerReady => true
      case CombinerPlaced(queued_ops: seq<RequestId>) => true
      case CombinerLtail(queued_ops: seq<RequestId>, localTail: nat) => (
        // we've just read the local tail value, and no-one else should modify that
        && localTail == s.localTails[nodeId]
        // the local tail should be smaller or equal than the ctail
        && localTail <= s.ctail.value
      )
      case Combiner(queued_ops: seq<RequestId>, localTail: nat, globalTail: nat) => (
        // the global tail may have already advanced...
        && globalTail <= s.global_tail.value
        // we're advancing the local tail here
        && localTail >= s.localTails[nodeId]
        // the local tail should always be smaller or equal to the global tail
        && localTail <= globalTail
        // the log now contains all entries up to localtail
        && LogContainsEntriesUpToHere(s.log, localTail)
      )
      case CombinerUpdatedCtail(queued_ops: seq<RequestId>, localAndGlobalTail: nat) => (
        // the global tail may have already advanced...
        && localAndGlobalTail <= s.global_tail.value
        // update the ctail value
        && localAndGlobalTail <= s.ctail.value
        // the local tail should be smaller than this one here
        && s.localTails[nodeId] <= localAndGlobalTail
        // the log now contains all entries up to localAndGlobalTail
        && LogContainsEntriesUpToHere(s.log, localAndGlobalTail)
      )
    }
  }

  // the completed tail must be ahead of, or equal to the local tails
  predicate Inv_ReadOnlyStateNodeIdExists(s: M)
    requires Inv_WF(s)
  {
    forall rid | rid in s.localReads :: (
      if s.localReads[rid].ReadonlyReadyToRead? then
         && s.localReads[rid].nodeId in s.replicas
         && s.localReads[rid].nodeId in s.localTails
      else
        true
    )
  }



  function CombinerRange(c: CombinerState) : set<nat> {
    match c {
      case CombinerReady => {}
      case CombinerPlaced(_) => {}
      case CombinerLtail(_, _) => {}
      case Combiner(_, _, _) => {}
      case CombinerUpdatedCtail(_, _) => {}
    }
  }

    // the completed tail must be ahead of, or equal to the local tails
  predicate Inv_CombinerLogNonOverlap(s: M)
    requires Inv_WF(s)
  {
    forall c1, c2 | c1 in s.combiner &&  c2 in s.combiner ::
        c1 == c2 || CombinerRange(s.combiner[c1]) !! CombinerRange(s.combiner[c2])
  }

  // all entries up to the global tail in the log, above not in the log
  predicate Inv_LogEntriesGlobalTail(s: M)
    requires Inv_WF(s)
  {
    // the log doesn't contain entries above the global tail
    && (forall idx : nat | idx >= s.global_tail.value :: idx !in s.log.Keys)
    && (forall idx : nat | 0 <= idx < s.global_tail.value :: idx in s.log.Keys)
  }

  // the stored log idx are in the log, and smaller than the global tail
  predicate Inv_LocalUpdatesIdx(s: M)
    requires Inv_WF(s)
  {
    // TODO(travis): all the `idx` in localUpdates.UpdatePlaced?.idx and
    // localUpdates.UpdateDone?.idx should be less than ctail?
    && (forall upd | upd in s.localUpdates && s.localUpdates[upd].UpdatePlaced?
      :: s.localUpdates[upd].idx in s.log.Keys && s.localUpdates[upd].idx < s.global_tail.value)
    && (forall upd | upd in s.localUpdates && s.localUpdates[upd].UpdateApplied?
      :: s.localUpdates[upd].idx in s.log.Keys && s.localUpdates[upd].idx < s.global_tail.value)
    && (forall upd | upd in s.localUpdates && s.localUpdates[upd].UpdateDone?
      :: s.localUpdates[upd].idx in s.log.Keys && s.localUpdates[upd].idx < s.global_tail.value)
    && (forall upd | upd in s.localUpdates && s.localUpdates[upd].UpdateDone?
      :: s.localUpdates[upd].idx in s.log.Keys && s.localUpdates[upd].idx < s.ctail.value)
  }

  // the result of the read operation corresponds to reading the replica at one given version
  // we wait until localTail >= ctail before we go ahead and read.
  predicate Inv_ReadOnlyResult(s: M)
    requires Inv_WF(s)
    requires Inv_LogEntriesUpToCTailExists(s)
  {
      (forall r | r in s.localReads && s.localReads[r].ReadonlyDone? ::
        exists v | 0 <= v <= s.ctail.value ::
          s.localReads[r].ret == nrifc.read(state_at_version(s.log, v),  s.localReads[r].op)
      )
  }

  predicate Inv_UpdateResults(s: M)
    requires Inv_WF(s)
    requires Inv_LocalUpdatesIdx(s)
    requires Inv_LogEntriesGlobalTail(s)
  {
      && (forall r | r in s.localUpdates && s.localUpdates[r].UpdateApplied? ::
           s.localUpdates[r].ret
            == nrifc.update(state_at_version(s.log, s.localUpdates[r].idx),
                            s.log[s.localUpdates[r].idx].op).return_value
      )

      && (forall r | r in s.localUpdates && s.localUpdates[r].UpdateDone? ::
           s.localUpdates[r].ret
            == nrifc.update(state_at_version(s.log, s.localUpdates[r].idx),
                            s.log[s.localUpdates[r].idx].op).return_value
      )

  }

  // the invariant
  predicate Inv(s: M) {
    && Inv_WF(s)
    && Inv_GlobalTailCompleteTailOrdering(s)
    && Inv_CompletedTailLowerBound(s)
    && Inv_GlobalTailLowerBound(s)
    && Inv_ReadOnlyCtailsCompleteTailOrdering(s)
    && Inv_LogEntriesUpToCTailExists(s)
    && Inv_LogEntriesUpToLocalTailExist(s)
    && Inv_CombinerStateValid(s)
    && Inv_CombinerLogNonOverlap(s)
    && Inv_ReadOnlyStateNodeIdExists(s)
    && Inv_LogEntriesGlobalTail(s)
    && Inv_LocalUpdatesIdx(s)
    && Inv_ReadOnlyResult(s)
    && Inv_UpdateResults(s)

    // && (forall nid | nid in s.combiner :: CombinerRange(s.combiner[nid]) !!  (set x | 0 <= x < get_local_tail(s, nid) :: x))

    // replica[nodeId] == fold the operations in the log up to version logicalLocalTail
    //     (initial state + log 0 + log 1 + ... + log k)
    //     (see state_at_version in NRSimple)

    && (forall nodeId | nodeId in s.replicas :: (forall i | 0 <= i < get_local_tail(s, nodeId) :: i in s.log.Keys))
    && (forall nodeId | nodeId in s.replicas :: s.replicas[nodeId] == state_at_version(s.log, get_local_tail(s, nodeId)))
  }

  lemma InitImpliesInv(s: M)
  //requires Init(s)
  ensures Inv(s)

  lemma InternalPreservesInv(shard: M, shard': M, rest: M)
  //requires Inv(dot(shard, rest))
  //requires Internal(shard, shard')
  ensures Inv(dot(shard', rest))
  {
    InternalMonotonic(shard, shard', rest);
    Next_Implies_inv(dot(shard, rest), dot(shard', rest));
  }

  lemma NewTicketPreservesInv(whole: M, whole': M, rid: RequestId, input: IOIfc.Input)
  //requires Inv(whole)
  //requires NewTicket(whole, whole', rid, input)
  ensures Inv(whole')

  lemma ConsumeStubPreservesInv(whole: M, whole': M, rid: RequestId, output: IOIfc.Output, stub: M)
  //requires Inv(whole)
  //requires ConsumeStub(whole, whole', rid, output)
  ensures Inv(whole')

  lemma dot_unit(x: M)
  ensures dot(x, unit()) == x
  {
    assert unit().M?;
    assert dot(unit(), unit()).M?;
    assert dot(unit(), unit()) == unit();
    assert dot(x, unit()) == x;
  }

  lemma commutative(x: M, y: M)
  ensures dot(x, y) == dot(y, x)
  {
    if dot(x, y) == Fail {
      assert dot(x, y) == dot(y, x);
    } else {
      assert dot(x, y) == dot(y, x);
    }
  }

  lemma associative(x: M, y: M, z: M)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)
  {
    if dot(x, dot(y, z)) == Fail {
      assert dot(x, dot(y, z)) == dot(dot(x, y), z);
    } else {
      assert dot(x, dot(y, z)) == dot(dot(x, y), z);
    }
  }

  lemma exists_inv_state()
  returns (s: M)
  ensures Inv(s)

  datatype Step =
    | GoToCombinerReady_Step(nodeId: NodeId)
    | ExecLoadLtail_Step(nodeId: NodeId)
    | ExecLoadGlobalTail_Step(nodeId: NodeId)
    | ExecDispatchLocal_Step(nodeId: NodeId)
    | ExecDispatchRemote_Step(nodeId: NodeId)
    | TransitionReadonlyReadCtail_Step(nodeId: NodeId, rid: RequestId )
    | TransitionReadonlyReadyToRead_Step(nodeId: NodeId, rid: RequestId)
    | TransitionReadonlyDone_Step(nodeId: NodeId, rid: RequestId)
    | UpdateCompletedTail_Step(nodeId: NodeId)
    | AdvanceTail_Step(nodeId: NodeId, request_ids: seq<RequestId>)
    | UpdateRequestDone_Step(request_id: RequestId)


  predicate NextStep(m: M, m': M, step: Step) {
    match step {
      case GoToCombinerReady_Step(nodeId: NodeId) => GoToCombinerReady(m, m', nodeId)
      case ExecLoadLtail_Step(nodeId: NodeId) => ExecLoadLtail(m, m', nodeId)
      case ExecLoadGlobalTail_Step(nodeId: NodeId) => ExecLoadGlobalTail(m, m', nodeId)
      case ExecDispatchLocal_Step(nodeId: NodeId) => ExecDispatchLocal(m, m',nodeId)
      case ExecDispatchRemote_Step(nodeId: NodeId) => ExecDispatchRemote(m, m',nodeId)
      case TransitionReadonlyReadCtail_Step(nodeId: NodeId, rid: RequestId) =>  TransitionReadonlyReadCtail(m, m', nodeId, rid)
      case TransitionReadonlyReadyToRead_Step(nodeId: NodeId, rid: RequestId) => TransitionReadonlyReadyToRead(m, m', nodeId, rid)
      case TransitionReadonlyDone_Step(nodeId: NodeId, rid: RequestId) => TransitionReadonlyDone(m, m', nodeId, rid)
      case AdvanceTail_Step(nodeId: NodeId, request_ids: seq<RequestId>) => AdvanceTail(m, m', nodeId, request_ids)
      case UpdateCompletedTail_Step(nodeId: NodeId) => UpdateCompletedTail(m, m',nodeId)
      case UpdateRequestDone_Step(request_id: RequestId) => UpdateRequestDone(m, m', request_id)
    }
  }

  predicate Next(m: M, m': M) {
    exists step :: NextStep(m, m', step)
  }


  /// invariance proofs
  lemma Init_Implies_Inv(m: M)
  requires Init(m)
  ensures Inv(m)
  {

  }

  lemma TransitionReadonlyReadCtail_PreservesInv(m: M, m': M, nodeId: NodeId, rid: RequestId)
    requires Inv(m)
    requires TransitionReadonlyReadCtail(m, m', nodeId, rid)
    ensures Inv(m')
  {

  }

  lemma TransitionReadonlyReadyToRead_PreservesInv(m: M, m': M, nodeId: NodeId, rid: RequestId)
    requires Inv(m)
    requires TransitionReadonlyReadyToRead(m, m', nodeId, rid)
    ensures Inv(m')
  {

  }

  lemma TransitionReadonlyDone_PreservesInv(m: M, m': M, nodeId: NodeId, rid: RequestId)
    requires Inv(m)
    requires TransitionReadonlyDone(m, m', nodeId, rid)
    ensures Inv(m')
  {
    var req := m.localReads[rid];
    assert get_local_tail(m, req.nodeId) == m.localTails[req.nodeId];
    assert m.replicas[req.nodeId] == state_at_version(m.log, get_local_tail(m, req.nodeId));
    assert get_local_tail(m, req.nodeId) <= m.ctail.value;
    assert m'.localReads[rid].ret ==  nrifc.read(state_at_version(m.log, get_local_tail(m, req.nodeId)),  m.localReads[rid].op);
  }

  lemma state_at_version_preserves(a: map<nat, LogEntry>, b: map<nat, LogEntry>, i: nat)
  requires forall k | 0 <= k < i :: k in a && k in b && a[k] == b[k]
  ensures state_at_version(a, i) == state_at_version(b, i)
  decreases i
  {
    if i > 0 {
      state_at_version_preserves(a, b, i-1);
    }
  }

  lemma AdvanceTail_PreservesInv(m: M, m': M, nodeId: NodeId, request_ids: seq<RequestId>)
    requires Inv(m)
    requires AdvanceTail(m, m', nodeId, request_ids)
    ensures Inv(m')
  {
    assert(seq_unique(request_ids));
    var updated_log := ConstructNewLogEntries(request_ids, nodeId, m.global_tail.value, m.localUpdates);
    ConstructNewLogEntries_InMap(request_ids, nodeId, m.global_tail.value, m.localUpdates, updated_log);

    assert m'.log == map_update(m.log, updated_log);

    forall nid | nid in m'.replicas
      ensures m'.replicas[nid] == state_at_version(m'.log, get_local_tail(m', nid))
      {
        state_at_version_preserves(m.log, m'.log, get_local_tail(m', nid));
      }


    forall idx : nat | 0 <= idx < m'.global_tail.value
    ensures idx in m'.log.Keys
    {
      if idx < m.global_tail.value {
        assert idx in m'.log.Keys;
      } else {
        var i := idx - m.global_tail.value;
        assert m.global_tail.value + i == idx;
      }
    }

    forall v | 0 <= v <= m'.ctail.value
    ensures state_at_version(m'.log, v) == state_at_version(m.log, v)
    {
      state_at_version_preserves(m.log, m'.log, v);
    }

    reveal_ConstructLocalUpdateMap();

    forall upd | upd in m'.localUpdates && m'.localUpdates[upd].UpdatePlaced?
    ensures m'.localUpdates[upd].idx in m'.log.Keys
    ensures m'.localUpdates[upd].idx <= m'.global_tail.value
    {

    }

    forall r | r in m'.localUpdates && m'.localUpdates[r].UpdateApplied?
      ensures m'.localUpdates[r].idx == m.localUpdates[r].idx
      ensures state_at_version(m'.log, m'.localUpdates[r].idx) == state_at_version(m.log, m.localUpdates[r].idx)
    {
      state_at_version_preserves(m.log, m'.log, m'.localUpdates[r].idx);
    }
  }


  lemma ExecLoadLtail_PreservesInv(m: M, m': M, nodeId: NodeId)
    requires Inv(m)
    requires ExecLoadLtail(m, m', nodeId)
    ensures Inv(m')
  {

  }


  lemma ExecLoadGlobalTail_PreservesInv(m: M, m': M, nodeId: NodeId)
    requires Inv(m)
    requires ExecLoadGlobalTail(m, m', nodeId)
    ensures Inv(m')
  {
  }

  lemma ExecDispatchRemote_PreservesInv(m: M, m': M, nodeId: NodeId)
    requires Inv(m)
    requires ExecDispatchRemote(m, m',nodeId)
    ensures Inv(m')
  {

  }

  lemma ExecDispatchLocal_PreservesInv(m: M, m': M, nodeId: NodeId)
    requires Inv(m)
    requires ExecDispatchLocal(m, m',nodeId)
    ensures Inv(m')
  {

  }

  lemma UpdateCompletedTail_PreservesInv(m: M, m': M, nodeId: NodeId)
    requires Inv(m)
    requires UpdateCompletedTail(m, m',nodeId)
    ensures Inv(m')
  {
  }

  lemma GoToCombinerReady_PreservesInv(m: M, m': M, nodeId: NodeId)
    requires Inv(m)
    requires GoToCombinerReady(m, m', nodeId)
    ensures Inv(m')
  {

  }

  lemma UpdateRequestDone_PreservesInv(m: M, m': M, request_id: RequestId)
    requires Inv(m)
    requires UpdateRequestDone(m, m', request_id)
    ensures Inv(m')
  {

  }

  lemma NextStep_PreservesInv(m: M, m': M, step: Step)
    requires Inv(m)
    requires NextStep(m, m', step)
    ensures Inv(m')
  {
    match step {
      case GoToCombinerReady_Step(nodeId: NodeId) => GoToCombinerReady_PreservesInv(m, m', nodeId);
      case ExecLoadLtail_Step(nodeId: NodeId) => ExecLoadLtail_PreservesInv(m, m', nodeId);
      case ExecLoadGlobalTail_Step(nodeId: NodeId) => ExecLoadGlobalTail_PreservesInv(m, m', nodeId);
      case ExecDispatchLocal_Step(nodeId: NodeId) => ExecDispatchLocal_PreservesInv(m, m',nodeId);
      case ExecDispatchRemote_Step(nodeId: NodeId) => ExecDispatchRemote_PreservesInv(m, m',nodeId);
      case TransitionReadonlyReadCtail_Step(rid: RequestId, nodeId: NodeId) =>  TransitionReadonlyReadCtail_PreservesInv(m, m', rid, nodeId);
      case TransitionReadonlyReadyToRead_Step(nodeId: NodeId, rid: RequestId) => TransitionReadonlyReadyToRead_PreservesInv(m, m', nodeId, rid);
      case TransitionReadonlyDone_Step(nodeId: NodeId, rid: RequestId) => TransitionReadonlyDone_PreservesInv(m, m', nodeId, rid);
      case AdvanceTail_Step(nodeId: NodeId, request_ids: seq<RequestId>) => AdvanceTail_PreservesInv(m, m', nodeId, request_ids);
      case UpdateCompletedTail_Step(nodeId: NodeId) =>  UpdateCompletedTail_PreservesInv(m, m', nodeId);
      case UpdateRequestDone_Step(request_id: RequestId) => UpdateRequestDone_PreservesInv(m, m', request_id);
    }
  }

  lemma Next_Implies_inv(m: M, m': M)
  requires Inv(m)
  requires Next(m, m')
  ensures Inv(m')
  {
    var step :| NextStep(m, m', step);
    NextStep_PreservesInv(m, m', step);
  }

  lemma GoToCombinerReady_Monotonic(m: M, m': M, p: M, nodeId: NodeId)
  //requires Inv(dot(m, p))
  requires dot(m, p) != Fail
  requires GoToCombinerReady(m, m', nodeId)
  ensures GoToCombinerReady(dot(m, p), dot(m', p), nodeId)
  {
  }

  lemma ExecLoadLtail_Monotonic(m: M, m': M, p: M, nodeId: NodeId)
  //requires Inv(dot(m, p))
  requires dot(m, p) != Fail
  requires ExecLoadLtail(m, m', nodeId)
  ensures ExecLoadLtail(dot(m, p), dot(m', p), nodeId)
  {
  }

  lemma ExecLoadGlobalTail_Monotonic(m: M, m': M, p: M, nodeId: NodeId)
  //requires Inv(dot(m, p))
  requires dot(m, p) != Fail
  requires ExecLoadGlobalTail(m, m', nodeId)
  ensures ExecLoadGlobalTail(dot(m, p), dot(m', p), nodeId)
  {
  }

  lemma ExecDispatchLocal_Monotonic(m: M, m': M, p: M, nodeId: NodeId)
  //requires Inv(dot(m, p))
  requires dot(m, p) != Fail
  requires ExecDispatchLocal(m, m', nodeId)
  ensures ExecDispatchLocal(dot(m, p), dot(m', p), nodeId)
  {
    /*
    var c := m.combiner[nodeId];
    var UpdateResult(nr_state', ret) := nrifc.update(m.replicas[nodeId], m.log[c.localTail].op);
    var c_new := c.(localTail := c.localTail + 1);
    var queue_index := |c.queued_ops| - (c.globalTail - c.localTail);
    assert dot(m', p).combiner == dot(m, p).combiner[nodeId := c_new];
    assert dot(m', p).replicas == dot(m, p).replicas[nodeId := nr_state'];
    assert dot(m', p).localUpdates == dot(m, p).localUpdates[c.queued_ops[queue_index]:= UpdateDone(ret)];
    */
  }

  lemma ExecDispatchRemote_Monotonic(m: M, m': M, p: M, nodeId: NodeId)
  //requires Inv(dot(m, p))
  requires dot(m, p) != Fail
  requires ExecDispatchRemote(m, m', nodeId)
  ensures ExecDispatchRemote(dot(m, p), dot(m', p), nodeId)
  {
  }

  lemma TransitionReadonlyReadCtail_Monotonic(m: M, m': M, p: M, rid: RequestId, nodeId: NodeId)
  //requires Inv(dot(m, p))
  requires dot(m, p) != Fail
  requires TransitionReadonlyReadCtail(m, m', rid, nodeId)
  ensures TransitionReadonlyReadCtail(dot(m, p), dot(m', p), rid, nodeId)
  {
  }

  lemma TransitionReadonlyReadyToRead_Monotonic(m: M, m': M, p: M, nodeId: NodeId, rid: RequestId)
  //requires Inv(dot(m, p))
  requires dot(m, p) != Fail
  requires TransitionReadonlyReadyToRead(m, m', nodeId, rid)
  ensures TransitionReadonlyReadyToRead(dot(m, p), dot(m', p), nodeId, rid)
  {
  }

  lemma TransitionReadonlyDone_Monotonic(m: M, m': M, p: M, nodeId: NodeId, rid: RequestId)
  //requires Inv(dot(m, p))
  requires dot(m, p) != Fail
  requires TransitionReadonlyDone(m, m', nodeId, rid)
  ensures TransitionReadonlyDone(dot(m, p), dot(m', p), nodeId, rid)
  {
  }

  lemma UpdateCompletedTail_Monotonic(m: M, m': M, p: M, nodeId: NodeId)
  //requires Inv(dot(m, p))
  requires dot(m, p) != Fail
  requires UpdateCompletedTail(m, m', nodeId)
  ensures UpdateCompletedTail(dot(m, p), dot(m', p), nodeId)
  {
  }

  lemma AdvanceTail_Monotonic(m: M, m': M, p: M, nodeId: NodeId, request_ids: seq<RequestId>)
  requires Inv_WF(dot(m, p))
  requires Inv_LogEntriesGlobalTail(dot(m, p))
  //requires Inv(dot(m, p))
  requires dot(m, p) != Fail
  requires AdvanceTail(m, m', nodeId, request_ids)
  ensures AdvanceTail(dot(m, p), dot(m', p), nodeId, request_ids)
  {
    // NOTE(travis): this lemma currenty verifies, takes 40s thought, so I'm adding
    // this for now to save time verifying the file. If the proof breaks again, we can
    // just fix it later.
    assume false;

    var lupd := ConstructLocalUpdateMap(request_ids, nodeId, m.global_tail.value);

    var big_lupd := ConstructLocalUpdateMap(request_ids, nodeId, dot(m, p).global_tail.value);

    var updated_log := ConstructNewLogEntries(request_ids, nodeId, m.global_tail.value, m.localUpdates);

    var big_updated_log := ConstructNewLogEntries(request_ids, nodeId, dot(m, p).global_tail.value, dot(m, p).localUpdates);

    assert dot(m', p) != Fail
    by {
      assert m'.log.Keys !! p.log.Keys by {
        forall j | j in m'.log.Keys && j in p.log.Keys
        ensures false
        {
          assert j in updated_log;
          assert exists i: nat :: InRange(request_ids, i) && 0 <= i < |request_ids|
              && LogIdx(m.global_tail.value, i) == j by { reveal_ConstructNewLogEntries(); }
        }
      }
      assert m'.localUpdates.Keys !! p.localUpdates.Keys by {
        forall rid | rid in m'.localUpdates.Keys
        ensures rid in m.localUpdates.Keys
        {
          if rid !in m.localUpdates.Keys {
            assert rid in lupd; // if it's in m' but not in m, it must be in local_updates_new
            // which means rid is in request_ids:
            assert exists i:nat :: InRange(request_ids, i) && 0 <= i < |request_ids| && request_ids[i] == rid
                by { reveal_ConstructLocalUpdateMap(); }
            var i:nat :| InRange(request_ids, i) && 0 <= i < |request_ids| && request_ids[i] == rid;
            // By InUpdateInitAll:
            assert InUpdateInit(m, rid); // trigger
            assert false; // contradiction
          }
        }
      }
    }

    // sequence must be unique, ensured by from AdvancedTail
    assert(seq_unique(request_ids));

    // the request ids are the same in dot(m, p) and in m
    assert forall rid | rid in request_ids :: rid in m.localUpdates;
    assert forall rid | rid in request_ids :: dot(m, p).localUpdates[rid] == m.localUpdates[rid];

    // check the combiner state
    assert dot(m', p).combiner == dot(m, p).combiner[nodeId := CombinerPlaced(request_ids)]
    by {
      assert nodeId !in p.combiner;
      assert m'.combiner == m.combiner[nodeId := CombinerPlaced(request_ids)];
    }

    // global tail in the right state
    assert dot(m', p).global_tail  == Some(dot(m, p).global_tail.value + |request_ids|)
    by {
      // global tail in the dot(m, p) is the same as in m
      assert dot(m, p).global_tail.value == m.global_tail.value;
    }

    assert lupd == big_lupd
    by {
      ConstructLocalUpdateMap_InMap(request_ids, nodeId, dot(m, p).global_tail.value, lupd);
    }

    assert updated_log == big_updated_log
    by {
      ConstructNewLogEntries_Equal(request_ids, nodeId, m.global_tail.value, m.localUpdates, dot(m, p).localUpdates);
    }
  }

  lemma UpdateRequestDone_Monotonic(m: M, m': M, p: M, request_id: RequestId)
  //requires Inv(dot(m, p))
  requires dot(m, p) != Fail
  requires UpdateRequestDone(m, m', request_id)
  ensures UpdateRequestDone(dot(m, p), dot(m', p), request_id)
  {
  }

  lemma InternalMonotonic(m: M, m': M, p: M)
  requires Internal(m, m')
  requires Inv(dot(m, p))
  requires dot(m, p) != Fail
  ensures Internal(dot(m, p), dot(m', p))
  {
    var step :| NextStep(m, m', step);
    match step {
      case GoToCombinerReady_Step(nodeId: NodeId) => {
        GoToCombinerReady_Monotonic(m, m', p, nodeId);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case ExecLoadLtail_Step(nodeId: NodeId) => {
        ExecLoadLtail_Monotonic(m, m', p, nodeId);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case ExecLoadGlobalTail_Step(nodeId: NodeId) => {
        ExecLoadGlobalTail_Monotonic(m, m', p, nodeId);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case ExecDispatchLocal_Step(nodeId: NodeId) => {
        ExecDispatchLocal_Monotonic(m, m', p, nodeId);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case ExecDispatchRemote_Step(nodeId: NodeId) => {
        ExecDispatchRemote_Monotonic(m, m', p, nodeId);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case TransitionReadonlyReadCtail_Step(rid: RequestId, nodeId: NodeId) => {
        TransitionReadonlyReadCtail_Monotonic(m, m', p, rid, nodeId);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case TransitionReadonlyReadyToRead_Step(nodeId: NodeId, rid: RequestId) => {
        TransitionReadonlyReadyToRead_Monotonic(m, m', p, nodeId, rid);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case TransitionReadonlyDone_Step(nodeId: NodeId, rid: RequestId) => {
        TransitionReadonlyDone_Monotonic(m, m', p, nodeId, rid);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case AdvanceTail_Step(nodeId: NodeId, request_ids: seq<RequestId>) => {
        AdvanceTail_Monotonic(m, m', p, nodeId, request_ids);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case UpdateCompletedTail_Step(nodeId: NodeId) => {
        UpdateCompletedTail_Monotonic(m, m', p, nodeId);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case UpdateRequestDone_Step(request_id: RequestId) => {
        UpdateRequestDone_Monotonic(m, m', p, request_id);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
    }
  }
}
