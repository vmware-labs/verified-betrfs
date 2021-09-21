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
    && var readRequest := m.localReads[rid];

    // TODO require us to be in 'CombinerReady' state
    // && InCombinerReady(m, readRequest.nodeId)

    // perform the read operation from the replica
    && var ret := nrifc.read(m.replicas[readRequest.nodeId], readRequest.op);

    // construct the new state
    && var newst := ReadonlyDone(ret);
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

  // https://stackoverflow.com/questions/52610402/updating-a-map-with-another-map-in-dafny
  function update_map<K(!new), V>(m1: map<K, V>, m2: map<K, V>): map<K, V>
  ensures
    (forall k :: k in m1 || k in m2 ==> k in update_map(m1, m2)) &&
    (forall k :: k in m2 ==> update_map(m1, m2)[k] == m2[k]) &&
    (forall k :: !(k in m2) && k in m1 ==> update_map(m1, m2)[k] == m1[k]) &&
    (forall k :: !(k in m2) && !(k in m1) ==> !(k in update_map(m1, m2)))
  {
    map k | k in (m1.Keys + m2.Keys) :: if k in m2 then m2[k] else m1[k]
  }


  predicate RequestIdsValidAndUpdateInit(request_ids: seq<RequestId>, localUpdates: map<RequestId, UpdateState>)
  {
    forall rid | rid in request_ids :: (rid in localUpdates &&  localUpdates[rid].UpdateInit?)
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
    && RequestIdsValidAndUpdateInit(request_ids, m.localUpdates)

    && var global_tail_var := m.global_tail.value;

    // Question(RA): this one here should be part of the invariant, and not of this predicate
    // && (forall i | global_tail_var <= i < global_tail_var+|request_ids| :: i !in m.log.Keys)

    // Add new entries to the log:
    && var updated_log := (map idx | global_tail_var <= idx < global_tail_var+|request_ids| :: LogEntry(m.localUpdates[request_ids[idx-global_tail_var]].op, nodeId));

    // the new combiner state
    && var combiner_state_new := CombinerPlaced(request_ids);

    // calculate the new global tail
    && var global_tail_new := m.global_tail.value + |request_ids|;

    // construct the new local updates, and record the placed updates
    && var local_updates_new := (map rid | rid in request_ids :: UpdatePlaced(nodeId));

    && m.log.Keys * updated_log.Keys == {}

    // update the state
    && m' == m.(log := update_map(m.log, updated_log))
              .(localUpdates := update_map(m.localUpdates, local_updates_new))
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

    && c.queued_ops[queue_index] in m.localUpdates // NOTE(travis): added this

    // update the combiner state by incrementing the current local tail
    &&  var c_new := c.(localTail := c.localTail + 1);

    // update the state
    && m' == m.(combiner := m.combiner[nodeId := c_new])
              .(replicas := m.replicas[nodeId := nr_state'])
              .(localUpdates := m.localUpdates[c.queued_ops[queue_index]:= UpdateDone(ret)])
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
    && var new_ctail := if m.ctail.value > c.localTail then m.ctail.value else c.localTail;
    // construct the new combiner state
    && var newst := CombinerUpdatedCtail(c.queued_ops, c.localTail);
    // update the ctail and the combiner state
    && m' == m.(combiner := m.combiner[nodeId := newst])
              .(ctail := Some(new_ctail))
  }

  // STATE TRANSITION: CombinerUpdatedCtail -> CombinerReady
  //
  // Update the local tail pointer of the replica to the stored global tail
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

  /*
   * ============================================================================================
   * State merging etc.
   * ============================================================================================
   */


// update the map
// Question: precedence between m1 and m2, currently always take m1 first
function map_union<K,V>(m1: map<K,V>, m2: map<K,V>) : map<K,V> {
    map k | k in m1.Keys + m2.Keys ::
        (if k in m1.Keys then m1[k] else m2[k])
  }

  // tips for implementing dot:
  // you should probably be able to find a map_union function in the codebase you can steal
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
      map_union(x.log, y.log),
      if x.global_tail.Some? then x.global_tail else y.global_tail,
      map_union(x.replicas, y.replicas),
      map_union(x.localTails, y.localTails),
      if x.ctail.Some? then x.ctail else y.ctail,
      map_union(x.localReads, y.localReads),
      map_union(x.localUpdates, y.localUpdates),
      map_union(x.combiner, y.combiner)
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

  // Travis: should be UpdateDone or ReadonlyDone
  function Stub(rid: RequestId, output: IOIfc.Output) : M {
      // RS: How do we represent that the rid should be in one of localReads
      // or localUpdates?
      dot(ReadOp(rid, ReadonlyDone(output)), UpdateOp(rid, UpdateDone(output)))
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
    && forall i | i in s.localTails :: s.localTails[i] == 0
    // all combiners are in ready state
    && forall i | i in s.combiner :: s.combiner[i] == CombinerReady

    // all replicas should be identical
    && forall i | i in s.replicas :: s.replicas[i] == nrifc.init_state()

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

    // the log doesn't contain entries above the global tail
    && (forall idx : nat | idx >= s.global_tail.value :: idx !in s.log.Keys)


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

  lemma ConsumeStubPreservesInv(whole: M, whole': M, rid: RequestId, output: IOIfc.Output)
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

  }

  lemma state_at_version_preserves(a: map<nat, LogEntry>, b: map<nat, LogEntry>, i: nat)
  requires forall k | 0 <= k < i :: k in a && k in b && a[k] == b[k]
  ensures state_at_version(a, i) == state_at_version(b, i)
  decreases i
  {
  }

  lemma AdvanceTail_PreservesInv(m: M, m': M, nodeId: NodeId, request_ids: seq<RequestId>)
    requires Inv(m)
    requires AdvanceTail(m, m', nodeId, request_ids)
    ensures Inv(m')
  {
    forall nid | nid in m'.replicas
      ensures m'.replicas[nid] == state_at_version(m'.log, get_local_tail(m', nid))
      {
        state_at_version_preserves(m.log, m'.log, get_local_tail(m', nid));
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

  lemma InternalMonotonic(m: M, m': M, p: M)
  requires Internal(m, m')
  requires Inv(dot(m, p))
  requires dot(m, p) != Fail
  ensures Internal(dot(m, p), dot(m', p))
  {
    var step :| NextStep(m, m', step);
    match step {
      case GoToCombinerReady_Step(nodeId: NodeId) => {
        assert GoToCombinerReady(dot(m, p), dot(m', p), nodeId);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case ExecLoadLtail_Step(nodeId: NodeId) => {
        assert ExecLoadLtail(dot(m, p), dot(m', p), nodeId);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case ExecLoadGlobalTail_Step(nodeId: NodeId) => {
        assert ExecLoadGlobalTail(dot(m, p), dot(m', p), nodeId);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case ExecDispatchLocal_Step(nodeId: NodeId) => {
        /*
        var c := m.combiner[nodeId];
        var UpdateResult(nr_state', ret) := nrifc.update(m.replicas[nodeId], m.log[c.localTail].op);
        var c_new := c.(localTail := c.localTail + 1);
        var queue_index := |c.queued_ops| - (c.globalTail - c.localTail);
        assert dot(m', p).combiner == dot(m, p).combiner[nodeId := c_new];
        assert dot(m', p).replicas == dot(m, p).replicas[nodeId := nr_state'];
        assert dot(m', p).localUpdates == dot(m, p).localUpdates[c.queued_ops[queue_index]:= UpdateDone(ret)];
        */
        assert ExecDispatchLocal(dot(m, p), dot(m', p), nodeId);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case ExecDispatchRemote_Step(nodeId: NodeId) => {
        assert ExecDispatchRemote(dot(m, p), dot(m', p), nodeId);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case TransitionReadonlyReadCtail_Step(rid: RequestId, nodeId: NodeId) => {
        assert TransitionReadonlyReadCtail(dot(m, p), dot(m', p), rid, nodeId);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case TransitionReadonlyReadyToRead_Step(nodeId: NodeId, rid: RequestId) => {
        assert TransitionReadonlyReadyToRead(dot(m, p), dot(m', p), nodeId, rid);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case TransitionReadonlyDone_Step(nodeId: NodeId, rid: RequestId) => {
        assert TransitionReadonlyDone(dot(m, p), dot(m', p), nodeId, rid);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case AdvanceTail_Step(nodeId: NodeId, request_ids: seq<RequestId>) => {
        assert AdvanceTail(dot(m, p), dot(m', p), nodeId, request_ids);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
      case UpdateCompletedTail_Step(nodeId: NodeId) => {
        assert UpdateCompletedTail(dot(m, p), dot(m', p), nodeId);
        assert NextStep(dot(m, p), dot(m', p), step);
      }
    }
  }

  // import NRSimple
  // include "NRSimple.i.dfy"

  // // interpretation function
  // function I(m: M) : NRSimple.Variables
  // {
  //   NRSimple.Variables(
  //     // log: seq<nrifc.UpdateOp>,
  //     // ctail: nat,
  //     // readonly_reqs: map<RequestId, ReadReq>,
  //     // update_reqs: map<RequestId, nrifc.UpdateOp>,
  //     // update_resps: map<RequestId, UpdateResp>
  //   )
  // }

  // // refinement
  // lemma InfiniteLog_Refines_NRSimple_NextStep(m: M, m' : M, op: nrifc.Op, step: Step)
  //   requires Inv(m)
  //   requires NextStep(m, m', op, step)
  //   requires Inv(m')
  //   ensures NRSimple.Next(I(m), I(m'), op)
  // {

  // }

  // lemma InfiniteLog_Refines_NRSimple_Next(m: M, m' : M,  op: nrifc.Op)
  //   requires Inv(m)
  //   requires Inv(m')
  //   requires Next(m, m', op, step)
  //   ensures NRSimple.Next(I(m), I(m'), op)
  // {
  //   var step :| NextStep(m, m', op, step);
  //   InfiniteLog_Refines_NRSimple_NextStep(m, m', op, step);
  // }

  // lemma InfiniteLog_Refines_NRSimple_Init(m: M)
  //   requires Init(m)
  //   ensures NRSimple.init(I(m))
  // {

  // }
}
