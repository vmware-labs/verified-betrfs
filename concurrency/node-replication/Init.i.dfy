include "Impl.i.dfy"

module Init(nrifc: NRIfc) {
  import opened RequestIds
  import opened Atomics
  import opened ILT = InfiniteLogTokens(nrifc)
  import opened IL = InfiniteLogSSM(nrifc)
  import opened CBT = CyclicBufferTokens(nrifc)
  import opened FCT = FlatCombinerTokens
  import opened LinearSequence_i
  import opened LinearSequence_s
  import opened NativeTypes
  import opened RwLockImpl
  import opened Runtime
  import opened ThreadUtils
  import opened Ptrs
  import opened GlinearMap
  import opened GlinearOption
  import opened Cells
  import opened GhostLoc
  import opened Impl = Impl(nrifc)
  import opened Constants

  linear datatype NodeCreationToken = NodeCreationToken(
    nodeId: uint64,
    glinear combiner: CombinerToken,
    glinear reader: Reader,
    glinear ghost_replica: Replica)
  {
    predicate WF()
    {
      && 0 <= nodeId as int < NUM_REPLICAS as int
      && ghost_replica == Replica(nodeId as int, nrifc.init_state())
      && combiner == CombinerToken(nodeId as int, CombinerReady)
      && reader == Reader(nodeId as int, ReaderIdle)
    }
  }

  linear datatype ThreadOwnedContext = ThreadOwnedContext(
    tid: uint64,
    glinear fc_client: FCClient,
    glinear cell_contents: CellContents<OpResponse>)
  {
    predicate WF(node: Node)
    {
      && node.WF()
      && fc_client == FCClient(node.fc_loc, tid as nat, FCClientIdle)
      && 0 <= tid < MAX_THREADS_PER_REPLICA
      && cell_contents.cell == node.contexts[tid as nat].cell
    }
  }

  method initNode(linear nct: NodeCreationToken)
  returns (linear node: Node, linear owned_contexts: lseq<ThreadOwnedContext>)
  requires nct.WF()
  ensures node.WF()
  ensures |owned_contexts| == MAX_THREADS_PER_REPLICA as int
  ensures forall i | 0 <= i < |owned_contexts| ::
    i in owned_contexts && owned_contexts[i].WF(node)
  {
    linear var NodeCreationToken(nodeId, combiner, reader, ghost_replica) := nct;

    // initialize the flat_combiner ghost tokens

    glinear var fc_clients, fc_slots, fc_combiner := fc_initialize();
    ghost var fc_loc := fc_combiner.loc;

    // build stuff

    linear var combiner_atomic := new_atomic(0, UnitGhostType, (v, g) => true, 0);
    linear var actual_replica := nrifc.initialize();
    linear var nodeReplica := NodeReplica(
      actual_replica, ghost_replica, combiner, reader);
    linear var replica := new_mutex(nodeReplica, (v: NodeReplica) => v.WF(nodeId as int));

    // thread contexts

    linear var contexts := lseq_alloc<Context>(MAX_THREADS_PER_REPLICA);
    owned_contexts := lseq_alloc<ThreadOwnedContext>(MAX_THREADS_PER_REPLICA);
    var i := 0;
    while i < MAX_THREADS_PER_REPLICA
    invariant 0 <= i <= MAX_THREADS_PER_REPLICA
    invariant |contexts| == MAX_THREADS_PER_REPLICA as int
    invariant |owned_contexts| == MAX_THREADS_PER_REPLICA as int
    invariant forall j: nat | 0 <= j < i as int ::
        j in contexts && j in owned_contexts
    invariant forall j: nat | i as int <= j < MAX_THREADS_PER_REPLICA as int ::
        j !in contexts && j !in owned_contexts
    invariant forall j: nat | 0 <= j < i as int ::
        && owned_contexts[j].tid as int == j
        && owned_contexts[j].fc_client == FCClient(fc_loc, j, FCClientIdle)
        && owned_contexts[j].cell_contents.cell == contexts[j].cell
    invariant forall j: nat | 0 <= j < i as int ::
        contexts[j].WF(j, fc_loc)
    invariant forall j: nat | i as int <= j < MAX_THREADS_PER_REPLICA as int ::
        j in fc_slots && fc_slots[j] == FCSlot(fc_loc, j, FCEmpty)
    invariant forall j: nat | i as int <= j < MAX_THREADS_PER_REPLICA as int ::
        j in fc_clients && fc_clients[j] == FCClient(fc_loc, j, FCClientIdle)
    {
      glinear var fc_client, fc_slot;
      fc_clients, fc_client := glmap_take(fc_clients, i as int);
      fc_slots, fc_slot := glmap_take(fc_slots, i as int);

      var dummy_op :| true;
      var dummy_ret :| true;
      linear var ctx_cell;
      glinear var ctx_cell_contents;
      ctx_cell, ctx_cell_contents := new_cell(OpResponse(dummy_op, dummy_ret));

      glinear var ctx_ghost := ContextGhost(glNone, fc_slot, glNone);
      linear var ctx_atomic := new_atomic(0, ctx_ghost,
          (v, g: ContextGhost) => g.inv(v, i as int, ctx_cell, fc_loc), 0);

      linear var toc := ThreadOwnedContext(i, fc_client, ctx_cell_contents);
      linear var c := Context(ctx_atomic, ctx_cell);

      lseq_give_inout(inout contexts, i, c);
      lseq_give_inout(inout owned_contexts, i, toc);

      i := i + 1;
    }

    dispose_anything(fc_clients); // this are now empty
    dispose_anything(fc_slots); // this are now empty

    dispose_anything(fc_combiner); // TODO this should be put in combiner lock

    node := Node(combiner_atomic, replica, contexts, nodeId, fc_loc);
  }
}
