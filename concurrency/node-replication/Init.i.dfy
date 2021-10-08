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
  import Tokens = TicketStubToken(nrifc, IL)

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

  method make_buffer_cells()
  returns (linear cells: lseq<Cell<LogEntry>>,
      glinear cell_contents: map<nat, StoredType>)
  ensures |cells| == BUFFER_SIZE as int
  ensures forall i | 0 <= i < |cells| :: i in cells
  ensures forall i | -(BUFFER_SIZE as int) <= i < 0 :: i in cell_contents
      && cell_contents[i].cellContents.cell == cells[i % BUFFER_SIZE as int]
  ensures forall i | i in cell_contents ::
      -(BUFFER_SIZE as int) <= i < 0

  method make_buffer(
      linear cells: lseq<Cell<LogEntry>>, 
      glinear alive: map<nat, AliveBit>)
  returns (linear buffer: lseq<BufferEntry>)
  requires |cells| == BUFFER_SIZE as int
  requires forall i | 0 <= i < BUFFER_SIZE as int ::
      && i in cells
      && i in alive
      && alive[i] == AliveBit(i, false)
  ensures |buffer| == BUFFER_SIZE as int
  ensures forall i | 0 <= i < BUFFER_SIZE as int
    :: i in buffer && buffer[i].cell == cells[i]
        && buffer[i].WF(i)

  method make_node_infos(
      glinear localTails: map<nat, LocalTail>,
      glinear cbLocalTails: map<nat, CBLocalTail>)
  returns (linear node_info: lseq<NodeInfo>)
  requires forall i | 0 <= i < NUM_REPLICAS as int ::
      && i in localTails
      && i in cbLocalTails
      && localTails[i] == LocalTail(i as int, 0)
      && cbLocalTails[i] == CBLocalTail(i as int, 0)
  ensures |node_info| == NUM_REPLICAS as int
  ensures forall i | 0 <= i < NUM_REPLICAS as int
      :: i in node_info && node_info[i].WF(i)

  method make_node_creation_tokens(
      glinear replicas: map<nat, Replica>,
      glinear combiners: map<nat, CombinerToken>,
      glinear readers: map<nat, Reader>)
  returns (linear nodeCreationTokens: lseq<NodeCreationToken>)
  requires forall i | 0 <= i < NUM_REPLICAS as int ::
      && i in replicas
      && i in combiners
      && i in readers
      && replicas[i] == Replica(i, nrifc.init_state())
      && combiners[i] == CombinerToken(i, CombinerReady)
      && readers[i] == Reader(i, ReaderIdle)
  ensures |nodeCreationTokens| == NUM_REPLICAS as int
  ensures forall i | 0 <= i < NUM_REPLICAS as int
      :: i in nodeCreationTokens && nodeCreationTokens[i].WF()

  method initNR(glinear token: Tokens.Token)
  returns (
      linear nr: NR,
      linear nodeCreationTokens: lseq<NodeCreationToken>
      )
  requires token.loc == loc()
  requires IL.Init(token.val)
  ensures nr.WF()
  ensures |nodeCreationTokens| == NUM_REPLICAS as int
  ensures forall i | 0 <= i < |nodeCreationTokens| ::
      i in nodeCreationTokens && nodeCreationTokens[i].WF()
  {
    linear var buffer_cells;
    glinear var buffer_cell_contents;
    buffer_cells, buffer_cell_contents := make_buffer_cells();

    glinear var globalTail, replicas, localTails, ctail, combiners := perform_Init(token);
    glinear var cbHead, cbGlobalTail, cbLocalTails, alive, cbContents, readers :=
        cyclic_buffer_init(buffer_cell_contents);

    linear var ctail_atomic: Atomic<uint64, Ctail> := new_atomic(
        0,
        ctail,
        (v, g) => g == Ctail(v as int),
        0);
    linear var head_atomic: Atomic<uint64, CBHead> := new_atomic(
        0,
        cbHead,
        (v, g) => g == CBHead(v as int),
        0);
    linear var globalTail_atomic: Atomic<uint64, GlobalTailTokens> := new_atomic(
          0,
          GlobalTailTokens(globalTail, cbGlobalTail),
          ((v, g) => g == GlobalTailTokens(GlobalTail(v as int), CBGlobalTail(v as int))),
          0);

    linear var buffer: lseq<BufferEntry> := make_buffer(buffer_cells, alive);

    glinear var bufferContents: GhostAtomic<Contents> := new_ghost_atomic(
        cbContents,
        (g) => ContentsInv(buffer, g),
        1);

    linear var node_infos: lseq<NodeInfo> := make_node_infos(localTails, cbLocalTails);

    nr := NR(ctail_atomic, head_atomic, globalTail_atomic, node_infos, buffer, bufferContents);

    nodeCreationTokens := make_node_creation_tokens(replicas, combiners, readers);
  }
}
