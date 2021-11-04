include "InfiniteLogTokens.i.dfy"
include "NRSpec.s.dfy"
include "../../lib/Lang/LinearSequence.i.dfy"
include "rwlock/Impl.i.dfy"
include "../framework/Atomic.s.dfy"
include "../framework/ThreadUtils.s.dfy"
include "../framework/Ptrs.s.dfy"
include "../framework/GlinearMap.s.dfy"
include "../framework/Cells.s.dfy"
include "Runtime.i.dfy"
include "CyclicBufferTokens.i.dfy"
include "FlatCombinerTokens.i.dfy"
include "../../lib/Base/Option.s.dfy"

module NodeReplica(nrifc: NRIfc) refines ContentsTypeMod {
  import opened O = Options
  import opened ILT = InfiniteLogTokens(nrifc)    // Replica, CombinerToken
  import opened IL = InfiniteLogSSM(nrifc)        // NodeId
  import opened CBT = CyclicBufferTokens(nrifc)   // CBCombinerToken
  import opened LC = LinearCells

  linear datatype NodeReplica = NodeReplica(
    linear actual_replica: nrifc.DataStructureType,
    glinear ghost_replica: Replica,
    glinear combiner: CombinerToken,
    glinear cb: CBCombinerToken
  )
  {
    predicate WF(nodeId: nat) {
      && ghost_replica.state == nrifc.I(actual_replica)
      && ghost_replica.nodeId == nodeId
      && combiner.state == CombinerReady
      && combiner.nodeId == nodeId
      && cb.nodeId == nodeId
      && cb.rs.CBCombinerIdle?
    }
  }

  type ContentsType = NodeReplica
}

module Impl(nrifc: NRIfc) {
  import opened RequestIds
  import opened Atomics
  import opened ILT = InfiniteLogTokens(nrifc)
  import opened IL = InfiniteLogSSM(nrifc)
  import opened CBT = CyclicBufferTokens(nrifc)
  import opened FCT = FlatCombinerTokens
  import opened LinearSequence_i
  import opened LinearSequence_s
  import opened NativeTypes
  import opened NodeReplicaApplied = NodeReplica(nrifc)
  import opened RwLockImpl(NodeReplica(nrifc))
  import opened Runtime
  import opened ThreadUtils
  import opened Ptrs
  import opened GlinearMap
  import opened GlinearOption
  import opened Cells
  import opened GhostLoc
  import opened Constants
  import opened ClientCounter

  type Tid = uint64

  /*
   * Anything which is allocated on a NUMA node
   */

  datatype OpResponse = OpResponse(op: nrifc.UpdateOp, ret: nrifc.ReturnType)

  glinear datatype ContextGhost = ContextGhost(
    glinear contents: glOption<CellContents<OpResponse>>,
    glinear fc: FCSlot,
    glinear update: glOption<Update>
  )
  {
    predicate inv(v: uint64, i: nat, cell: Cell<OpResponse>, fc_loc: Loc)
    {
      && fc.tid == i
      && fc.loc == fc_loc
      && (v == 0 || v == 1 || v == 2)
      && (v == 0 ==> fc.state.FCEmpty? || fc.state.FCResponse?)
      && (v == 1 ==> fc.state.FCRequest?)
      && (v == 2 ==> fc.state.FCInProgress?)
      && (fc.state.FCEmpty? ==>
        && update.glNone?
        && contents.glNone?
      )
      && (fc.state.FCRequest? ==>
        && update.glSome?
        && contents.glSome?
        && update.value.us.UpdateInit?
        && update.value.rid == fc.state.rid
        && contents.value.cell == cell
        && contents.value.v.op == update.value.us.op
      )
      && (fc.state.FCInProgress? ==>
        && update.glNone?
        && contents.glNone?
      )
      && (fc.state.FCResponse? ==>
        && update.glSome?
        && contents.glSome?
        && update.value.us.UpdateDone?
        && update.value.rid == fc.state.rid
        && contents.value.cell == cell
        && contents.value.v.ret == update.value.us.ret
      )
    }
  }

  linear datatype Context = Context(
    linear atomic: Atomic<uint64, ContextGhost>,
    linear cell: Cell<OpResponse>
  )
  {
    predicate WF(i: nat, fc_loc: Loc)
    {
      (forall v, g :: atomic_inv(atomic, v, g) <==> g.inv(v, i, cell, fc_loc))
    }
  }

  glinear datatype UnitGhostType = UnitGhostType

  glinear datatype CombinerLockState = CombinerLockState(glinear flatCombiner: FCCombiner, glinear gops: LC.LCellContents<seq<nrifc.UpdateOp>>, glinear gresponses: LC.LCellContents<seq<nrifc.ReturnType>>)

  linear datatype Node = Node(
    linear combiner_lock: Atomic<uint64, glOption<CombinerLockState>>,
    // protected by the `combiner_lock`
    linear ops: LC.LinearCell<seq<nrifc.UpdateOp>>,
    // protected by the `combiner_lock`
    linear responses: LC.LinearCell<seq<nrifc.ReturnType>>,
    linear replica: RwLock,
    //linear context: map<Tid, nrifc.UpdateOp>,
    linear contexts: lseq<Context>, // TODO cache-line padded?
    nodeId: uint64,
    //next: Atomic<Tid, ()>

    ghost fc_loc: Loc
  )
  {
    predicate WF() {
      && (forall nodeReplica :: replica.inv(nodeReplica) <==> nodeReplica.WF(nodeId as int))
      && 0 <= nodeId as int < NUM_REPLICAS as int
      && |contexts| == MAX_THREADS_PER_REPLICA as int
      && (forall i | 0 <= i < |contexts| :: i in contexts && contexts[i].WF(i, fc_loc))
      && (forall v, g :: atomic_inv(combiner_lock, v, g) <==> (
        && ((v == 0) <==> (
          && g.glSome? 
          && g.value.flatCombiner.state == FCCombinerCollecting(0, [])
          && g.value.flatCombiner.loc == fc_loc
          && g.value.gops.v.Some?
          && g.value.gops.lcell == ops
          && |g.value.gops.v.value| == MAX_THREADS_PER_REPLICA as int
          && g.value.gresponses.v.Some?
          && g.value.gresponses.lcell == responses
          && |g.value.gresponses.v.value| == MAX_THREADS_PER_REPLICA as int
        ))
        && ((v > 0) <==> g.glNone?)))
      && replica.InternalInv()
    }
  }

  /*
   * Per-thread
   */

  linear datatype ThreadOwnedContext = ThreadOwnedContext(
    tid: uint64,
    glinear fc_client: FCClient,
    glinear cell_contents: CellContents<OpResponse>,
    glinear client_counter: Client)
  {
    predicate WF(node: Node)
    {
      && node.WF()
      && fc_client == FCClient(node.fc_loc, tid as nat, FCClientIdle)
      && 0 <= tid < MAX_THREADS_PER_REPLICA
      && cell_contents.cell == node.contexts[tid as nat].cell
      && client_counter.loc == node.replica.loc
    }
  }


  /*
   * Central cyclic buffer stuff
   */

  glinear datatype LocalTailTokens = LocalTailTokens(
      glinear localTail: LocalTail,
      glinear cbLocalTail: CBLocalTail)

  glinear datatype GlobalTailTokens = GlobalTailTokens(
      glinear globalTail: GlobalTail,
      glinear cbGlobalTail: CBGlobalTail)

  linear datatype {:alignment 128} NodeInfo = NodeInfo(
    linear localTail: Atomic<uint64, LocalTailTokens>
  )
  {
    predicate WF(nodeId: nat) {
      && (forall v, g :: atomic_inv(localTail, v, g) <==>
          g == LocalTailTokens(LocalTail(nodeId, v as int), CBLocalTail(nodeId, v as int)))
    }
  }

  linear datatype BufferEntry = BufferEntry(
    linear cell: Cell<ConcreteLogEntry>,
    linear alive: Atomic<bool, CBAliveBit>)
  {
    predicate WF(i: nat)
    {
      && (forall v, g :: atomic_inv(alive, v, g) <==> g == CBAliveBit(i, v))
      && alive.namespace() == 0
    }
  }

  predicate BufferEntryInv(buffer: lseq<BufferEntry>, i: int, t: StoredType)
  requires |buffer| == BUFFER_SIZE as int
  {
    && t.cellContents.cell == buffer[i % BUFFER_SIZE as int].cell
    && (i >= 0 ==>
      && t.logEntry.glSome?
      && t.logEntry.value.op == t.cellContents.v.op
      && t.logEntry.value.node_id == t.cellContents.v.node_id as int
      && t.logEntry.value.idx == i
    )
  }

  predicate ContentsInv(buffer: lseq<BufferEntry>, contents: Contents)
  requires |buffer| == BUFFER_SIZE as int
  {
    && (forall i | i in contents.contents :: BufferEntryInv(buffer, i, contents.contents[i]))
  }

  linear datatype NR = NR(
    linear ctail: CachePadded<Atomic<uint64, Ctail>>,
    linear head: CachePadded<Atomic<uint64, CBHead>>,
    linear globalTail: CachePadded<Atomic<uint64, GlobalTailTokens>>,
    linear node_info: lseq<NodeInfo>, // NodeInfo is padded

    linear buffer: lseq<BufferEntry>,
    glinear bufferContents: GhostAtomic<Contents>
  )
  {
    predicate WF() {
      && (forall v, g :: atomic_inv(ctail.inner, v, g) <==> g == Ctail(v as int))
      && (forall v, g :: atomic_inv(head.inner, v, g) <==> g == CBHead(v as int))
      && (forall v, g :: atomic_inv(globalTail.inner, v, g) <==>
            g == GlobalTailTokens(GlobalTail(v as int), CBGlobalTail(v as int)))
      && |node_info| == NUM_REPLICAS as int
      && (forall nodeId | 0 <= nodeId < |node_info| :: nodeId in node_info)
      && (forall nodeId | 0 <= nodeId < |node_info| :: node_info[nodeId].WF(nodeId))
      && |buffer| == BUFFER_SIZE as int
      && (forall v, g :: atomic_inv(bufferContents, v, g) <==> ContentsInv(buffer, g))
      && (forall i: nat | 0 <= i < BUFFER_SIZE as int :: i in buffer)
      && (forall i: nat | 0 <= i < BUFFER_SIZE as int :: buffer[i].WF(i))

      && bufferContents.namespace() == 1
      && globalTail.inner.namespace() == 0
    }
  }

  // https://github.com/vmware/node-replication/blob/1d92cb7c040458287bedda0017b97120fd8675a7/nr/src/log.rs#L708
  method is_replica_synced_for_reads(shared nr: NR, nodeId: uint64, ctail: uint64, 
          glinear ticket: Readonly) 
  returns (is_synced: bool, glinear ticket': Readonly) 
  requires ticket.rs.ReadonlyCtail?
  //requires ticket.rs.ctail <= ctail as nat
  requires nr.WF()
  requires nodeId < NUM_REPLICAS
  ensures is_synced ==> ticket'.rs.ReadonlyReadyToRead?
  ensures !is_synced ==> ticket' == ticket
  ensures ticket.rid == ticket'.rid
  ensures is_synced ==> ticket'.rs.nodeId == nodeId as nat
  ensures ticket.rs.op == ticket'.rs.op
  {
    atomic_block var local_tail := execute_atomic_load(lseq_peek(nr.node_info, nodeId).localTail) { 
      ghost_acquire local_tail_token;

      // TODO: maybe remove?
      assert local_tail_token.localTail == LocalTail(nodeId as nat, local_tail as nat); 

      // perform transition of ghost state here ...
      if local_tail_token.localTail.localTail >= ctail as nat {
        assert local_tail_token.localTail.localTail >= ctail as nat;
        ticket' := perform_TransitionReadonlyReadyToRead(ticket, local_tail_token.localTail);
      }
      else {
        ticket' := ticket;
      }

      ghost_release local_tail_token;
    }

    is_synced := local_tail >= ctail;
  }

  // https://github.com/vmware/node-replication/blob/1d92cb7c040458287bedda0017b97120fd8675a7/nr/src/replica.rs#L584
  method try_combine(shared nr: NR, shared node: Node, tid: uint64)
  // requires tid > 0, rust version had tid > 0, in dafny we do tid >= 0
  requires tid < MAX_THREADS_PER_REPLICA
  requires nr.WF()
  requires node.WF()
  decreases *
  {
    // Check `combiner_lock` a few times until it appears to be free...
    var i: uint64 := 0;
    while i < 5
    invariant 0 <= i <= 5
    {
      atomic_block var combiner_lock := execute_atomic_load(node.combiner_lock) {
        ghost_acquire combiner_lock_token;
        ghost_release combiner_lock_token;
      }
      if combiner_lock != 0 {
        return;
      }
      i := i + 1;
    }

    glinear var fcStateOpt: glOption<FCCombiner>;
    glinear var gops: glOption<LC.LCellContents<seq<nrifc.UpdateOp>>>;
    glinear var gresponses: glOption<LC.LCellContents<seq<nrifc.ReturnType>>>;
    
    // Try and acquire the lock... (tid+1 because we reserve 0 as "no-one holds the lock")
    atomic_block var success := execute_atomic_compare_and_set_weak(node.combiner_lock, 0, tid + 1) {
      ghost_acquire contents;
      if success {
        assert contents.glSome?;
        //assert old_value == 0;
        glinear var CombinerLockState(flatCombiner, go, gr) := unwrap_value(contents);
        fcStateOpt := glSome(flatCombiner);
        gops := glSome(go);
        gresponses := glSome(gr);
        contents := glNone;
      } else {
        fcStateOpt := glNone;
        gops := glNone;
        gresponses := glNone;
      }
      ghost_release contents;
    }

    if success {
      assert fcStateOpt.glSome?;
      assert gops.glSome?;
      assert gresponses.glSome?;

      linear var ops;
      linear var responses;

      linear var ops';
      linear var responses';

      glinear var gops';
      glinear var gresponses';
      glinear var fcstate';
      
      ops, gops' := LC.take_lcell(node.ops, unwrap_value(gops));
      responses, gresponses' := LC.take_lcell(node.responses, unwrap_value(gresponses));

      ops', responses', fcstate' := combine(nr, node, ops, responses, unwrap_value(fcStateOpt));

      glinear var gops'' := LC.give_lcell(node.ops, gops', ops');
      glinear var gresponses'' := LC.give_lcell(node.responses, gresponses', responses');

      // Release combiner_lock
      atomic_block var _ := execute_atomic_store(node.combiner_lock, 0) {
        ghost_acquire contents;
        //assert old_value > 0; // doesn't believe me
        //assert contents.glNone?;

        //assert fcstate'.state == FCCombinerCollecting(0, []);
        //assert fcstate'.loc == node.fc_loc;
        //assert gops''.v.Some?;
        //assert gops''.lcell == node.ops;
        //assert |gops''.v.value| == MAX_THREADS_PER_REPLICA as int;
        //assert gresponses''.v.Some?;
        //assert gresponses''.lcell == node.responses;
        //assert |gresponses''.v.value| == MAX_THREADS_PER_REPLICA as int;

        dispose_anything(contents);
        contents := glSome(CombinerLockState(fcstate', gops'', gresponses''));
        ghost_release contents;
      }
    }
    else {
      assert gops.glNone?;
      dispose_glnone(fcStateOpt);
      dispose_glnone(gops);
      dispose_glnone(gresponses);
    }
  }

  method combine(shared nr: NR, shared node: Node,
      // these are not inputs or ouputs;
      // they only serve internally as buffers 
      // for ops and responses
      linear ops: seq<nrifc.UpdateOp>,
      linear responses: seq<nrifc.ReturnType>,
      glinear flatCombiner: FCCombiner)
  returns (
      linear ops': seq<nrifc.UpdateOp>,
      linear responses': seq<nrifc.ReturnType>,
      glinear flatCombiner': FCCombiner)
  requires nr.WF() 
  requires node.WF() 
  requires |ops| == MAX_THREADS_PER_REPLICA as int
  requires |responses| == MAX_THREADS_PER_REPLICA as int
  requires flatCombiner.state == FCCombinerCollecting(0, [])
  requires flatCombiner.loc == node.fc_loc
  ensures flatCombiner'.loc == node.fc_loc
  ensures flatCombiner'.state == FCCombinerCollecting(0, [])
  ensures |ops'| == MAX_THREADS_PER_REPLICA as int
  ensures |responses'| == MAX_THREADS_PER_REPLICA as int
  decreases *
  {
    /////// Collect the operations
    glinear var updates, opCellPermissions;
    ghost var requestIds;
    var num_ops;
    ops', num_ops, flatCombiner', requestIds, updates, opCellPermissions :=
        combine_collect(node, ops, flatCombiner);

    /////// Take the rwlock
    linear var rep;
    glinear var guard;
    rep, guard := node.replica.acquire();
    assert rep.WF(node.nodeId as int);
    linear var NodeReplica(actual_replica, ghost_replica, combinerState, cb) := rep;

    /////// append
    actual_replica, responses', ghost_replica, updates, combinerState, cb :=
      append(nr, node, ops', num_ops, actual_replica, responses,
          // ghost stuff
          ghost_replica, requestIds, updates, combinerState, cb);

    /////// exec

    actual_replica, responses',
        ghost_replica, updates, combinerState, cb :=
      exec(nr, node, actual_replica, responses', ghost_replica,
          requestIds, updates, combinerState, cb);

    /////// Release the rwlock

    node.replica.release(
        NodeReplica(actual_replica, ghost_replica, combinerState, cb),
        guard);

    /////// Return responses
    flatCombiner' := combine_respond(
        node, responses', flatCombiner', requestIds,
        updates, opCellPermissions);
  }

  method combine_collect(
      shared node: Node,
      linear ops: seq<nrifc.UpdateOp>,
      glinear flatCombiner: FCCombiner)
  returns (
      linear ops': seq<nrifc.UpdateOp>,
      num_ops: uint64,
      glinear flatCombiner': FCCombiner,
      ghost requestIds: seq<RequestId>,
      glinear updates: map<nat, Update>,
      glinear opCellPermissions: map<nat, CellContents<OpResponse>>)
  requires node.WF()
  requires flatCombiner.loc == node.fc_loc
  requires flatCombiner.state == FCCombinerCollecting(0, [])
  requires |ops| == MAX_THREADS_PER_REPLICA as int
  ensures |ops'| == |ops|
  ensures flatCombiner'.loc == node.fc_loc
  ensures 0 <= num_ops as int <= |ops'|
  ensures flatCombiner'.state.FCCombinerResponding?
      && flatCombiner'.state.idx == 0
      && flatCombiner'.state.elem_idx == 0
      && num_ops as int == |flatCombiner'.state.elems| == |requestIds|
      && (forall i | 0 <= i < |flatCombiner'.state.elems| ::
          && flatCombiner'.state.elems[i].rid == requestIds[i]
          && i in updates
          && updates[i].rid == flatCombiner'.state.elems[i].rid
          && updates[i].us.UpdateInit?
          && updates[i].us.op == ops'[i]
          && i in opCellPermissions
          && 0 <= flatCombiner'.state.elems[i].tid < MAX_THREADS_PER_REPLICA as int
          && opCellPermissions[i].cell
                  == node.contexts[flatCombiner'.state.elems[i].tid].cell
      )
  {
    ops' := ops;
    flatCombiner' := flatCombiner;
    //requestIds := [];
    num_ops := 0;
    updates := glmap_empty();
    opCellPermissions := glmap_empty();

    var j := 0 as uint64;
    while j < MAX_THREADS_PER_REPLICA
    invariant 0 <= j <= MAX_THREADS_PER_REPLICA
    invariant num_ops <= j
    invariant |ops'| == |ops|
    invariant flatCombiner'.loc == node.fc_loc
    invariant flatCombiner'.state.FCCombinerCollecting?
      && flatCombiner'.state.idx == j as int
      && num_ops as int == |flatCombiner'.state.elems| // == |requestIds|
      && (forall i | 0 <= i < |flatCombiner'.state.elems| ::
          //&& flatCombiner'.state.elems[i].rid //== requestIds[i]
          && i in updates
          && updates[i].rid == flatCombiner'.state.elems[i].rid
          && updates[i].us.UpdateInit?
          && updates[i].us.op == ops'[i]
          && i in opCellPermissions
          && 0 <= flatCombiner'.state.elems[i].tid < MAX_THREADS_PER_REPLICA as int
          && opCellPermissions[i].cell
                  == node.contexts[flatCombiner'.state.elems[i].tid].cell
      )
    {
      glinear var new_contents_opt;
      glinear var new_update_opt;

      atomic_block var has_op := execute_atomic_compare_and_set_strong(
          lseq_peek(node.contexts, j).atomic, 1, 2)
      {
        ghost_acquire ghost_context;
        glinear var ContextGhost(contents, fc, update) := ghost_context;
        flatCombiner', fc := combiner_collect(flatCombiner', fc);
        if has_op { // FCRequest
          new_contents_opt := contents;
          new_update_opt := update;
          ghost_context := ContextGhost(glNone, fc, glNone);
        } else {
          ghost_context := ContextGhost(contents, fc, update);
          new_contents_opt := glNone;
          new_update_opt := glNone;
        }
        ghost_release ghost_context;
      }

      if has_op {
        // get the op, add to ops' buffer
        var opResponse := read_cell(lseq_peek(node.contexts, j).cell, new_contents_opt.value);
        var op := opResponse.op;
        ops' := seq_set(ops', num_ops, op);

        // ghost state update
        updates := glmap_insert(updates, num_ops as int, unwrap_value(new_update_opt));
        opCellPermissions := glmap_insert(opCellPermissions, num_ops as int, unwrap_value(new_contents_opt));

        num_ops := num_ops + 1;
      } else {
        dispose_glnone(new_contents_opt);
        dispose_glnone(new_update_opt);
      }

      j := j + 1;
    }

    flatCombiner' := combiner_goto_responding(flatCombiner');
    requestIds := seq(num_ops as int, (i) requires 0 <= i < num_ops as int =>
        flatCombiner'.state.elems[i].rid);      
  }

  method combine_respond(
      shared node: Node,
      shared responses: seq<nrifc.ReturnType>,
      glinear flatCombiner: FCCombiner,
      ghost requestIds: seq<RequestId>,
      glinear updates: map<nat, Update>,
      glinear opCellPermissions: map<nat, CellContents<OpResponse>>)
  returns (
      glinear flatCombiner': FCCombiner)
  requires node.WF()
  requires |responses| == MAX_THREADS_PER_REPLICA as int
  requires flatCombiner.loc == node.fc_loc
  requires flatCombiner.state.FCCombinerResponding?
      && flatCombiner.state.idx == 0
      && flatCombiner.state.elem_idx == 0
      && |flatCombiner.state.elems| == |requestIds| <= |responses|
      && (forall i | 0 <= i < |flatCombiner.state.elems| ::
          && flatCombiner.state.elems[i].rid == requestIds[i]
          && i in updates
          && updates[i].rid == flatCombiner.state.elems[i].rid
          && updates[i].us.UpdateDone?
          && updates[i].us.ret == responses[i]
          && i in opCellPermissions
          && 0 <= flatCombiner.state.elems[i].tid < MAX_THREADS_PER_REPLICA as int
          && opCellPermissions[i].cell
                  == node.contexts[flatCombiner.state.elems[i].tid].cell
      )
  ensures flatCombiner'.loc == node.fc_loc
  ensures flatCombiner'.state == FCCombinerCollecting(0, [])
  {
    flatCombiner' := flatCombiner;
    glinear var updates' := updates;
    glinear var opCellPermissions' := opCellPermissions;

    var cur_idx: uint64 := 0;
    var j := 0;
    while j < MAX_THREADS_PER_REPLICA
    invariant 0 <= cur_idx <= j <= MAX_THREADS_PER_REPLICA
    invariant flatCombiner'.loc == node.fc_loc
    invariant
      && flatCombiner'.state.FCCombinerResponding?
      && flatCombiner'.state.idx == j as int
      && flatCombiner'.state.elem_idx == cur_idx as int
      && |flatCombiner'.state.elems| == |requestIds| <= |responses|
      && (forall i | cur_idx as int <= i < |flatCombiner'.state.elems| ::
          && flatCombiner'.state.elems[i].rid == requestIds[i]
          && i in updates'
          && updates'[i].rid == flatCombiner'.state.elems[i].rid
          && updates'[i].us.UpdateDone?
          && updates'[i].us.ret == responses[i]
          && i in opCellPermissions'
          && 0 <= flatCombiner'.state.elems[i].tid < MAX_THREADS_PER_REPLICA as int
          && opCellPermissions'[i].cell
                  == node.contexts[flatCombiner'.state.elems[i].tid].cell
      )
    {
      atomic_block var slot_state := execute_atomic_load(
          lseq_peek(node.contexts, j).atomic)
      {
        ghost_acquire ghost_context;
        glinear var ContextGhost(contents, fc, update) := ghost_context;
        if slot_state == 2 {
          flatCombiner', fc :=
            combiner_response_matches(flatCombiner', fc);
        } else {
          flatCombiner', fc := combiner_response_skip(flatCombiner', fc);
        }
        ghost_context := ContextGhost(contents, fc, update);
        ghost_release ghost_context;
      }

      if slot_state == 2 {
        glinear var update, opCellPerm;
        updates', update := glmap_take(updates', cur_idx as int);
        opCellPermissions', opCellPerm := glmap_take(opCellPermissions', cur_idx as int);

        // write the return value

        var opResponse := read_cell(lseq_peek(node.contexts, j).cell, opCellPerm);
        opResponse := opResponse.(ret := seq_get(responses, cur_idx));

        write_cell(lseq_peek(node.contexts, j).cell, inout opCellPerm,
            opResponse);

        atomic_block var slot_state := execute_atomic_store(
            lseq_peek(node.contexts, j).atomic, 0)
        {
          ghost_acquire ghost_context;
          glinear var ContextGhost(old_contents, fc, old_update) := ghost_context;

          flatCombiner', fc := combiner_respond(flatCombiner', fc);

          dispose_glnone(old_contents);
          dispose_glnone(old_update);
          ghost_context := ContextGhost(glSome(opCellPerm), fc, glSome(update));
          //assert ghost_context.inv(0, j as int, lseq_peek(node.contexts, j).cell);
          ghost_release ghost_context;
        }

        cur_idx := cur_idx + 1;
      }

      j := j + 1;
    }

    dispose_anything(updates');
    dispose_anything(opCellPermissions');
    flatCombiner' := combiner_goto_collecting(flatCombiner');
  }

/* use something like this for initializing the `lseq` stuff:

  method init_batch_busy()
  returns (linear batch_busy: lseq<Atomic<bool, NullGhostType>>)
  ensures |batch_busy| == NUM_CHUNKS as int
  ensures (forall i :: 0 <= i < NUM_CHUNKS as int ==> lseq_has(batch_busy)[i])
  ensures (forall i, v, g :: 0 <= i < NUM_CHUNKS as int ==> atomic_inv(batch_busy[i], v, g) <==> true)
  {
    batch_busy := lseq_alloc<Atomic<bool, NullGhostType>>(NUM_CHUNKS_64());
    var i: uint64 := 0;
    while i < NUM_CHUNKS_64()
    invariant 0 <= i as int <= NUM_CHUNKS as int
    invariant |batch_busy| == NUM_CHUNKS as int
    invariant (forall j :: i as int <= j < NUM_CHUNKS as int ==> !lseq_has(batch_busy)[j])
    invariant (forall j :: 0 <= j < i as int ==> lseq_has(batch_busy)[j])
    invariant (forall j, v, g :: 0 <= j < i as int ==> atomic_inv(batch_busy[j], v, g) <==> true)
    {
      linear var ato := new_atomic(false, NullGhostType, (v, g) => true, 0);
      lseq_give_inout(inout batch_busy, i, ato);
      i := i + 1;
    }
  }
*/
//    var i := 0;
//    var j := 0;
//    while i < next-1 {
//      if i in node.context {
//        operations[i] = 1;      
//        buffer[j] = node.context[i];
//        j := j + 1;
//      }
//      else {
//        has_ops[i] = 0;
//      }
//    }



  method do_update(shared nr: NR, shared node: Node, op: nrifc.UpdateOp,
      glinear ticket: Update, linear ctx: ThreadOwnedContext)
  returns (result: nrifc.ReturnType, glinear stub: Update, linear ctx': ThreadOwnedContext)
  requires nr.WF()
  requires node.WF()
  requires ctx.WF(node)
  requires ticket.us == UpdateInit(op)
  ensures stub.us.UpdateDone? 
  ensures stub.rid == ticket.rid
  ensures stub.us.ret == result
  ensures ctx'.WF(node)
  decreases * // method is not guaranteed to terminate
  {
    linear var ThreadOwnedContext(tid, fc_client, cell_contents, client_counter) := ctx;

    var opr := read_cell(lseq_peek(node.contexts, tid).cell, cell_contents);
    opr := opr.(op := op);
    write_cell(lseq_peek(node.contexts, tid).cell, inout cell_contents, opr);

    assert node.contexts[tid as int].WF(tid as int, node.fc_loc);

    atomic_block var _ := execute_atomic_store(lseq_peek(node.contexts, tid).atomic, 1)
    {
      ghost_acquire ctx_g;
      glinear var ContextGhost(contents_none, fc_slot, update_none) := ctx_g;
      fc_client, fc_slot := fc_send(fc_client, fc_slot, ticket.rid);
      dispose_glnone(contents_none);
      dispose_glnone(update_none);
      ctx_g := ContextGhost(glSome(cell_contents), fc_slot, glSome(ticket));
      ghost_release ctx_g;
    }

    assume tid > 0; // TODO
    try_combine(nr, node, tid);

    glinear var cell_contents_opt: glOption<CellContents<OpResponse>> := glNone;
    glinear var stub_opt: glOption<Update> := glNone;

    var done := false;
    while !done
    invariant !done ==>
      && fc_client == FCClient(node.fc_loc, tid as int, FCClientWaiting(ticket.rid))
    invariant done ==>
      && cell_contents_opt.glSome?
      && stub_opt.glSome?
      && cell_contents_opt.value.cell == node.contexts[tid as nat].cell
      && stub_opt.value.us.UpdateDone? 
      && stub_opt.value.rid == ticket.rid
      && stub_opt.value.us.ret == result
      && fc_client == FCClient(node.fc_loc, tid as int, FCClientIdle)
    decreases *
    {
      atomic_block var aval := execute_atomic_load(lseq_peek(node.contexts, tid).atomic)
      {
        ghost_acquire ctx_g;
        if aval == 0 {
          glinear var ContextGhost(cell_contents_opt', fc_slot, stub_opt') := ctx_g;
          dispose_anything(cell_contents_opt);
          dispose_anything(stub_opt);
          cell_contents_opt := cell_contents_opt';
          stub_opt := stub_opt';
          fc_client, fc_slot := fc_recv(fc_client, fc_slot, ticket.rid);
          ctx_g := ContextGhost(glNone, fc_slot, glNone);
        }
        ghost_release ctx_g;
      }

      if aval == 0 {
        opr := read_cell(lseq_peek(node.contexts, tid).cell, cell_contents_opt.value);
        result := opr.ret;
        done := true;
      } else {
        SpinLoopHint();
      }
    }

    cell_contents := unwrap_value(cell_contents_opt);
    stub := unwrap_value(stub_opt);
    ctx' := ThreadOwnedContext(tid, fc_client, cell_contents, client_counter);
  }

  method do_read(shared nr: NR, shared node: Node, op: nrifc.ReadonlyOp, linear ctx: ThreadOwnedContext,
      glinear ticket: Readonly)
  returns (result: nrifc.ReturnType, glinear stub: Readonly, linear ctx': ThreadOwnedContext)
  requires nr.WF()
  requires node.WF()
  requires ctx.WF(node)
  //requires node.ghost_replica.state == nrifc.I(actual_replica)
  // The contract for this method works like this:
  // Input a ticket which "allows" us to perform the readonly operation specified
  // by the input parameter `op`
  requires ticket.rs == ReadonlyInit(op)
  // And we must return a stub that validates that we performed the operation
  // with the result being that value that we are returning.
  ensures stub.rs.ReadonlyDone? 
  ensures stub.rid == ticket.rid
  ensures stub.rs.ret == result
  ensures ctx'.WF(node)
  //ensures ghost_replica'.state == nrifc.I(actual_replica')
  decreases * // method is not guaranteed to terminate
  {
    // https://github.com/vmware/node-replication/blob/1d92cb7c040458287bedda0017b97120fd8675a7/nr/src/replica.rs#L559
    //        let ctail = self.slog.get_ctail();
    //        while !self.slog.is_replica_synced_for_reads(self.idx, ctail) {
    //            self.try_combine(tid);
    //            spin_loop();
    //        }
    //
    //        return self.data.read(tid - 1).dispatch(op);

    // 1. Read ctail
    atomic_block var ctail := execute_atomic_load(nr.ctail.inner) {
      ghost_acquire ctail_token; // declares ctail_token as a 'glinear' object
      assert ctail_token == Ctail(ctail as int); // this follows from the invariant on nr.ctail

      // perform transition of ghost state here ...
      stub := perform_TransitionReadonlyReadCtail(ticket, ctail_token);

      ghost_release ctail_token;
    }

    assert stub.rs.ReadonlyCtail?; // advisory

    // 2. Read localTail (loop until you read a good value)
    var synced := false;
    synced, stub := is_replica_synced_for_reads(nr, node.nodeId, ctail, stub);

    while !synced 
    decreases * 
    invariant synced ==> stub.rs.ReadonlyReadyToRead? 
    invariant !synced ==> stub.rs.ReadonlyCtail?
    invariant !synced ==> stub.rs.ctail <= ctail as nat;
    invariant stub.rid == ticket.rid
    invariant synced ==> stub.rs.nodeId == node.nodeId as nat
    invariant stub.rs.op == op
    {
      try_combine(nr, node, ctx.tid);
      Runtime.SpinLoopHint();
      synced, stub := is_replica_synced_for_reads(nr, node.nodeId, ctail, stub);
    }

    assert stub.rs.ReadonlyReadyToRead?; // advisory
    assert stub.rs.nodeId == node.nodeId as nat;

    linear var ThreadOwnedContext(tid, fc_client, cell_contents, client_counter) := ctx;

    // 3. Take read-lock on replica; apply operation on replica
    linear var linear_guard := node.replica.acquire_shared(tid as uint8, client_counter);
    assert linear_guard.v.ghost_replica.nodeId == stub.rs.nodeId;

    result, stub := apply_readonly(node.replica, linear_guard, op, stub);
    client_counter := node.replica.release_shared(linear_guard);

    ctx' := ThreadOwnedContext(tid, fc_client, cell_contents, client_counter);
    assert stub.rs.ReadonlyDone?; // advisory
  }

  method apply_readonly(shared rwlock: RwLock, shared guard: SharedGuard, op: nrifc.ReadonlyOp,
      glinear ticket: Readonly)
  returns (result: nrifc.ReturnType, glinear ticket': Readonly)
  requires rwlock.InternalInv()
  requires guard.Inv(rwlock)
  requires ticket.rs.ReadonlyReadyToRead?
  requires guard.v.ghost_replica.nodeId == ticket.rs.nodeId
  requires ticket.rs.op == op
  requires guard.v.ghost_replica.state == nrifc.I(guard.v.actual_replica)
  ensures ticket.rid == ticket'.rid
  ensures ticket'.rs.ReadonlyDone?
  ensures ticket'.rs.ret == result
  ensures guard.v.ghost_replica.state == nrifc.I(guard.v.actual_replica)
  {
    shared var shared_v := RwLockImpl.borrow_shared(rwlock, guard);
    assert shared_v.ghost_replica.nodeId == ticket.rs.nodeId;
    result := nrifc.do_readonly(shared_v.actual_replica, op);

    assert nrifc.read(shared_v.ghost_replica.state, ticket.rs.op) == result;

    shared var NodeReplica(actual_replica, ghost_replica, combinerState, cb) := shared_v;
    ticket' := perform_ReadonlyDone(ticket, ghost_replica);
  }

  method append(shared nr: NR, shared node: Node,
      shared ops: seq<nrifc.UpdateOp>,
      num_ops: uint64,
      linear actual_replica: nrifc.DataStructureType,
      linear responses: seq<nrifc.ReturnType>,
      glinear ghost_replica: Replica,
      ghost requestIds: seq<RequestId>,
      glinear updates: map<nat, Update>,
      glinear combinerState: CombinerToken,
      glinear cb: CBCombinerToken)
  returns (
    linear actual_replica': nrifc.DataStructureType,
    linear responses': seq<nrifc.ReturnType>,
    glinear ghost_replica': Replica,
    glinear updates': map<nat, Update>,
    glinear combinerState': CombinerToken,
    glinear cb': CBCombinerToken)
  requires nr.WF()
  requires node.WF()
  requires |ops| == MAX_THREADS_PER_REPLICA as int
  requires |requestIds| == num_ops as int <= MAX_THREADS_PER_REPLICA as int
  requires combinerState.nodeId == node.nodeId as int
  requires combinerState.state == CombinerReady
  requires forall i | 0 <= i < |requestIds| ::
      i in updates && updates[i] == Update(requestIds[i], UpdateInit(ops[i]))
  requires cb.nodeId == node.nodeId as int
  requires cb.rs.CBCombinerIdle?
  requires ghost_replica.state == nrifc.I(actual_replica)
  requires ghost_replica.nodeId == node.nodeId as int
  requires |responses| == MAX_THREADS_PER_REPLICA as int
  requires |requestIds| <= MAX_THREADS_PER_REPLICA as int

  ensures combinerState'.state.CombinerReady?
      || combinerState'.state.CombinerPlaced?
  ensures combinerState'.state.CombinerReady? ==>
      post_exec(node, requestIds, responses', updates', combinerState')
  ensures combinerState'.state.CombinerPlaced? ==>
      pre_exec(node, requestIds, responses', updates', combinerState')
  ensures cb' == cb
  ensures ghost_replica'.state == nrifc.I(actual_replica')
  ensures ghost_replica'.nodeId == node.nodeId as int

  decreases *
  {
    updates' := updates;
    combinerState' := combinerState;
    actual_replica' := actual_replica;
    ghost_replica' := ghost_replica;
    cb' := cb;
    responses' := responses;

    var iteration := 1;
    var waitgc := 1;

    var done := false;
    while !done
    invariant 0 <= iteration as int <= WARN_THRESHOLD as int
    invariant 0 <= waitgc as int <= WARN_THRESHOLD as int
    invariant cb' == cb
    invariant ghost_replica'.state == nrifc.I(actual_replica')
    invariant ghost_replica'.nodeId == node.nodeId as int
    invariant !done ==>
      && combinerState' == combinerState
      && updates' == updates
      && responses' == responses
      && ghost_replica'.state == nrifc.I(actual_replica')
      && ghost_replica'.nodeId == node.nodeId as int

    invariant done ==>
      && (combinerState'.state.CombinerReady?
          || combinerState'.state.CombinerPlaced?)
      && (combinerState'.state.CombinerReady? ==>
          post_exec(node, requestIds, responses', updates', combinerState'))
      && (combinerState'.state.CombinerPlaced? ==>
          pre_exec(node, requestIds, responses', updates', combinerState'))

    decreases *
    {
      if iteration % WARN_THRESHOLD == 0 {
        iteration := 0;
        print "append takes too many iterations to complete\n";
      }
      iteration := iteration + 1;

      atomic_block var tail := execute_atomic_load(nr.globalTail.inner) { }

      glinear var advance_tail_state;
      atomic_block var head := execute_atomic_load(nr.head.inner) {
        ghost_acquire h;
        advance_tail_state := init_advance_tail_state(h);
        ghost_release h;
      }
      if tail > head + (BUFFER_SIZE - GC_FROM_HEAD) {  // TODO: bounded int error
        if waitgc % WARN_THRESHOLD == 0 {
          waitgc := 0;
          print "append takes too many waitgc to complete\n";
        }
        waitgc := waitgc + 1;

        dispose_anything(advance_tail_state);

        actual_replica', responses',
            ghost_replica', updates', combinerState', cb' :=
          exec(nr, node, actual_replica', responses', ghost_replica',
              requestIds, updates', combinerState', cb');
      } else {

        assume tail as int + num_ops as int < 0x1_0000_0000_0000_0000; // TODO
        var advance: bool := (tail + num_ops > head + (BUFFER_SIZE - GC_FROM_HEAD));

        glinear var log_entries;
        glinear var cyclic_buffer_entries;
        glinear var appendStateOpt;

        atomic_block var success := execute_atomic_compare_and_set_weak(
            nr.globalTail.inner, tail, tail + num_ops)
        {
          ghost_acquire globalTailTokens;
          atomic_block var _ := execute_atomic_noop(nr.bufferContents)
          {
            ghost_acquire contents;
            if success {
              glinear var GlobalTailTokens(globalTail, cbGlobalTail) := globalTailTokens;
              glinear var appendState;
              globalTail, updates', combinerState', log_entries :=
                perform_AdvanceTail(globalTail, updates', combinerState', ops[.. num_ops], requestIds, node.nodeId as int);
              cbGlobalTail, cyclic_buffer_entries, appendState := finish_advance_tail(
                  advance_tail_state, cbGlobalTail, tail as int + num_ops as int, contents);
              appendStateOpt := glSome(appendState);
              globalTailTokens := GlobalTailTokens(globalTail, cbGlobalTail);
            } else {
              // no transition
              log_entries := glmap_empty(); // to satisfy linearity checker
              cyclic_buffer_entries := glmap_empty();
              appendStateOpt := glNone;

              dispose_anything(advance_tail_state);
            }
            ghost_release contents;
          }
          ghost_release globalTailTokens;
        }

        if success {
          glinear var append_state := unwrap_value(appendStateOpt);

          ghost var original_cyclic_buffer_entries := cyclic_buffer_entries;
          
          var j := 0;
          while j < num_ops
          invariant 0 <= j <= num_ops
          invariant append_state.cur_idx == tail as int + j as int
          invariant append_state.tail == tail as int + num_ops as int
          invariant forall i: int | j as int <= i < |requestIds| ::
              i in log_entries
                && log_entries[i] == Log(tail as int + i, ops[i], node.nodeId as int)
          invariant forall i: int | j as int <= i < |requestIds| ::
              && (tail as int + i) in cyclic_buffer_entries
              && cyclic_buffer_entries[tail as int + i]
                  == original_cyclic_buffer_entries[tail as int + i]
          {
            // Get the single 'Log' token we're going to store
            glinear var log_entry, cyclic_buffer_entry;
            log_entries, log_entry := glmap_take(log_entries, j as int);
            // Get the access to the 'Cell' in the buffer entry
            cyclic_buffer_entries, cyclic_buffer_entry :=
                glmap_take(cyclic_buffer_entries, tail as int + j as int);

            assert BufferEntryInv(nr.buffer,
                (tail as int + j as int) - BUFFER_SIZE as int, cyclic_buffer_entry);

            glinear var StoredType(cellContents, oldLogEntry) := cyclic_buffer_entry;

            dispose_anything(oldLogEntry); // don't need this anymore

            var bounded_idx := (tail + j) % BUFFER_SIZE;
            calc {
              ((tail as int + j as int) - BUFFER_SIZE as int) % BUFFER_SIZE as int;
              bounded_idx as int;
            }

            assert nr.buffer[bounded_idx as int].WF(bounded_idx as int);

            // Physically write the log entry into the cyclic buffer
            write_cell(lseq_peek(nr.buffer, bounded_idx).cell,
                inout cellContents,
                ConcreteLogEntry(seq_get(ops, j), node.nodeId));
            
            cyclic_buffer_entry := StoredType(cellContents, glSome(log_entry));
            assert BufferEntryInv(nr.buffer,
                (tail as int + j as int), cyclic_buffer_entry);

            var m := ((tail + j) / BUFFER_SIZE) % 2 == 0;
            atomic_block var _ := execute_atomic_store(
                lseq_peek(nr.buffer, bounded_idx).alive, m)
            {
              ghost_acquire aliveToken;
              atomic_block var _ := execute_atomic_noop(nr.bufferContents)
              {
                ghost_acquire contents;
                append_state, aliveToken, contents :=
                  append_flip_bit(append_state, aliveToken, contents, cyclic_buffer_entry);
                ghost_release contents;
              }
              ghost_release aliveToken;
            }

            j := j + 1;
          }

          dispose_anything(log_entries);
          dispose_anything(cyclic_buffer_entries);
          dispose_anything(append_state);

          assert pre_exec(node, requestIds, responses', updates', combinerState');

          if advance {
            actual_replica', responses', ghost_replica',
                updates', combinerState', cb' :=
              advance_head(nr, node, actual_replica', responses', ghost_replica',
                  requestIds, updates', combinerState', cb');

            assert combinerState'.state.CombinerPlaced? ==>
                pre_exec(node, requestIds, responses', updates', combinerState');
          }
          
          done := true;
        } else {
          dispose_anything(log_entries);
          dispose_anything(cyclic_buffer_entries);
          dispose_anything(appendStateOpt);
        }
      }
    }
  }

  predicate pre_exec(node: Node,
      requestIds: seq<RequestId>,
      responses: seq<nrifc.ReturnType>,
      updates: map<nat, Update>,
      combinerState: CombinerToken)
  {
    && combinerState.nodeId == node.nodeId as int
    && combinerState.state == CombinerPlaced(requestIds)
    && |responses| == MAX_THREADS_PER_REPLICA as int
    && |requestIds| <= MAX_THREADS_PER_REPLICA as int
    && (forall i | 0 <= i < |requestIds| ::
      i in updates
        && updates[i].us.UpdatePlaced?
        && updates[i] == Update(requestIds[i],
            UpdatePlaced(node.nodeId as int, updates[i].us.idx))
    )
  }

  predicate post_exec(node: Node,
      requestIds: seq<RequestId>,
      responses': seq<nrifc.ReturnType>,
      updates': map<nat, Update>,
      combinerState': CombinerToken)
  {
    && combinerState'.nodeId == node.nodeId as int
    && combinerState'.state == CombinerReady
    && |responses'| == MAX_THREADS_PER_REPLICA as int
    && |requestIds| <= MAX_THREADS_PER_REPLICA as int
    && (forall i | 0 <= i < |requestIds| as int ::
            i in updates'
              && updates'[i].us.UpdateDone?
              && updates'[i].rid == requestIds[i]
              && updates'[i].us.ret == responses'[i]
    )
  }

  method exec(shared nr: NR, shared node: Node,
      linear actual_replica: nrifc.DataStructureType,
      linear responses: seq<nrifc.ReturnType>,
      glinear ghost_replica: Replica,
      ghost requestIds: seq<RequestId>,
      glinear updates: map<nat, Update>,
      glinear combinerState: CombinerToken,
      glinear cb: CBCombinerToken)
  returns (
    linear actual_replica': nrifc.DataStructureType,
    linear responses': seq<nrifc.ReturnType>,
    glinear ghost_replica': Replica,
    glinear updates': map<nat, Update>,
    glinear combinerState': CombinerToken,
    glinear cb': CBCombinerToken)
  requires nr.WF()
  requires node.WF()
  requires cb.nodeId == node.nodeId as int
  requires cb.rs.CBCombinerIdle?
  requires ghost_replica.state == nrifc.I(actual_replica)
  requires ghost_replica.nodeId == node.nodeId as int
  requires combinerState.state.CombinerReady?
      || combinerState.state.CombinerPlaced?
  requires combinerState.nodeId == node.nodeId as int
  requires |responses| == MAX_THREADS_PER_REPLICA as int
  requires combinerState.state.CombinerPlaced? ==>
      pre_exec(node, requestIds, responses, updates, combinerState)
  ensures combinerState.state.CombinerPlaced? ==>
      post_exec(node, requestIds, responses', updates', combinerState')
  ensures combinerState.state.CombinerReady? ==>
      responses == responses' && combinerState' == combinerState && updates' == updates
  ensures cb' == cb
  ensures ghost_replica'.state == nrifc.I(actual_replica')
  ensures ghost_replica'.nodeId == node.nodeId as int
  decreases *
  {
    actual_replica' := actual_replica;
    ghost_replica' := ghost_replica;
    combinerState' := combinerState;
    updates' := updates;
    cb' := cb;
    responses' := responses;

    assert nr.node_info[node.nodeId as int].WF(node.nodeId as int);

    ghost var requestIds' := requestIds;
    if combinerState'.state.CombinerReady? {
      combinerState' := perform_TrivialStartCombining(combinerState');
      requestIds' := [];
    }

    atomic_block var ltail := execute_atomic_load(lseq_peek(nr.node_info, node.nodeId).localTail)
    {
      ghost_acquire ltail_token;
      combinerState' := perform_ExecLoadLtail(combinerState', ltail_token.localTail);
      cb' := reader_start(cb', ltail_token.cbLocalTail);
      ghost_release ltail_token;
    }

    atomic_block var gtail := execute_atomic_load(nr.globalTail.inner)
    {
      ghost_acquire gtail_token;
      combinerState' := perform_ExecLoadGlobalTail(combinerState', gtail_token.globalTail);
      cb' := reader_enter(cb', gtail_token.cbGlobalTail);
      ghost_release gtail_token;
    }

    if ltail == gtail {
      // done
      assume false; // TODO
    } else {
      var responsesIndex: uint64 := 0;

      ghost var prev_combinerState := combinerState';
      var i := ltail;
      while i < gtail
      invariant 0 <= i <= gtail
      invariant combinerState'.nodeId == prev_combinerState.nodeId
      invariant combinerState'.state.Combiner?
      invariant combinerState'.state.queueIndex == responsesIndex as int
      invariant combinerState'.state == prev_combinerState.state.(localTail := i as int).(queueIndex := responsesIndex as int)
      invariant cb' == CBCombinerToken(node.nodeId as int, CBCombinerReading(CBReaderRange(ltail as int, gtail as int)))
      invariant ghost_replica'.state == nrifc.I(actual_replica')
      invariant ghost_replica'.nodeId == node.nodeId as int
      invariant |responses'| == MAX_THREADS_PER_REPLICA as int
      invariant 0 <= responsesIndex as int <= |requestIds'|
      invariant forall i | responsesIndex as int <= i < |requestIds'| ::
          i in updates'
            && updates'[i].us.UpdatePlaced?
            && updates'[i] == Update(requestIds'[i], UpdatePlaced(node.nodeId as int, updates'[i].us.idx))
      invariant forall i | 0 <= i < responsesIndex as int ::
          i in updates'
            && updates'[i].us.UpdateApplied?
            && updates'[i].us.idx < combinerState'.state.globalTail
            && updates'[i].rid == requestIds'[i]
            && updates'[i].us.ret == responses'[i]
      invariant responsesIndex == 0 ==> responses' == responses && updates' == updates
      {
        var iteration := 1;

        var done := false;
        while !done
        invariant 0 <= iteration as int <= WARN_THRESHOLD as int
        invariant cb' == CBCombinerToken(node.nodeId as int, CBCombinerReading(CBReaderRange(ltail as int, gtail as int)))
        invariant ghost_replica'.state == nrifc.I(actual_replica')
        invariant ghost_replica'.nodeId == node.nodeId as int
        invariant combinerState'.nodeId == prev_combinerState.nodeId
        invariant combinerState'.state.Combiner?
        invariant combinerState'.state.queueIndex == responsesIndex as int
        invariant !done ==> combinerState'.state == prev_combinerState.state.(localTail := i as int).(queueIndex := responsesIndex as int)
        invariant done ==> combinerState'.state == prev_combinerState.state.(localTail := i as int + 1).(queueIndex := responsesIndex as int)
        invariant 0 <= responsesIndex as int <= |requestIds'|
        invariant |responses'| == MAX_THREADS_PER_REPLICA as int
        invariant forall i | responsesIndex as int <= i < |requestIds'| ::
            i in updates'
              && updates'[i].us.UpdatePlaced?
              && updates'[i] == Update(requestIds'[i], UpdatePlaced(node.nodeId as int, updates'[i].us.idx))
        invariant forall i | 0 <= i < responsesIndex as int ::
            i in updates'
              && updates'[i].us.UpdateApplied?
              && updates'[i].us.idx < combinerState'.state.globalTail
              && updates'[i].rid == requestIds'[i]
              && updates'[i].us.ret == responses'[i]
        invariant responsesIndex == 0 ==> responses' == responses && updates' == updates

        decreases *
        {
          var bounded := i % BUFFER_SIZE;
          atomic_block var live_bit := execute_atomic_load(
              lseq_peek(nr.buffer, bounded).alive)
          {
            ghost_acquire alive_bit;
            atomic_block var _ := execute_atomic_noop(nr.bufferContents)
            {
              ghost_acquire contents;
              if live_bit == ((i / BUFFER_SIZE) % 2 == 0) {
                cb' := reader_guard(cb', alive_bit, i as int, contents);
              }
              ghost_release contents;
            }
            ghost_release alive_bit;
          }

          if live_bit == ((i / BUFFER_SIZE) % 2 == 0) {
            // read the log_entry from memory
            var log_entry := read_cell(lseq_peek(nr.buffer, bounded).cell,
                reader_borrow(cb').cellContents);

            var ret;
            actual_replica', ret := nrifc.do_update(actual_replica', log_entry.op);

            if log_entry.node_id == node.nodeId {
              combinerState' := pre_ExecDispatchLocal(
                  combinerState',
                  reader_borrow(cb').logEntry.value);
              assert responsesIndex as int < |requestIds'|;

              glinear var my_update, my_update';
              updates', my_update := glmap_take(updates', responsesIndex as int);
              combinerState', ghost_replica', my_update' :=
                perform_ExecDispatchLocal(combinerState', ghost_replica',
                      my_update,
                      reader_borrow(cb').logEntry.value);
              updates' := glmap_insert(updates', responsesIndex as int, my_update');

              responses' := seq_set(responses', responsesIndex, ret);

              responsesIndex := responsesIndex + 1;
            } else {
              // TODO remote dispatch
              combinerState', ghost_replica' :=
                perform_ExecDispatchRemote(combinerState', ghost_replica',
                      reader_borrow(cb').logEntry.value);
            }

            cb' := reader_unguard(cb');
            done := true;
          } else {
            if iteration % WARN_THRESHOLD == 0 {
              print "exec warn threshold\n";
              iteration := 0;
            }
            iteration := iteration + 1;
          }
        }

        i := i + 1;
      }

      // Use the state machine invariant to learn that the queue is complete
      combinerState' := queueIsFinishedAfterExec(combinerState');
      assert responsesIndex as int == |requestIds'|;

      // fetch & max
      ghost var prev_combinerState1 := combinerState';
      ghost var prev_updates1 := updates';
      var done := false;
      while !done
      invariant !done ==> combinerState' == prev_combinerState1
      invariant !done ==> updates' == prev_updates1
      invariant done ==>
        && combinerState'.nodeId == node.nodeId as int
        && combinerState'.state == CombinerUpdatedCtail(
            prev_combinerState1.state.queued_ops, gtail as int)
      invariant done ==>
        forall i | 0 <= i < responsesIndex as int ::
            i in updates'
              && updates'[i].us.UpdateDone?
              && updates'[i].rid == requestIds'[i]
              && updates'[i].us.ret == responses'[i]
      invariant |requestIds'| == 0 ==> responses' == responses && updates' == updates
      decreases *
      {
        atomic_block var cur_ctail := execute_atomic_load(nr.ctail.inner) { }
        var max_ctail := (if cur_ctail > gtail then cur_ctail else gtail);
        atomic_block done := execute_atomic_compare_and_set_strong(nr.ctail.inner, cur_ctail, max_ctail)
        {
          ghost_acquire ctail_token;
          if done {
            combinerState', ctail_token :=
              perform_UpdateCompletedTail(combinerState', ctail_token);
            if |requestIds'| > 0 {
              updates' := perform_UpdateDoneMultiple(|requestIds'|, updates', ctail_token);
            }
          } else {
            // do nothing
          }
          ghost_release ctail_token;
        }
      }

      atomic_block var _ :=
        execute_atomic_store(lseq_peek(nr.node_info, node.nodeId).localTail, gtail)
      {
        ghost_acquire ltail_tokens;
        glinear var LocalTailTokens(localTail, cbLocalTail) := ltail_tokens;
        combinerState', localTail := perform_GoToCombinerReady(combinerState', localTail);
        cb', cbLocalTail := reader_finish(cb', cbLocalTail);
        ltail_tokens := LocalTailTokens(localTail, cbLocalTail);
        ghost_release ltail_tokens;
      }
    }
  }

  method advance_head(shared nr: NR, shared node: Node,
      linear actual_replica: nrifc.DataStructureType,
      linear responses: seq<nrifc.ReturnType>,
      glinear ghost_replica: Replica,
      ghost requestIds: seq<RequestId>,
      glinear updates: map<nat, Update>,
      glinear combinerState: CombinerToken,
      glinear cb: CBCombinerToken)
  returns (
    linear actual_replica': nrifc.DataStructureType,
    linear responses': seq<nrifc.ReturnType>,
    glinear ghost_replica': Replica,
    glinear updates': map<nat, Update>,
    glinear combinerState': CombinerToken,
    glinear cb': CBCombinerToken)

  requires nr.WF()
  requires node.WF()
  requires cb.nodeId == node.nodeId as int
  requires cb.rs.CBCombinerIdle?
  requires ghost_replica.state == nrifc.I(actual_replica)
  requires ghost_replica.nodeId == node.nodeId as int
  requires combinerState.state.CombinerPlaced?
  requires combinerState.nodeId == node.nodeId as int
  requires |responses| == MAX_THREADS_PER_REPLICA as int
  requires pre_exec(node, requestIds, responses, updates, combinerState)

  ensures cb' == cb
  ensures ghost_replica'.state == nrifc.I(actual_replica')
  ensures ghost_replica'.nodeId == node.nodeId as int
  ensures combinerState'.nodeId == node.nodeId as int
  ensures |responses'| == MAX_THREADS_PER_REPLICA as int

  ensures combinerState'.state.CombinerReady?
      || combinerState'.state.CombinerPlaced?
  ensures combinerState'.state.CombinerReady? ==>
      post_exec(node, requestIds, responses', updates', combinerState')
  ensures combinerState'.state.CombinerPlaced? ==>
    updates' == updates && combinerState' == combinerState && cb' == cb

  decreases *
  {
    actual_replica' := actual_replica;
    ghost_replica' := ghost_replica;
    combinerState' := combinerState;
    updates' := updates;
    cb' := cb;
    responses' := responses;

    // https://github.com/vmware/node-replication/blob/1d92cb7c040458287bedda0017b97120fd8675a7/nr/src/log.rs#L570

    var iteration: uint64 := 1;
    var done := false;
    while !done
    invariant 0 <= iteration as int <= WARN_THRESHOLD as int

    invariant cb' == cb
    invariant ghost_replica'.state == nrifc.I(actual_replica')
    invariant ghost_replica'.nodeId == node.nodeId as int

    invariant combinerState'.nodeId == node.nodeId as int
    invariant combinerState'.state.CombinerReady?
        || combinerState'.state.CombinerPlaced?
    invariant combinerState'.state.CombinerReady? ==>
        post_exec(node, requestIds, responses', updates', combinerState')
    invariant combinerState'.state.CombinerPlaced? ==>
      updates' == updates && combinerState' == combinerState && cb' == cb
            && responses' == responses
    invariant |responses'| == MAX_THREADS_PER_REPLICA as int

    decreases *
    {
      var r := NUM_REPLICAS;
      atomic_block var global_head := execute_atomic_load(nr.head.inner) {
        
      }
      atomic_block var f := execute_atomic_load(nr.globalTail.inner) { }

      glinear var advance_state_token;

      atomic_block var min_local_tail :=
          execute_atomic_load(lseq_peek(nr.node_info, 0).localTail)
      {
        ghost_acquire ltail;
        advance_state_token := init_advance_head_state(ltail.cbLocalTail);
        ghost_release ltail;
      }

      var idx: uint64 := 1;
      while idx < r
      invariant 0 <= idx <= r
      invariant advance_state_token == CBAdvanceHeadState(idx as int, min_local_tail as int)

      invariant cb' == cb
      invariant ghost_replica'.state == nrifc.I(actual_replica')
      invariant ghost_replica'.nodeId == node.nodeId as int

      invariant combinerState'.nodeId == node.nodeId as int
      invariant combinerState'.state.CombinerReady?
          || combinerState'.state.CombinerPlaced?
      invariant combinerState'.state.CombinerReady? ==>
          post_exec(node, requestIds, responses', updates', combinerState')
      invariant combinerState'.state.CombinerPlaced? ==>
        updates' == updates && combinerState' == combinerState && cb' == cb
            && responses' == responses
      invariant |responses'| == MAX_THREADS_PER_REPLICA as int

      {
        atomic_block var cur_local_tail :=
            execute_atomic_load(lseq_peek(nr.node_info, idx).localTail)
        {
          ghost_acquire ltail;
          advance_state_token := step_advance_head_state(ltail.cbLocalTail, advance_state_token);
          ghost_release ltail;
        }
        if cur_local_tail < min_local_tail {
          min_local_tail := cur_local_tail;
        }
        idx := idx + 1;
      }

      if min_local_tail == global_head {
        if iteration == WARN_THRESHOLD {
          print "Spending a long time in `advance_head`, are we starving?";
          iteration := 0;
        }
        iteration := iteration + 1;

        actual_replica', responses',
            ghost_replica', updates', combinerState', cb' :=
          exec(nr, node, actual_replica', responses',
              ghost_replica', requestIds, updates', combinerState', cb');

        dispose_anything(advance_state_token);
      } else {
        atomic_block var _ := execute_atomic_store(nr.head.inner, min_local_tail)
        {
          ghost_acquire head;
          head := finish_advance_head_state(head, advance_state_token);
          ghost_release head;
        }

        if f < min_local_tail + (BUFFER_SIZE - GC_FROM_HEAD) { // TODO bounded int errors
          done := true;
        } else {
          actual_replica', responses',
              ghost_replica', updates', combinerState', cb' :=
            exec(nr, node, actual_replica', responses',
                ghost_replica', requestIds, updates', combinerState', cb');
        }
      }
    }
  }
}

