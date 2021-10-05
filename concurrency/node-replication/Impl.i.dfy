include "InfiniteLogTokens.i.dfy"
include "NRSpec.s.dfy"
include "../../lib/Lang/LinearSequence.i.dfy"
include "rwlock/Impl.i.dfy"
include "../framework/Atomic.s.dfy"
include "../framework/ThreadUtils.s.dfy"
include "../framework/Ptrs.s.dfy"
include "Runtime.s.dfy"
include "CyclicBufferTokens.i.dfy"

module Impl(nrifc: NRIfc) {
  import opened Atomics
  import opened ILT = InfiniteLogTokens(nrifc)
  import opened IL = InfiniteLogSSM(nrifc)
  import opened CyclicBufferTokens
  import opened LinearSequence_i
  import opened LinearSequence_s
  import opened NativeTypes
  import opened RwLockImpl
  import opened Runtime
  import opened ThreadUtils
  import opened Ptrs

  // TODO fill in reasonable constants for these
  const BUFFER_SIZE: uint64 := 4096;
  const GC_FROM_HEAD: uint64 := 19;
  const WARN_THRESHOLD: uint64 := 1283748;

  /*
   * Anything which is allocated on a NUMA node
   */

  linear datatype NodeReplica = NodeReplica(
    linear actual_replica: nrifc.DataStructureType,
    glinear ghost_replica: Replica
  )
  {
    predicate WF(nodeId: NodeId) {
      && ghost_replica.state == nrifc.I(actual_replica)
      && ghost_replica.nodeId == nodeId
    }
  }

  linear datatype Node = Node(
    linear combiner: Atomic<uint64, ()>,
    linear replica: RwLock<NodeReplica>,
    nodeId: uint64
  )
  {
    predicate WF() {
      && (forall nodeReplica :: replica.inv(nodeReplica) <==> nodeReplica.WF(nodeId as int))
    }
  }

  /*
   * Central cyclic buffer stuff
   */

  glinear datatype LocalTailTokens = LocalTailTokens(
      glinear localTail: LocalTail,
      glinear cbLocalTail: CBLocalTail)

  linear datatype NodeInfo = NodeInfo(
    linear localTail: Atomic<uint64, LocalTailTokens>
  )
  {
    predicate WF(nodeId: NodeId) {
      && (forall v, g :: atomic_inv(localTail, v, g) <==>
          g == LocalTailTokens(LocalTail(nodeId, v as int), CBLocalTail(nodeId, v as int)))
    }
  }

  linear datatype NR = NR(
    linear ctail: Atomic<uint64, Ctail>,
    linear head: Atomic<uint64, CBHead>,
    linear globalTail: Atomic<uint64, CBGlobalTail>, // TODO Add the InfiniteLog's GlobalTail token
    linear node_info: lseq<NodeInfo>
  )
  {
    predicate WF() {
      && (forall v, g :: atomic_inv(ctail, v, g) <==> g == Ctail(v as int))
      && (forall v, g :: atomic_inv(head, v, g) <==> g == CBHead(v as int))
      && (forall v, g :: atomic_inv(globalTail, v, g) <==> g == CBGlobalTail(v as int))
      && |node_info| == NUM_REPLICAS as int
      && (forall nodeId | 0 <= nodeId < |node_info| :: nodeId in node_info)
      && (forall nodeId | 0 <= nodeId < |node_info| :: node_info[nodeId].WF(nodeId))
    }
  }


  method is_replica_synced_for_reads(shared nr: NR, nodeId: uint64, ctail: uint64) 
  returns (is_synced: bool) 
  requires nr.WF()
  requires nodeId < NUM_REPLICAS
  {
    // https://github.com/vmware/node-replication/blob/1d92cb7c040458287bedda0017b97120fd8675a7/nr/src/log.rs#L708

    // TODO(unclear): what's so bad about `nr.node_info[nodeId as
    // nat].localTail`
    atomic_block var local_tail := execute_atomic_load(lseq_peek(nr.node_info, nodeId).localTail) { 
      // TODO(unclear): when we need to so stuff in the `atomic_block` and when
      // we don't
    }

    is_synced := local_tail >= ctail;
  }

  method try_combine(shared nr: NR, shared node: Node, tid: uint64)
  requires tid > 0
  requires nr.WF()
  {
    // TODO: Are we CombinerReady? I think so..

    var i: uint64 := 0;
    while i < 5
    invariant 0 <= i <= 5
    {
      atomic_block var combiner := execute_atomic_load(node.combiner) {}
      if combiner != 0 {
        return;
      }
    }

    atomic_block var acquired := execute_atomic_compare_and_set_weak(node.combiner, 0, tid) {}
    if !acquired {
      return;
    }
    combine(nr, node, tid);
    atomic_block var _ := execute_atomic_store(node.combiner, 0) {}
  }

  method combine(shared nr: NR, shared node: Node, tid: uint64)
  requires tid > 0
  requires nr.WF() 
  {

  }

  method do_read(shared nr: NR, shared node: Node, op: nrifc.ReadonlyOp,
      glinear ticket: Readonly)
  returns (result: nrifc.ReturnType, glinear stub: Readonly)
  requires nr.WF()
  requires node.WF()
  // The contract for this method works like this:
  // Input a ticket which "allows" us to perform the readonly operation specified
  // by the input parameter `op`
  requires ticket.rs == ReadonlyInit(op)
  // And we must return a stub that validates that we performed the operation
  // with the result being that value that we are returning.
  ensures stub.rid == ticket.rid && stub.rs.ReadonlyDone? && stub.rs.ret == result
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
    atomic_block var ctail := execute_atomic_load(nr.ctail) {
      ghost_acquire ctail_token; // declares ctail_token as a 'glinear' object
      assert ctail_token == Ctail(ctail as int); // this follows from the invariant on nr.ctail

      // perform transition of ghost state here ...
      stub := perform_TransitionReadonlyReadCtail(ticket, ctail_token);

      ghost_release ctail_token;
    }

    // 2. Read localTail (loop until you read a good value)
    var tid := 1; // TODO: tid comes from client calling do_read
    var synced := is_replica_synced_for_reads(nr, node.nodeId, ctail);
    while !synced {
      try_combine(nr, node, tid);
      Runtime.SpinLoopHint();
      synced := is_replica_synced_for_reads(nr, node.nodeId, ctail);
    }

    // 3. Take read-lock on replica; apply operation on replica
    linear var linear_guard := node.replica.acquire_shared();
    result := apply_readonly(linear_guard, op);
    node.replica.release_shared(linear_guard);
  }

  method apply_readonly(shared guard: SharedGuard<NodeReplica>, op: nrifc.ReadonlyOp) 
  returns (result: nrifc.ReturnType)
  {
    shared var shared_v := RwLockImpl.borrow_shared(guard);
    result := nrifc.do_readonly(shared_v.actual_replica, op);
  }

  method advance_head(shared nr: NR, shared node: Node, op: nrifc.ReadonlyOp)
  requires nr.WF()
  requires node.WF()
  decreases *
  {
    // https://github.com/vmware/node-replication/blob/1d92cb7c040458287bedda0017b97120fd8675a7/nr/src/log.rs#L570

    var iteration: uint64 := 1;
    var done := false;
    while !done
    invariant 0 <= iteration as int <= WARN_THRESHOLD as int
    decreases *
    {
      var r := NUM_REPLICAS;
      atomic_block var global_head := execute_atomic_load(nr.head) {
        
      }
      atomic_block var f := execute_atomic_load(nr.globalTail) { }

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
      invariant advance_state_token == AdvanceHeadState(idx as int, min_local_tail as int)
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

        // TODO call `exec`

        thread_yield();

        dispose_anything(advance_state_token);
      } else {
        atomic_block var _ := execute_atomic_store(nr.head, min_local_tail)
        {
          ghost_acquire head;
          head := finish_advance_head_state(head, advance_state_token);
          ghost_release head;
        }

        if f < min_local_tail + BUFFER_SIZE - GC_FROM_HEAD { // TODO bounded int errors
          done := true;
        } else {
          // TODO call `exec`
        }
      }
    }
  }
}
