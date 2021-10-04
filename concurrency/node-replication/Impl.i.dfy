include "InfiniteLogTokens.i.dfy"
include "../../lib/Lang/LinearSequence.i.dfy"
include "rwlock/Impl.i.dfy"
include "../framework/Atomic.s.dfy"
include "Runtime.s.dfy"

module Impl(nrifc: NRIfc) {
  import opened Atomics
  import opened ILT = InfiniteLogTokens(nrifc)
  import opened IL = InfiniteLogSSM(nrifc)
  import opened LinearSequence_i
  import opened LinearSequence_s
  import opened NativeTypes
  import opened RwLockImpl
  import opened Runtime

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

  linear datatype NodeInfo = NodeInfo(
    linear localTail: Atomic<uint64, LocalTail>
  )
  {
    predicate WF(nodeId: NodeId) {
      && (forall v, g :: atomic_inv(localTail, v, g) <==> g == LocalTail(nodeId, v as int))
    }
  }
  
  linear datatype NR = NR(
    linear ctail: Atomic<uint64, Ctail>,
    linear node_info: lseq<NodeInfo>
  )
  {
    predicate WF() {
      && (forall v, g :: atomic_inv(ctail, v, g) <==> g == Ctail(v as int))
      && (forall nodeId | 0 <= nodeId < |node_info| :: node_info[nodeId].WF(nodeId))
    }
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
    // 1. Read ctail
    atomic_block var ctail := execute_atomic_load(nr.ctail) {
      ghost_acquire ctail_token; // declares ctail_token as a 'glinear' object
      assert ctail_token == Ctail(ctail as int); // this follows from the invariant on nr.ctail

      // perform transition of ghost state here ...
      stub := perform_TransitionReadonlyReadCtail(ticket, ctail_token);

      ghost_release ctail_token;
    }

    // 2. Read localTail (loop until you read a good value)

    // 3. Take read-lock on replica; apply operation on replica
  }
}
