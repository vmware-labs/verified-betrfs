include "../../lib/Lang/NativeTypes.s.dfy"

module CyclicBufferTokens {
  import opened NativeTypes

  // Fixed number of replicas (in reference impl, this is variable)
  const NUM_REPLICAS: uint64 := 4;

  // Use 'CB' prefix to distinguish these from the corresponding state in the InfiniteLog
  // state machine.

  // TODO add 'ghost loc' to these types

  datatype CBHead = CBHead(head: nat)

  datatype CBLocalTail = CBLocalTail(nodeId: nat, tail: nat)

  datatype CBGlobalTail = CBGlobalTail(tail: nat)

  datatype AdvanceHeadState = AdvanceHeadState(idx: nat, min_tail: nat)

  glinear method init_advance_head_state(gshared first_local_tail: CBLocalTail)
  returns (glinear state': AdvanceHeadState)
  requires first_local_tail.nodeId == 0
  ensures state'.idx == 1
  ensures state'.min_tail == first_local_tail.tail

  glinear method step_advance_head_state(
      gshared local_tail: CBLocalTail, glinear state: AdvanceHeadState)
  returns (glinear state': AdvanceHeadState)
  requires local_tail.nodeId == state.idx
  ensures state' == AdvanceHeadState(state.idx + 1,
      if state.min_tail < local_tail.tail then state.min_tail else local_tail.tail)

  glinear method finish_advance_head_state(
      glinear head: CBHead, glinear state: AdvanceHeadState)
  returns (glinear head': CBHead)
  requires state.idx == NUM_REPLICAS as int
  ensures head' == CBHead(state.min_tail)
}
