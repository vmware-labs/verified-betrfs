include "../../lib/Lang/NativeTypes.s.dfy"

module CyclicBufferTokens {
  import opened NativeTypes

  // Fixed number of replicas (in reference impl, this is variable)
  // TODO fill in reasonable constants for these
  const NUM_REPLICAS: uint64 := 4;
  const BUFFER_SIZE: uint64 := 9999;

  // Use 'CB' prefix to distinguish these from the corresponding state in the InfiniteLog
  // state machine.

  // TODO add 'ghost loc' to these types

  datatype CBHead = CBHead(head: nat)

  datatype CBLocalTail = CBLocalTail(nodeId: nat, tail: nat)

  datatype CBGlobalTail = CBGlobalTail(tail: nat)

  datatype AdvanceHeadState = AdvanceHeadState(idx: nat, min_tail: nat)

  datatype AdvanceTailState = AdvanceTailState(observed_head: nat)

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

  glinear method init_advance_tail_state(gshared head: CBHead)
  returns (glinear state': AdvanceTailState)
  ensures state'.observed_head == head.head

  glinear method finish_advance_tail(glinear state: AdvanceTailState, glinear tail: CBGlobalTail,
      ghost new_tail: nat)
  returns (glinear tail': CBGlobalTail)
  requires tail.tail <= new_tail <= state.observed_head + BUFFER_SIZE as int
  ensures tail'.tail == new_tail

}
