include "../framework/AsyncSSM.s.dfy"
include "CyclicBufferTokens.i.dfy"

module FlatCombinerTokens(nrifc: NRIfc) {
  import opened RequestIds
  import opened CBT = CyclicBufferTokens(nrifc) // for NUM_REPLICAS constant

  // Allows clients to enqueue requests
  // The combiner reads the requests and returns responses
  // This machinery allows us make sure the requestId of the request & response match

  datatype FCClientState =
    | FCClientIdle
    | FCClientWaiting(rid: RequestId)
  
  datatype FCClient = FCClient(tid: nat, state: FCClientState)

  datatype Elem = Elem(tid: nat, rid: nat)
  datatype FCCombinerState =
    // no 'idle' state - just use Collecting(0, [])
    | FCCombinerCollecting(idx: nat, elems: seq<Elem>)
    | FCCombinerResponding(idx: nat, elems: seq<Elem>, elem_idx: nat)

  datatype FCCombiner = FCCombiner(state: FCCombinerState)

  datatype FCSlotState =
    | FCEmpty
    | FCRequest(rid: RequestId)
    | FCInProgress(rid: RequestId)
    | FCResponse(rid: RequestId)

  datatype FCSlot = FCSlot(tid: nat, state: FCSlotState)

  // Ops for the combiner

  glinear method combiner_collect(glinear comb: FCCombiner, glinear slot: FCSlot)
  returns (glinear comb': FCCombiner, glinear slot': FCSlot)
  requires comb.state.FCCombinerCollecting?
  requires comb.state.idx < NUM_REPLICAS as int
  requires slot.tid == comb.state.idx
  ensures slot.state.FCEmpty? || slot.state.FCRequest?
  ensures slot.state.FCEmpty? ==>
      && comb' == FCCombiner(comb.state.(idx := comb.state.idx + 1))
      && slot' == slot
  ensures slot.state.FCRequest? ==>
      && comb' == FCCombiner(FCCombinerCollecting(comb.state.idx + 1,
            comb.state.elems + [Elem(comb.state.idx, slot.state.rid)]))
      && slot' == slot.(state := FCInProgress(slot.state.rid))
    
  glinear method combiner_goto_responding(glinear comb: FCCombiner)
  returns (glinear comb': FCCombiner)
  requires comb.state.FCCombinerCollecting?
  requires comb.state.idx == NUM_REPLICAS as int
  ensures comb' == FCCombiner(FCCombinerResponding(0, comb.state.elems, 0))

  glinear method combiner_response_matches(glinear comb: FCCombiner, glinear slot: FCSlot)
  returns (glinear comb': FCCombiner, glinear slot': FCSlot)
  requires comb.state.FCCombinerResponding?
  requires comb.state.idx < NUM_REPLICAS as int
  requires slot.tid == comb.state.idx
  requires slot.state.FCInProgress?
  ensures 0 <= comb.state.elem_idx < |comb.state.elems|
  ensures comb.state.elems[comb.state.elem_idx].tid == comb.state.idx
  ensures comb.state.elems[comb.state.elem_idx].rid == slot.state.rid
  ensures comb' == comb && slot' == slot
      
  glinear method combiner_response_skip(glinear comb: FCCombiner, glinear slot: FCSlot)
  returns (glinear comb': FCCombiner, glinear slot': FCSlot)
  requires comb.state.FCCombinerResponding?
  requires comb.state.idx < NUM_REPLICAS as int
  requires slot.tid == comb.state.idx
  requires !slot.state.FCInProgress?
  ensures comb' == FCCombiner(comb.state.(idx := comb.state.idx + 1))
  ensures slot' == slot

  glinear method combiner_respond(glinear comb: FCCombiner, glinear slot: FCSlot)
  returns (glinear comb': FCCombiner, glinear slot': FCSlot)
  requires comb.state.FCCombinerResponding?
  requires comb.state.idx < NUM_REPLICAS as int
  requires slot.tid == comb.state.idx
  requires slot.state.FCInProgress?
  ensures comb' == FCCombiner(comb.state.(idx := comb.state.idx + 1, elem_idx := comb.state.elem_idx + 1))
  ensures slot' == slot.(state := FCInProgress(slot.state.rid))

  glinear method combiner_goto_collecting(glinear comb: FCCombiner)
  returns (glinear comb': FCCombiner)
  requires comb.state.FCCombinerResponding?
  requires comb.state.idx == NUM_REPLICAS as int
  ensures comb' == FCCombiner(FCCombinerCollecting(0, []))
}
