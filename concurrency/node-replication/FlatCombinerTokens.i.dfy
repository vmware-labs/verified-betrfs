include "../framework/AsyncSSM.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "Constants.i.dfy"

module FlatCombinerTokens {
  import opened RequestIds
  import opened NativeTypes
  import opened GhostLoc
  import opened Constants

  // Allows clients to enqueue requests
  // The combiner reads the requests and returns responses
  // This machinery allows us make sure the requestId of the request & response match

  datatype FCClientState =
    | FCClientIdle
    | FCClientWaiting(rid: RequestId)
  
  datatype FCClient = FCClient(loc: Loc, tid: nat, state: FCClientState)

  datatype Elem = Elem(tid: nat, rid: nat)
  datatype FCCombinerState =
    // no 'idle' state - just use Collecting(0, [])
    | FCCombinerCollecting(idx: nat, elems: seq<Elem>)
    | FCCombinerResponding(idx: nat, elems: seq<Elem>, elem_idx: nat)

  datatype FCCombiner = FCCombiner(loc: Loc, state: FCCombinerState)

  datatype FCSlotState =
    | FCEmpty
    | FCRequest(rid: RequestId)
    | FCInProgress(rid: RequestId)
    | FCResponse(rid: RequestId)

  datatype FCSlot = FCSlot(loc: Loc, tid: nat, state: FCSlotState)

  // Ops for the combiner

  glinear method fc_initialize()
  returns (
    glinear clients: map<nat, FCClient>,
    glinear slots: map<nat, FCSlot>,
    glinear combiner: FCCombiner
  )
  ensures combiner.state == FCCombinerCollecting(0, [])
  ensures forall i | 0 <= i < MAX_THREADS_PER_REPLICA as int ::
      i in slots && slots[i] == FCSlot(combiner.loc, i, FCEmpty)
  ensures forall i | 0 <= i < MAX_THREADS_PER_REPLICA as int ::
      i in clients && clients[i] == FCClient(combiner.loc, i, FCClientIdle)

  glinear method combiner_collect(glinear comb: FCCombiner, glinear slot: FCSlot)
  returns (glinear comb': FCCombiner, glinear slot': FCSlot)
  requires comb.state.FCCombinerCollecting?
  requires comb.state.idx < MAX_THREADS_PER_REPLICA as int
  requires slot.tid == comb.state.idx
  requires comb.loc == slot.loc
  ensures slot.state.FCEmpty? || slot.state.FCRequest?
  ensures slot.state.FCEmpty? ==>
      && comb' == FCCombiner(comb.loc, comb.state.(idx := comb.state.idx + 1))
      && slot' == slot
  ensures slot.state.FCRequest? ==>
      && comb' == FCCombiner(comb.loc, FCCombinerCollecting(comb.state.idx + 1,
            comb.state.elems + [Elem(comb.state.idx, slot.state.rid)]))
      && slot' == slot.(state := FCInProgress(slot.state.rid))
    
  glinear method combiner_goto_responding(glinear comb: FCCombiner)
  returns (glinear comb': FCCombiner)
  requires comb.state.FCCombinerCollecting?
  requires comb.state.idx == MAX_THREADS_PER_REPLICA as int
  ensures comb' == FCCombiner(comb.loc, FCCombinerResponding(0, comb.state.elems, 0))

  glinear method combiner_response_matches(glinear comb: FCCombiner, glinear slot: FCSlot)
  returns (glinear comb': FCCombiner, glinear slot': FCSlot)
  requires comb.state.FCCombinerResponding?
  requires comb.state.idx < MAX_THREADS_PER_REPLICA as int
  requires slot.tid == comb.state.idx
  requires slot.state.FCInProgress?
  requires comb.loc == slot.loc
  ensures 0 <= comb.state.elem_idx < |comb.state.elems|
  ensures comb.state.elems[comb.state.elem_idx].tid == comb.state.idx
  ensures comb' == comb && slot' == slot
      
  glinear method combiner_response_skip(glinear comb: FCCombiner, glinear slot: FCSlot)
  returns (glinear comb': FCCombiner, glinear slot': FCSlot)
  requires comb.state.FCCombinerResponding?
  requires comb.state.idx < MAX_THREADS_PER_REPLICA as int
  requires slot.tid == comb.state.idx
  requires !slot.state.FCInProgress?
  requires comb.loc == slot.loc
  ensures comb' == FCCombiner(comb.loc, comb.state.(idx := comb.state.idx + 1))
  ensures slot' == slot

  glinear method combiner_respond(glinear comb: FCCombiner, glinear slot: FCSlot)
  returns (glinear comb': FCCombiner, glinear slot': FCSlot)
  requires comb.state.FCCombinerResponding?
  requires comb.state.idx < MAX_THREADS_PER_REPLICA as int
  requires slot.tid == comb.state.idx
  requires 0 <= comb.state.elem_idx < |comb.state.elems|
  requires comb.state.elems[comb.state.elem_idx].tid == comb.state.idx
  requires comb.loc == slot.loc
  ensures slot.state.FCInProgress?
  ensures comb' == FCCombiner(comb.loc, comb.state.(idx := comb.state.idx + 1, elem_idx := comb.state.elem_idx + 1))
  ensures slot' == slot.(state := FCResponse(slot.state.rid))
  ensures comb.state.elems[comb.state.elem_idx].rid == slot.state.rid

  glinear method combiner_goto_collecting(glinear comb: FCCombiner)
  returns (glinear comb': FCCombiner)
  requires comb.state.FCCombinerResponding?
  requires comb.state.idx == MAX_THREADS_PER_REPLICA as int
  ensures comb' == FCCombiner(comb.loc, FCCombinerCollecting(0, []))

  // Ops for the requester

  glinear method fc_send(glinear fc_client: FCClient, glinear fc_slot: FCSlot, ghost rid: RequestId)
  returns (glinear fc_client': FCClient, glinear fc_slot': FCSlot)
  requires fc_client.loc == fc_slot.loc
  requires fc_client.tid == fc_slot.tid
  requires fc_client.state.FCClientIdle?
  ensures fc_slot.state.FCEmpty?
  ensures fc_client' == fc_client.(state := FCClientWaiting(rid))
  ensures fc_slot' == fc_slot.(state := FCRequest(rid))

  glinear method fc_recv(glinear fc_client: FCClient, glinear fc_slot: FCSlot, ghost rid: RequestId)
  returns (glinear fc_client': FCClient, glinear fc_slot': FCSlot)
  requires fc_client.loc == fc_slot.loc
  requires fc_client.tid == fc_slot.tid
  requires fc_client.state.FCClientWaiting?
  requires !fc_slot.state.FCRequest?
  requires !fc_slot.state.FCInProgress?
  ensures fc_slot.state.FCResponse?
  ensures fc_slot.state.rid == fc_client.state.rid
  ensures fc_client' == fc_client.(state := FCClientIdle)
  ensures fc_slot' == fc_slot.(state := FCEmpty)

}
