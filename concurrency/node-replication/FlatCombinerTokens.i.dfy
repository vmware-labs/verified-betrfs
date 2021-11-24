include "../framework/AsyncSSM.s.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Base/Option.s.dfy"
include "Constants.i.dfy"

module FlatCombinerTokens {
  import opened RequestIds
  import opened NativeTypes
  import opened GhostLoc
  import opened Constants
  import opened Options

  // Allows clients to enqueue requests
  // The combiner reads the requests and returns responses
  // This machinery allows us make sure the requestId of the request & response match

  datatype FCClientState =
    | FCClientIdle
    | FCClientWaiting(ghost rid: RequestId)
  
  datatype FCClient = FCClient(ghost loc: Loc, ghost tid: nat, ghost state: FCClientState)

  datatype Elem = Elem(ghost rid: nat)
  datatype FCCombinerState =
    // no 'idle' state - just use Collecting(0, [])
    | FCCombinerCollecting(ghost elems: seq<Option<Elem>>)
    | FCCombinerResponding(ghost elems: seq<Option<Elem>>, ghost idx: nat)

  datatype FCCombiner = FCCombiner(ghost loc: Loc, ghost state: FCCombinerState)

  datatype FCSlotState =
    | FCEmpty
    | FCRequest(ghost rid: RequestId)
    | FCInProgress(ghost rid: RequestId)
    | FCResponse(ghost rid: RequestId)

  datatype FCSlot = FCSlot(ghost loc: Loc, ghost tid: nat, ghost state: FCSlotState)

  // Ops for the combiner

  glinear method fc_initialize()
  returns (
    glinear clients: map<nat, FCClient>,
    glinear slots: map<nat, FCSlot>,
    glinear combiner: FCCombiner
  )
  ensures combiner.state == FCCombinerCollecting([])
  ensures forall i | 0 <= i < MAX_THREADS_PER_REPLICA as int ::
      i in slots && slots[i] == FCSlot(combiner.loc, i, FCEmpty)
  ensures forall i | 0 <= i < MAX_THREADS_PER_REPLICA as int ::
      i in clients && clients[i] == FCClient(combiner.loc, i, FCClientIdle)

  glinear method combiner_collect(glinear comb: FCCombiner, glinear slot: FCSlot)
  returns (glinear comb': FCCombiner, glinear slot': FCSlot)
  requires comb.state.FCCombinerCollecting?
  requires |comb.state.elems| < MAX_THREADS_PER_REPLICA as int
  requires slot.tid == |comb.state.elems|
  requires comb.loc == slot.loc
  ensures slot.state.FCEmpty? || slot.state.FCRequest?
  ensures slot.state.FCEmpty? ==>
      && comb' == FCCombiner(comb.loc,
          FCCombinerCollecting(comb.state.elems + [None]))
      && slot' == slot
  ensures slot.state.FCRequest? ==>
      && comb' == FCCombiner(comb.loc,
          FCCombinerCollecting(
            comb.state.elems + [Some(Elem(slot.state.rid))]))
      && slot' == slot.(state := FCInProgress(slot.state.rid))
    
  glinear method combiner_goto_responding(glinear comb: FCCombiner)
  returns (glinear comb': FCCombiner)
  requires comb.state.FCCombinerCollecting?
  requires |comb.state.elems| == MAX_THREADS_PER_REPLICA as int
  ensures comb' == FCCombiner(comb.loc, FCCombinerResponding(comb.state.elems, 0))

  glinear method combiner_response_skip(glinear comb: FCCombiner)
  returns (glinear comb': FCCombiner)
  requires comb.state.FCCombinerResponding?
  requires comb.state.idx < |comb.state.elems|
  requires comb.state.elems[comb.state.idx].None?
  ensures comb' == FCCombiner(comb.loc, comb.state.(idx := comb.state.idx + 1))

  glinear method combiner_respond(glinear comb: FCCombiner, glinear slot: FCSlot)
  returns (glinear comb': FCCombiner, glinear slot': FCSlot)
  requires comb.state.FCCombinerResponding?
  requires comb.state.idx < |comb.state.elems|
  requires comb.state.elems[comb.state.idx].Some?
  requires slot.tid == comb.state.idx
  requires comb.loc == slot.loc
  ensures slot.state.FCInProgress?
  ensures comb' == FCCombiner(comb.loc, comb.state.(idx := comb.state.idx + 1))
  ensures slot' == slot.(state := FCResponse(slot.state.rid))
  ensures comb.state.elems[comb.state.idx].value.rid == slot.state.rid

  glinear method combiner_goto_collecting(glinear comb: FCCombiner)
  returns (glinear comb': FCCombiner)
  requires comb.state.FCCombinerResponding?
  requires comb.state.idx == MAX_THREADS_PER_REPLICA as int
  ensures comb' == FCCombiner(comb.loc, FCCombinerCollecting([]))

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

  //// Utilties for the impl

  predicate RidsMatch(bools: seq<Option<Elem>>, rids: seq<RequestId>,
      bools_start: nat,
      bools_end: nat,
      rids_start: nat,
      rids_end: nat)
  requires 0 <= bools_start <= bools_end <= |bools|
  requires 0 <= rids_start <= rids_end <= |rids|
  decreases bools_end
  {
    if bools_end == bools_start then (
      rids_end == rids_start
    ) else (
      if bools[bools_end - 1].Some? then (
        && rids_end > rids_start
        && rids[rids_end - 1] == bools[bools_end - 1].value.rid
        && RidsMatch(bools, rids, bools_start, bools_end - 1, rids_start, rids_end - 1)
      ) else (
        RidsMatch(bools, rids, bools_start, bools_end - 1, rids_start, rids_end)
      )
    )
  }

  lemma {:induction true} RidsMatchAddNone(bools: seq<Option<Elem>>, rids: seq<RequestId>,
      bools_start: nat,
      bools_end: nat,
      rids_start: nat,
      rids_end: nat)
  requires 0 <= bools_start <= bools_end <= |bools|
  requires 0 <= rids_start <= rids_end <= |rids|
  requires RidsMatch(bools, rids, bools_start, bools_end, rids_start, rids_end)
  ensures RidsMatch(bools+[None], rids, bools_start, bools_end, rids_start, rids_end)
  {
  }

  lemma {:induction true} RidsMatchAddRidElem(bools: seq<Option<Elem>>, rids: seq<RequestId>,
      bools_start: nat,
      bools_end: nat,
      rids_start: nat,
      rids_end: nat,
      rid: RequestId)
  requires 0 <= bools_start <= bools_end <= |bools|
  requires 0 <= rids_start <= rids_end <= |rids|
  requires RidsMatch(bools, rids, bools_start, bools_end, rids_start, rids_end)
  ensures RidsMatch(bools+[Some(Elem(rid))], rids+[rid], bools_start, bools_end, rids_start, rids_end)
  {
  }

  lemma RidsMatchPop(bools: seq<Option<Elem>>, rids: seq<RequestId>,
      bools_start: nat,
      bools_end: nat,
      rids_start: nat,
      rids_end: nat)
  requires 0 <= bools_start < bools_end <= |bools|
  requires 0 <= rids_start <= rids_end <= |rids|
  requires RidsMatch(bools, rids, bools_start, bools_end, rids_start, rids_end)
  ensures bools[bools_start].Some? ==>
      && rids_start < rids_end
      && rids[rids_start] == bools[bools_start].value.rid
      && RidsMatch(bools, rids, bools_start + 1, bools_end, rids_start + 1, rids_end)
  ensures bools[bools_start].None? ==>
      && RidsMatch(bools, rids, bools_start + 1, bools_end, rids_start, rids_end)
  {
    if bools_end == bools_start {
    } else {
      if bools[bools_end - 1].Some? {
        if bools_end - 1 > bools_start {
          RidsMatchPop(bools, rids, bools_start, bools_end - 1, rids_start, rids_end - 1);
        }
      } else {
        if bools_end - 1 > bools_start {
          RidsMatchPop(bools, rids, bools_start, bools_end - 1, rids_start, rids_end);
        }
      }
    }
  }
}
