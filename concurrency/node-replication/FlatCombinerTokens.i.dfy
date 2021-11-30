include "../framework/AsyncSSM.i.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "../../lib/Base/Option.s.dfy"
include "Constants.i.dfy"
include "FlatCombiner.i.dfy"
include "../framework/Rw.i.dfy"
include "../framework/GlinearMap.s.dfy"
include "../framework/Ptrs.s.dfy"

module FlatCombinerTokens {
  import opened RequestIds
  import opened NativeTypes
  import opened GhostLoc
  import opened Constants
  import opened Options
  import FC = FlatCombiner
  import FCTokens = RwTokens(FC)
  import GlinearMap
  import Ptrs

  // Allows clients to enqueue requests
  // The combiner reads the requests and returns responses
  // This machinery allows us make sure the requestId of the request & response match

  datatype {:glinear_fold} FCClient = FCClient(ghost loc_s: nat, ghost tid: nat, ghost state: FC.FCClientState)
  {
    function defn(): FCTokens.Token {
      FCTokens.T.Token(
          ExtLoc(loc_s, FCTokens.Wrap.singleton_loc()),
          FC.M(map[tid := state], map[], None))
    }
  }

  datatype {:glinear_fold}  FCCombiner = FCCombiner(ghost loc_s: nat, ghost state: FC.FCCombinerState)
  {
    function defn(): FCTokens.Token {
      FCTokens.T.Token(
          ExtLoc(loc_s, FCTokens.Wrap.singleton_loc()),
          FC.M(map[], map[], Some(state)))
    }
  }

  datatype {:glinear_fold} FCSlot = FCSlot(ghost loc_s: nat, ghost tid: nat, ghost state: FC.FCSlotState)
  {
    function defn(): FCTokens.Token {
      FCTokens.T.Token(
          ExtLoc(loc_s, FCTokens.Wrap.singleton_loc()),
          FC.M(map[], map[tid := state], None))
    }
  }



  // Ops for the combiner

  // glinear method do_init_slots(glinear t: FCTokens.Token)
  // returns (glinear slots: map<nat, FCSlot>)
  // {
  //   glinear var t' := t;
  //   ghost var j := 0;
  //   slots := GlinearMap.glmap_empty();

  //   while j < MAX_THREADS_PER_REPLICA as nat
  //   invariant 0 <= j <= LOG_SIZE as nat
  //   invariant t'.loc_s == t.loc_s
  //   invariant t'.val.M?
  //   invariant forall i | 0 <= i < j :: i in slots && slots[i] == FCSlot(t.loc_s, j, FC.FCEmpty)
  //   invariant forall i | j <= i <  MAX_THREADS_PER_REPLICA as nat :: t.val.slots[i] == t'.val.slots[i]
  //   {
  //     var expected := FCSlot(t.loc_s, j, FC.FCEmpty);
  //     var x := expected.defn().val;
  //     var y := t'.val.(slots := t'.val.slots - {j});

  //     glinear var xl;
  //     t', xl := FCTokens.T.split(t', y, x);

  //     glinear var z := FCSlot_fold(expected, xl);
  //     slots := GlinearMap.glmap_insert(slots, j, z);
  //     j := j + 1;
  //   }
  //   Ptrs.dispose_anything(t');
  // }

  // glinear method do_init_clients(glinear t: FCTokens.Token)
  // returns (glinear clients: map<nat, FCClient>)
  // {
  //   glinear var t' := t;
  //   ghost var j := 0;
  //   clients := GlinearMap.glmap_empty();

  //   while j < MAX_THREADS_PER_REPLICA as nat
  //   invariant 0 <= j <= LOG_SIZE as nat
  //   invariant t'.loc_s == t.loc_s
  //   invariant t'.val.M?
  //   invariant forall i | 0<= i < j :: i in clients && clients[i] == FCClient(t.loc_s, i, FC.FCClientIdle)
  //   invariant forall i | j <= i <  MAX_THREADS_PER_REPLICA as nat :: t.val.clients[i] == t'.val.clients[i]
  //   {
  //     var expected := FCClient(t.loc_s, j, FC.FCClientIdle);
  //     var x := expected.defn().val;
  //     var y := t'.val.(clients := t'.val.clients - {j});

  //     glinear var xl;
  //     t', xl := FCTokens.T.split(t', y, x);

  //     glinear var z := FCClient_fold(expected, xl);
  //     clients := GlinearMap.glmap_insert(clients, j, z);
  //     j := j + 1;
  //   }

  //   Ptrs.dispose_anything(t');
  // }

  glinear method fc_initialize()
  returns (
    glinear clients: map<nat, FCClient>,
    glinear slots: map<nat, FCSlot>,
    glinear combiner: FCCombiner
  )
  ensures combiner.state == FC.FCCombinerCollecting([])
  ensures forall i | 0 <= i < MAX_THREADS_PER_REPLICA as int ::
      i in slots && slots[i] == FCSlot(combiner.loc_s, i, FC.FCEmpty)
  ensures forall i | 0 <= i < MAX_THREADS_PER_REPLICA as int ::
      i in clients && clients[i] == FCClient(combiner.loc_s, i, FC.FCClientIdle)
  // {

  //   ghost var new_clients := map x : nat | 0 <= x < (MAX_THREADS_PER_REPLICA as nat) :: x := FC.FCClientIdle;
  //   ghost var new_slots   := map x : nat | 0 <= x < (MAX_THREADS_PER_REPLICA as nat) :: x := FC.FCEmpty;
  //   ghost var new_comb := FC.FCCombinerCollecting([]);
  //   ghost var m := FC.M(new_clients, new_slots, Some(new_comb));

  //   FC.InitImpliesInv(m);
  //   glinear var token := FCTokens.initialize_nonempty(0, m);

  //   ghost var cl := FC.M(new_clients, map[], None);
  //   ghost var s  := FC.M(map[], new_slots, None);
  //   ghost var co := FC.M(map[], map[], Some(new_comb));

  //   glinear var tcl, ts, tco := FCTokens.split3(token, cl, s, co);

  //   clients := do_init_clients(tcl);
  //   slots := do_init_slots(ts);
  //   combiner := FCCombiner_fold(FCCombiner(token.loc_s, new_comb), tco);
  // }

  /* ----------------------------------------------------------------------------------------- */



  glinear method combiner_collect(glinear comb: FCCombiner, glinear slot: FCSlot)
  returns (glinear comb': FCCombiner, glinear slot': FCSlot)
  requires comb.state.FCCombinerCollecting?
  requires |comb.state.elems| < MAX_THREADS_PER_REPLICA as int
  requires slot.tid == |comb.state.elems|
  requires comb.loc_s == slot.loc_s
  ensures slot.state.FCEmpty? || slot.state.FCRequest?
  ensures slot.state.FCEmpty? ==>
      && comb' == FCCombiner(comb.loc_s,
          FC.FCCombinerCollecting(comb.state.elems + [None]))
      && slot' == slot
  ensures slot.state.FCRequest? ==>
      && comb' == FCCombiner(comb.loc_s,
          FC.FCCombinerCollecting(
            comb.state.elems + [Some(FC.Elem(slot.state.rid))]))
      && slot' == slot.(state := FC.FCInProgress(slot.state.rid))
  {
    glinear var c_token := FCCombiner_unfold(comb);
    glinear var s_token := FCSlot_unfold(slot);

    if slot.state.FCEmpty? {

      ghost var out_expect_c := FCCombiner(comb.loc_s, FC.FCCombinerCollecting(comb.state.elems + [None]));
      ghost var out_token_expect_c := FCCombiner_unfold(out_expect_c);

      ghost var out_expect_s := FCSlot(slot.loc_s, slot.tid, FC.FCEmpty);
      ghost var out_token_expect_s := FCSlot_unfold(out_expect_s);

      FC.CombinerDoCollectEmpty_is_transition(
        FC.dot(c_token.val, s_token.val),
        FC.dot(out_token_expect_c.val, s_token.val)
      );

      glinear var out_token_c, out_token_s := FCTokens.internal_transition_2_2(
        c_token, s_token, out_token_expect_c.val, s_token.val
      );

      comb' := FCCombiner_fold(out_expect_c, out_token_c);
      slot' := FCSlot_fold(out_expect_s, out_token_s);

    } else {

      assume slot.state.FCRequest?;

      ghost var out_expect_c := FCCombiner(comb.loc_s, FC.FCCombinerCollecting(comb.state.elems  + [Some(FC.Elem(slot.state.rid))]));
      ghost var out_token_expect_c := FCCombiner_unfold(out_expect_c);

      ghost var out_expect_s := FCSlot(slot.loc_s, slot.tid, FC.FCInProgress(slot.state.rid));
      ghost var out_token_expect_s := FCSlot_unfold(out_expect_s);

    FC.CombinerDoCollectRequest_is_transition(
      FC.dot(c_token.val, s_token.val),
      FC.dot(out_token_expect_c.val, out_token_expect_s.val)
    );

    glinear var out_token_c, out_token_s := FCTokens.internal_transition_2_2(
      c_token, s_token, out_token_expect_c.val, out_token_expect_s.val
    );

    comb' := FCCombiner_fold(out_expect_c, out_token_c);
    slot' := FCSlot_fold(out_expect_s, out_token_s);

    }
  }

  /* ----------------------------------------------------------------------------------------- */


  glinear method combiner_goto_responding(glinear comb: FCCombiner)
  returns (glinear comb': FCCombiner)
  requires comb.state.FCCombinerCollecting?
  requires |comb.state.elems| == MAX_THREADS_PER_REPLICA as int
  ensures comb' == FCCombiner(comb.loc_s, FC.FCCombinerResponding(comb.state.elems, 0))
  {
    glinear var c_token := FCCombiner_unfold(comb);

    ghost var out_expect := FCCombiner(comb.loc_s, FC.FCCombinerResponding(comb.state.elems, 0));
    ghost var out_token_expect := FCCombiner_unfold(out_expect);

    FC.CombinerGoToResponding_is_transition(c_token.val,out_token_expect.val);

    glinear var out_token := FCTokens.internal_transition(c_token, out_token_expect.val);

    comb' := FCCombiner_fold(out_expect, out_token);

  }


  /* ----------------------------------------------------------------------------------------- */


  glinear method combiner_response_skip(glinear comb: FCCombiner)
  returns (glinear comb': FCCombiner)
  requires comb.state.FCCombinerResponding?
  requires comb.state.idx < |comb.state.elems|
  requires comb.state.elems[comb.state.idx].None?
  ensures comb' == FCCombiner(comb.loc_s, comb.state.(idx := comb.state.idx + 1))
  {
    glinear var c_token := FCCombiner_unfold(comb);

    ghost var out_expect := FCCombiner(comb.loc_s, FC.FCCombinerResponding(comb.state.elems, comb.state.idx + 1));
    ghost var out_token_expect := FCCombiner_unfold(out_expect);


    FC.CombinerDoResponseSkip_is_transition(c_token.val,out_token_expect.val);

    glinear var out_token := FCTokens.internal_transition(c_token, out_token_expect.val);

    comb' := FCCombiner_fold(out_expect, out_token);
  }


  /* ----------------------------------------------------------------------------------------- */


  glinear method combiner_respond(glinear comb: FCCombiner, glinear slot: FCSlot)
  returns (glinear comb': FCCombiner, glinear slot': FCSlot)
  requires comb.state.FCCombinerResponding?
  requires comb.state.idx < |comb.state.elems|
  requires comb.state.elems[comb.state.idx].Some?
  requires slot.tid == comb.state.idx
  requires comb.loc_s == slot.loc_s
  ensures slot.state.FCInProgress?
  ensures comb' == FCCombiner(comb.loc_s, comb.state.(idx := comb.state.idx + 1))
  ensures slot' == slot.(state := FC.FCResponse(slot.state.rid))
  ensures comb.state.elems[comb.state.idx].value.rid == slot.state.rid
  {
    // that should follow from the invariant, need to obtain the invariant here.
    assume slot.state.FCInProgress?;
    assume comb.state.elems[comb.state.idx].value.rid == slot.state.rid;


    glinear var c_token := FCCombiner_unfold(comb);
    glinear var s_token := FCSlot_unfold(slot);

    ghost var out_expect_c := FCCombiner(comb.loc_s, FC.FCCombinerResponding(comb.state.elems, comb.state.idx + 1));
    ghost var out_token_expect_c := FCCombiner_unfold(out_expect_c);

    ghost var out_expect_s := FCSlot(slot.loc_s, slot.tid, FC.FCResponse(slot.state.rid));
    ghost var out_token_expect_s := FCSlot_unfold(out_expect_s);

    FC.CombinerDoResponse_is_transition(
      FC.dot(c_token.val, s_token.val),
      FC.dot(out_token_expect_c.val, out_token_expect_s.val)
    );

    glinear var out_token_c, out_token_s := FCTokens.internal_transition_2_2(
      c_token, s_token, out_token_expect_c.val, out_token_expect_s.val
    );

    comb' := FCCombiner_fold(out_expect_c, out_token_c);
    slot' := FCSlot_fold(out_expect_s, out_token_s);
  }


  /* ----------------------------------------------------------------------------------------- */


  glinear method combiner_goto_collecting(glinear comb: FCCombiner)
  returns (glinear comb': FCCombiner)
  requires comb.state.FCCombinerResponding?
  requires comb.state.idx == MAX_THREADS_PER_REPLICA as int
  ensures comb' == FCCombiner(comb.loc_s, FC.FCCombinerCollecting([]))
  {
    glinear var c_token := FCCombiner_unfold(comb);

    // that can be obtained from the Invariant: CombinerState_Elems
    assume |comb.state.elems| == MAX_THREADS_PER_REPLICA as int;

    ghost var out_expect := FCCombiner(comb.loc_s, FC.FCCombinerCollecting([]));
    ghost var out_token_expect := FCCombiner_unfold(out_expect);


    FC.CombinerGoToCollecting_is_transition(c_token.val,out_token_expect.val);

    glinear var out_token := FCTokens.internal_transition(c_token, out_token_expect.val);

    comb' := FCCombiner_fold(out_expect, out_token);
  }


  /* ----------------------------------------------------------------------------------------- */


  // Ops for the requester

  glinear method fc_send(glinear fc_client: FCClient, glinear fc_slot: FCSlot, ghost rid: RequestId)
  returns (glinear fc_client': FCClient, glinear fc_slot': FCSlot)
  requires fc_client.loc_s == fc_slot.loc_s
  requires fc_client.tid == fc_slot.tid
  requires fc_client.state.FCClientIdle?
  ensures fc_slot.state.FCEmpty?
  ensures fc_client' == fc_client.(state := FC.FCClientWaiting(rid))
  ensures fc_slot' == fc_slot.(state := FC.FCRequest(rid))
  {
    // that should follow from the invariant
    assume fc_slot.state.FCEmpty?;

    glinear var c_token := FCClient_unfold(fc_client);
    glinear var s_token := FCSlot_unfold(fc_slot);

    ghost var out_expect_c := FCClient(fc_client.loc_s, fc_client.tid , FC.FCClientWaiting(rid));
    ghost var out_token_expect_c := FCClient_unfold(out_expect_c);

    ghost var out_expect_s := FCSlot(fc_slot.loc_s, fc_slot.tid, FC.FCRequest(rid));
    ghost var out_token_expect_s := FCSlot_unfold(out_expect_s);


    FC.FCSend_is_transition(
      FC.dot(c_token.val, s_token.val),
      FC.dot(out_token_expect_c.val, out_token_expect_s.val),
      fc_client.tid,
      rid
    );

    glinear var out_token_c, out_token_s := FCTokens.internal_transition_2_2(
      c_token, s_token, out_token_expect_c.val, out_token_expect_s.val
    );

    fc_client':= FCClient_fold(out_expect_c, out_token_c);
    fc_slot'  := FCSlot_fold(out_expect_s, out_token_s);
  }


  /* ----------------------------------------------------------------------------------------- */


  glinear method fc_recv(glinear fc_client: FCClient, glinear fc_slot: FCSlot, ghost rid: RequestId)
  returns (glinear fc_client': FCClient, glinear fc_slot': FCSlot)
  requires fc_client.loc_s == fc_slot.loc_s
  requires fc_client.tid == fc_slot.tid
  requires fc_client.state.FCClientWaiting?
  requires !fc_slot.state.FCRequest?
  requires !fc_slot.state.FCInProgress?
  ensures fc_slot.state.FCResponse?
  ensures fc_slot.state.rid == fc_client.state.rid
  ensures fc_client' == fc_client.(state := FC.FCClientIdle)
  ensures fc_slot' == fc_slot.(state := FC.FCEmpty)
  {
    // that should follow from the invariant
    assume fc_slot.state.FCResponse?;
    assume fc_slot.state.rid == fc_client.state.rid;

    glinear var c_token := FCClient_unfold(fc_client);
    glinear var s_token := FCSlot_unfold(fc_slot);

    ghost var out_expect_c := FCClient(fc_client.loc_s, fc_client.tid , FC.FCClientIdle);
    ghost var out_token_expect_c := FCClient_unfold(out_expect_c);

    ghost var out_expect_s := FCSlot(fc_slot.loc_s, fc_slot.tid, FC.FCEmpty);
    ghost var out_token_expect_s := FCSlot_unfold(out_expect_s);


    FC.FCRecv_is_transition(
      FC.dot(c_token.val, s_token.val),
      FC.dot(out_token_expect_c.val, out_token_expect_s.val),
      fc_client.tid,
      rid
    );

    glinear var out_token_c, out_token_s := FCTokens.internal_transition_2_2(
      c_token, s_token, out_token_expect_c.val, out_token_expect_s.val
    );

    fc_client':= FCClient_fold(out_expect_c, out_token_c);
    fc_slot'  := FCSlot_fold(out_expect_s, out_token_s);
  }

  /* ----------------------------------------------------------------------------------------- */


  //// Utilties for the impl

  predicate RidsMatch(bools: seq<Option<FC.Elem>>, rids: seq<RequestId>,
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

  lemma {:induction true} RidsMatchAddNone(bools: seq<Option<FC.Elem>>, rids: seq<RequestId>,
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

  lemma {:induction true} RidsMatchAddRidElem(bools: seq<Option<FC.Elem>>, rids: seq<RequestId>,
      bools_start: nat,
      bools_end: nat,
      rids_start: nat,
      rids_end: nat,
      rid: RequestId)
  requires 0 <= bools_start <= bools_end <= |bools|
  requires 0 <= rids_start <= rids_end <= |rids|
  requires RidsMatch(bools, rids, bools_start, bools_end, rids_start, rids_end)
  ensures RidsMatch(bools+[Some(FC.Elem(rid))], rids+[rid], bools_start, bools_end, rids_start, rids_end)
  {
  }

  lemma RidsMatchPop(bools: seq<Option<FC.Elem>>, rids: seq<RequestId>,
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
