include "../framework/StateMachines.s.dfy"
include "NRSpec.s.dfy"
include "NRSimple.i.dfy"

module NROne(nrifc: NRIfc) refines StateMachine(nrifc) {
  type Variables = nrifc.NRState

  predicate Init(s: Variables) { s == nrifc.init_state() }

  predicate Next(s: Variables, s': Variables, op: ifc.Op) {
    match op.input {
      case ROp(readonly_op) =>
        && op.output == nrifc.read(s, readonly_op)
        && s' == s
      case UOp(update_op) =>
        && nrifc.update(s, update_op) == nrifc.UpdateResult(s', op.output)
    }
  }
}

module Behavior(ifc: Ifc, sm: StateMachine(ifc)) {
  datatype Behavior =
    | Stepped(s: sm.Variables, op: sm.ifc.Op, tail: Behavior)
    | Inited(s: sm.Variables)
  {
    predicate WF() {
      match this {
        case Stepped(s', op, tail) =>
          && tail.WF()
          && sm.Next(tail.s, s', op)
        case Inited(s) =>
          && sm.Init(s)
      }
    }
  }
}

module NRSimple_Refines_NRSingle(nrifc: NRIfc) {
  import simple = NRSimple(nrifc)
  import one = AsyncStateMachine(nrifc, NROne(nrifc))

  import AI = AsyncIfc(nrifc)
  import SimpleB = Behavior(AsyncIfc(nrifc), NRSimple(nrifc))
  import OneB = Behavior(AsyncIfc(nrifc), AsyncStateMachine(nrifc, NROne(nrifc)))
  import opened RequestIds

  predicate equiv(a: SimpleB.Behavior, b: OneB.Behavior)
  decreases a, b
  {
    || (a.Inited? && b.Inited?)
    || (a.Stepped? && a.op.InternalOp? && equiv(a.tail, b))
    || (b.Stepped? && b.op.InternalOp? && equiv(a, b.tail))
    || (a.Stepped? && b.Stepped? && a.op == b.op && equiv(a.tail, b.tail))
  }

  /*
  function IReqs(s: simple.Variables, r_points: map<RequestId, nat>)
    : map<RequestId,     
  {
    map 
  }
  */

  predicate FutureRidOk(s: simple.Variables, rid: RequestId, version: nat)
  {
    && rid in s.readonly_reqs
    && (s.readonly_reqs[rid].ReadInit? ==>
      s.ctail <= version
    )
    && (s.readonly_reqs[rid].ReadReq? ==>
      s.readonly_reqs[rid].ctail_at_start <= version
    )
  }

  predicate FuturePointsOk(s: simple.Variables, r_points: map<RequestId, nat>)
  {
    forall rid | rid in r_points :: FutureRidOk(s, rid, r_points[rid])
  }

  predicate readonly_is_req(
      s: simple.Variables, t: one.Variables, r_points: map<RequestId, nat>,
      rid: RequestId)
  {
    && rid in s.readonly_reqs
    && rid in t.reqs
    && t.reqs[rid] == nrifc.ROp(s.readonly_reqs[rid].op)
    && (s.readonly_reqs[rid].ReadReq? ==>
      && s.readonly_reqs[rid].ctail_at_start <= s.ctail
    )
    && (rid in r_points ==> (
      && s.ctail <= r_points[rid]
      && (s.readonly_reqs[rid].ReadReq? ==>
        s.ctail < r_points[rid]
      )
    ))
  }

  predicate readonly_is_resp(
      s: simple.Variables, t: one.Variables, r_points: map<RequestId, nat>,
      rid: RequestId)
  {
    && rid in t.resps
    && rid in s.readonly_reqs
    && s.readonly_reqs[rid].ReadReq?
    && s.readonly_reqs[rid].ctail_at_start <= s.ctail
    && (rid in r_points ==> (
      && s.readonly_reqs[rid].ctail_at_start <= r_points[rid] <= s.ctail
      && 0 <= r_points[rid] <= |s.log|
      && t.resps[rid] == nrifc.read(
          simple.state_at_version(s.log, r_points[rid]),
          s.readonly_reqs[rid].op)
    ))
  }

  predicate update_is_done(
      s: simple.Variables, t: one.Variables, r_points: map<RequestId, nat>,
      rid: RequestId)
  {
    && rid in t.resps
    && rid in s.update_resps
    && 0 <= s.update_resps[rid].idx_in_log < |s.log|
    && t.resps[rid] == nrifc.update(
        simple.state_at_version(s.log, s.update_resps[rid].idx_in_log),
        s.log[s.update_resps[rid].idx_in_log]
     ).return_value
  }

  predicate rel(s: simple.Variables, t: one.Variables, r_points: map<RequestId, nat>)
  {
    && rel_basic(s, t, r_points)
    && rel_r(s, t, r_points)
  }

  predicate HasVersion(update_resps: map<RequestId, simple.UpdateResp>, ver: int)
  {
    exists rid :: rid in update_resps && update_resps[rid].idx_in_log == ver
  }

  predicate rel_basic(s: simple.Variables, t: one.Variables, r_points: map<RequestId, nat>)
  {
    && 0 <= s.ctail <= |s.log|
    && t.s == simple.state_at_version(s.log, s.ctail)
    //&& t.reqs == IReqs(s, r_points)
    //&& t.resps == IResps(s, r_points)
    && (s.readonly_reqs.Keys !! s.update_reqs.Keys !! s.update_resps.Keys)
    && (t.reqs.Keys !! t.resps.Keys)
    && (forall rid ::
        (rid in s.readonly_reqs || rid in s.update_reqs || rid in s.update_resps) <==>
          (rid in t.reqs || rid in t.resps))
    && (forall rid :: rid in t.reqs && t.reqs[rid].ROp? ==>
            && rid in s.readonly_reqs
    )
    && (forall rid :: rid in t.reqs && t.reqs[rid].UOp? ==>
            rid in s.update_reqs || rid in s.update_resps
    )
    && (forall rid :: rid in t.resps ==>
            rid in s.readonly_reqs || rid in s.update_resps
    )
    && (forall ver | s.ctail <= ver < |s.log| :: HasVersion(s.update_resps, ver))
    && (forall rid1, rid2 | rid1 in s.update_resps && rid2 in s.update_resps && rid1 != rid2 ::
        s.update_resps[rid1] != s.update_resps[rid2])
    && (forall rid | rid in s.update_resps ::
            s.update_resps[rid].idx_in_log < |s.log|)

    && (forall rid | rid in s.update_reqs ::
            && rid in t.reqs
            && t.reqs[rid] == nrifc.UOp(s.update_reqs[rid])
    )

    && (forall rid | rid in s.update_resps && (s.update_resps[rid].idx_in_log >= s.ctail) ::
            && rid in t.reqs
            && 0 <= s.update_resps[rid].idx_in_log < |s.log|
            && t.reqs[rid] == nrifc.UOp(s.log[s.update_resps[rid].idx_in_log])
    )

    && (forall rid | rid in s.update_resps && (s.update_resps[rid].idx_in_log < s.ctail) ::
      update_is_done(s, t, r_points, rid)
    )
  }

  predicate rel_r(s: simple.Variables, t: one.Variables, r_points: map<RequestId, nat>)
  {
    && (forall rid | rid in s.readonly_reqs && rid in t.reqs ::
      readonly_is_req(s, t, r_points, rid)
    )

    && (forall rid | rid in s.readonly_reqs && rid in t.resps ::
      readonly_is_resp(s, t, r_points, rid)
    )
  }

  lemma StartUpdate_Refines(s: simple.Variables, s': simple.Variables, Is: one.Variables,
      r_points: map<RequestId, nat>,
      rid: RequestId, uop: nrifc.UpdateOp)
  returns (Is': one.Variables)
  requires simple.StartUpdate(s, s', rid, uop)
  requires rel(s, Is, r_points)
  ensures rel(s', Is', r_points)
  ensures one.Next(Is, Is', AI.Start(rid, nrifc.UOp(uop)))
  {
    Is' := Is.(reqs := Is.reqs[rid := nrifc.UOp(uop)]);
  }

  lemma state_at_version_preserves(a: seq<nrifc.UpdateOp>, b: seq<nrifc.UpdateOp>, x: seq<nrifc.UpdateOp>, i: nat)
  requires b == a + x
  requires 0 <= i <= |a|
  requires 0 <= i <= |b|
  ensures simple.state_at_version(a, i) == simple.state_at_version(b, i)
  decreases i
  {
    if i > 0 {
      state_at_version_preserves(a, b, x, i-1);
    }
  }

  lemma AddUpdateToLog_Refines(s: simple.Variables, s': simple.Variables, Is: one.Variables,
      r_points: map<RequestId, nat>,
      request_ids: seq<RequestId>)
  returns (Is': one.Variables)
  requires simple.AddUpdateToLog(s, s', request_ids)
  requires rel(s, Is, r_points)
  ensures rel(s', Is', r_points)
  ensures one.Next(Is, Is', AI.InternalOp)
  {
    Is' := Is;

    var new_log_entries := simple.ConstructNewLogEntries(request_ids, s.update_reqs);
    var new_responses := simple.ConstructUpdateResponses(request_ids, |s.log|);

    state_at_version_preserves(s.log, s'.log, new_log_entries, s.ctail);

    /*
    forall rid
    ensures rid in s.update_reqs ==> rid in s'.update_reqs || rid in s'.update_resps
    ensures rid in s.update_resps ==> rid in s'.update_resps
    ensures rid in s'.update_reqs ==> rid in s.update_reqs
    ensures rid in s'.update_resps ==> rid in s.update_reqs || rid in s.update_resps
    {
      simple.reveal_map_filter();
      simple.reveal_map_update();
      simple.ConstructUpdateResponses_in_map(request_ids, |s.log|, new_responses);
      if (rid in request_ids) {
        if rid in s.update_reqs {
          assert rid in s'.update_resps;
        }
        assert rid in s.update_reqs ==> rid in s'.update_reqs || rid in s'.update_resps;
        assert rid in s.update_resps ==> rid in s'.update_resps;
        assert rid in s'.update_reqs ==> rid in s.update_reqs;
        assert rid in s'.update_resps ==> rid in s.update_reqs || rid in s.update_resps;
      } else {
        assert rid in s.update_reqs ==> rid in s'.update_reqs || rid in s'.update_resps;
        assert rid in s.update_resps ==> rid in s'.update_resps;
        assert rid in s'.update_reqs ==> rid in s.update_reqs;
        assert rid in s'.update_resps ==> rid in s.update_reqs || rid in s.update_resps;
      }
    }

    assert s'.update_reqs.Keys !! s'.update_resps.Keys
    by {
      simple.reveal_map_filter();
      simple.reveal_map_update();
      simple.ConstructUpdateResponses_in_map(request_ids, |s.log|, new_responses);
    }
    */

    simple.reveal_map_filter();
    simple.reveal_map_update();
    simple.ConstructUpdateResponses_in_map(request_ids, |s.log|, new_responses);

    /*forall rid | rid in s.readonly_reqs && rid in t.resps ::
            && readonly_is_resp(s, t, r_points, rid)*/

    forall rid | rid in s'.readonly_reqs && rid in Is'.resps
    ensures readonly_is_resp(s', Is', r_points, rid)
    {
      if rid in r_points {
        state_at_version_preserves(s.log, s'.log, new_log_entries, r_points[rid]);
      }
    }

    forall rid | rid in s'.update_resps && (s'.update_resps[rid].idx_in_log < s'.ctail)
    ensures update_is_done(s', Is', r_points, rid)
    {
      state_at_version_preserves(s.log, s'.log, new_log_entries,
          s.update_resps[rid].idx_in_log);
    }

    forall ver | s'.ctail <= ver < |s'.log|
    ensures HasVersion(s'.update_resps, ver)
    {
      if ver < |s'.log| - |new_log_entries| {
        assert HasVersion(s.update_resps, ver);
        var qid :| qid in s.update_resps && s.update_resps[qid].idx_in_log == ver;
        assert s'.update_resps[qid].idx_in_log == ver;
      } else {
        var j := ver - (|s'.log| - |new_log_entries|);
        assert s'.update_resps[request_ids[j]].idx_in_log == ver;
      }
    }
    /*
    forall rid1, rid2 | rid1 in s'.update_resps && rid2 in s'.update_resps && rid1 != rid2
    ensures s'.update_resps[rid1] != s'.update_resps[rid2]
    {
      if s'.update_resps[rid1].idx_in_log < |s.log| {
        if s'.update_resps[rid2].idx_in_log < |s.log| {
          assert s'.update_resps[rid1] != s'.update_resps[rid2];
        } else {
          assert s'.update_resps[rid1] != s'.update_resps[rid2];
        }
      } else {
        if s'.update_resps[rid2].idx_in_log < |s.log| {
          assert s'.update_resps[rid1] != s'.update_resps[rid2];
        } else {
          assert s'.update_resps[rid1] != s'.update_resps[rid2];
        }
      }
    }
    */
  }

  lemma EndUpdate_Refines(s: simple.Variables, s': simple.Variables, Is: one.Variables,
      r_points: map<RequestId, nat>,
      rid: RequestId, return_value: nrifc.ReturnType)
  returns (Is': one.Variables)
  requires simple.EndUpdate(s, s', rid, return_value)
  requires rel(s, Is, r_points)
  ensures rel(s', Is', r_points)
  ensures one.Next(Is, Is', AI.End(rid, return_value))
  {
    Is' := Is.(resps := Is.resps - {rid});

    forall ver | s'.ctail <= ver < |s'.log|
    ensures HasVersion(s'.update_resps, ver)
    {
      assert HasVersion(s.update_resps, ver);
      var qid :| qid in s.update_resps && s.update_resps[qid].idx_in_log == ver;
      assert s'.update_resps[qid].idx_in_log == ver;
    }
  }

  lemma StartReadonly_Refines(s: simple.Variables, s': simple.Variables, Is: one.Variables,
      r_points: map<RequestId, nat>,
      rid: RequestId, rop: nrifc.ReadonlyOp)
  returns (Is': one.Variables)
  requires simple.StartReadonly(s, s', rid, rop)
  requires rel(s, Is, r_points - {rid});
  requires FuturePointsOk(s', r_points)
  ensures rel(s', Is', r_points)
  ensures one.Next(Is, Is', AI.Start(rid, nrifc.ROp(rop)))
  {
    Is' := Is.(reqs := Is.reqs[rid := nrifc.ROp(rop)]);

    forall rid | rid in s'.readonly_reqs && rid in Is'.reqs
    ensures readonly_is_req(s', Is', r_points, rid)
    {
    }
  }

  lemma ReadCtail_Refines(s: simple.Variables, s': simple.Variables, Is: one.Variables,
      r_points: map<RequestId, nat>,
      rid: RequestId)
  returns (Is': one.Variables)
  requires simple.ReadCtail(s, s', rid)
  requires rel(s, Is, r_points);
  requires FuturePointsOk(s', r_points)
  ensures rel(s', Is', r_points)
  ensures one.Next(Is, Is', AI.InternalOp)
  {
    if rid in r_points && r_points[rid] == s.ctail {
      // linearization point is now
      var retval := nrifc.read(
            simple.state_at_version(s.log, r_points[rid]),
            s.readonly_reqs[rid].op);
      Is' := Is.(reqs := Is.reqs - {rid})
               .(resps := Is.resps[rid := retval]);

      var input := nrifc.ROp(s.readonly_reqs[rid].op);
      assert one.InternalNext(rid, input, retval, Is, Is');

      assert rel(s', Is', r_points);
      assert one.Next(Is, Is', AI.InternalOp);
    } else {
      Is' := Is;

      assert rel(s', Is', r_points);
      assert one.Next(Is, Is', AI.InternalOp);
    }
  }

  lemma FinishReadonly_Refines(s: simple.Variables, s': simple.Variables, Is: one.Variables,
      r_points: map<RequestId, nat>,
      rid: RequestId, version: nat, return_value: nrifc.ReturnType)
  returns (Is': one.Variables)
  requires simple.FinishReadonly(s, s', rid, version, return_value)
  requires rel(s, Is, r_points[rid := version])
  ensures rel(s', Is', r_points)
  ensures one.Next(Is, Is', AI.End(rid, return_value))
  {
    Is' := Is.(resps := Is.resps - {rid});
  }

  function AllReadsFor(readonly_reqs: map<RequestId, simple.ReadReq>,
    r_points: map<RequestId, nat>, ver: int) : set<RequestId>
  {
    set rid: RequestId | rid in r_points && r_points[rid] == ver
        && rid in readonly_reqs && readonly_reqs[rid].ReadReq?
  }

  lemma pop_rid(t: set<RequestId>)
  returns (t': set<RequestId>, r: RequestId)
  requires t != {}
  ensures |t'| < |t|
  ensures r in t
  ensures t' == t - {r}
  {
    r :| r in t;
    t' := t - {r};
    assert t == t' + {r};
    assert |t| == |t'| + 1;
  }

  lemma {:induction true} trick_equiv(a: SimpleB.Behavior, a': SimpleB.Behavior, b: OneB.Behavior)
  requires equiv(a, b)
  requires a.Stepped? && a'.Stepped?
  requires a.tail == a'.tail
  requires a.op.InternalOp?
  requires a'.op.InternalOp?
  ensures equiv(a', b)
  {
  }

  lemma IncCtail1(b: OneB.Behavior, a: SimpleB.Behavior, a': SimpleB.Behavior,
      r_points: map<RequestId, nat>)
  returns (b': OneB.Behavior)
  requires a.WF()
  requires FuturePointsOk(a'.s, r_points)
  requires a.Stepped? && a'.Stepped?
  requires a.tail == a'.tail
  requires a.op.InternalOp?
  requires a'.op.InternalOp?
  requires a'.s == a.s.(ctail := a.s.ctail + 1)
  requires a.s.ctail + 1 <= |a.s.log|
  requires b.WF()
  requires equiv(a, b)
  requires rel(a.s, b.s, r_points)
  ensures b'.WF()
  ensures equiv(a', b')
  ensures rel(a'.s, b'.s, r_points)
  {
    // Linearization point for the update

    var s := a.s;
    var s' := a'.s;

    assert s.ctail < |s.log|;
    assert HasVersion(s.update_resps, s.ctail);
    var urid :| urid in s.update_resps && s.update_resps[urid].idx_in_log == s.ctail;

    var x := nrifc.update(
        simple.state_at_version(s.log, s.update_resps[urid].idx_in_log),
        s.log[s.update_resps[urid].idx_in_log]
     );
    var uret := x.return_value;

    var Is' := b.s
        .(s := x.new_state)
        .(reqs := b.s.reqs - {urid})
        .(resps := b.s.resps[urid := uret]);
    b' := OneB.Stepped(Is', AI.InternalOp, b);

    var input := nrifc.UOp(s.log[s.update_resps[urid].idx_in_log]);
    assert simple.state_at_version(s.log, s.update_resps[urid].idx_in_log) == b.s.s;
    assert one.InternalNext(urid, input, uret, b.s, b'.s);
    assert one.Next(b.s, b'.s, AI.InternalOp);

    var the_reads := AllReadsFor(s.readonly_reqs, r_points, s.ctail + 1);

    trick_equiv(a, a', b');

    /*forall rid | rid in s.readonly_reqs && rid in b'.s.reqs && rid !in the_reads
    ensures readonly_is_req(s', b'.s, r_points, rid)
    {
      if rid in r_points {
        assert s.ctail <= r_points[rid];
        assert r_points[rid] != s.ctail + 1;
        assert s'.ctail == s.ctail + 1;
        assert s'.ctail <= r_points[rid];
      }
    }*/

    while the_reads != {}
    decreases |the_reads|
    invariant b'.WF()
    invariant equiv(a', b')
    invariant rel_basic(a'.s, b'.s, r_points)
    invariant forall rid | rid in the_reads ::
        && rid in r_points
        && r_points[rid] == s.ctail + 1
        && rid in s.readonly_reqs
        && s.readonly_reqs[rid].ReadReq?
    invariant (forall rid | rid in s.readonly_reqs && rid in b'.s.reqs ::
      rid !in the_reads ==>
      readonly_is_req(s', b'.s, r_points, rid)
    )
    invariant (forall rid | rid in s.readonly_reqs && rid in b'.s.resps ::
      rid !in the_reads ==>
      readonly_is_resp(s', b'.s, r_points, rid)
    )
    invariant (forall rid | rid in s.readonly_reqs && rid in b'.s.reqs ::
      rid in the_reads ==>
      readonly_is_req(s, b'.s, r_points, rid)
    )
    invariant (forall rid | rid in s.readonly_reqs && rid in b'.s.resps ::
      rid in the_reads ==>
      readonly_is_resp(s, b'.s, r_points, rid)
    )
    {
      var the_reads', rid := pop_rid(the_reads);

      var ret := nrifc.read(
          simple.state_at_version(s.log, r_points[rid]),
          s.readonly_reqs[rid].op);

      var Is'' := b'.s
          .(reqs := b'.s.reqs - {rid})
          .(resps := b'.s.resps[rid := ret]);

      var b'' := OneB.Stepped(Is'', AI.InternalOp, b');

      var input := nrifc.ROp(s.readonly_reqs[rid].op);
      assert one.InternalNext(rid, input, ret, b'.s, b''.s);
      assert one.Next(b'.s, b''.s, AI.InternalOp);

      if rid in s.readonly_reqs && rid in b''.s.resps && rid !in the_reads' {
        assert readonly_is_resp(s', b''.s, r_points, rid);
      }
      forall rid | rid in s.readonly_reqs && rid in b''.s.resps && rid !in the_reads'
      ensures readonly_is_resp(s', b''.s, r_points, rid)
      {
      }

      the_reads := the_reads';
      b' := b'';
    }
  }

  lemma CtailRec(a: SimpleB.Behavior, r_points: map<RequestId, nat>,
      new_ctail: nat)
  returns (b: OneB.Behavior)
  requires a.WF()
  requires FuturePointsOk(a.s, r_points)
  requires a.Stepped?
  requires a.op.InternalOp?
  requires simple.IncreaseCtail(a.tail.s, a.s, new_ctail)
  ensures b.WF()
  ensures equiv(a, b)
  ensures rel(a.s, b.s, r_points)
  decreases a.tail, 1, new_ctail
  {
    if new_ctail == a.tail.s.ctail {
      b := ExistsEquivBehaviorRec(a.tail, r_points);
      assert a.s == a.tail.s;
    } else {
      var amid := a.(s := a.s.(ctail := a.s.ctail - 1));
      assert simple.NextStep(amid.tail.s, amid.s, AI.InternalOp, simple.IncreaseCtail_Step(new_ctail - 1));
      var bmid := CtailRec(amid, r_points, new_ctail - 1);
      b := IncCtail1(bmid, amid, a, r_points);
    }
  }

  lemma ExistsEquivBehaviorRec(a: SimpleB.Behavior, r_points: map<RequestId, nat>)
  returns (b: OneB.Behavior)
  requires a.WF()
  requires FuturePointsOk(a.s, r_points)
  ensures b.WF()
  ensures equiv(a, b)
  ensures rel(a.s, b.s, r_points)
  decreases a, 0, 0
  {
    match a {
      case Inited(s) => {
        b := OneB.Inited(one.Variables(nrifc.init_state(), map[], map[])); 
      }
      case Stepped(s', op, tail) => {
        var step :| simple.NextStep(tail.s, s', op, step);
        match step {
          case StartUpdate_Step(rid: RequestId, uop: nrifc.UpdateOp) => {
            var b0 := ExistsEquivBehaviorRec(tail, r_points);
            var Is' := StartUpdate_Refines(tail.s, s', b0.s, r_points, rid, uop);
            b := OneB.Stepped(Is', op, b0);
          }
          case AddUpdateToLog_Step(request_ids: seq<RequestId>) => {
            var b0 := ExistsEquivBehaviorRec(tail, r_points);
            var Is' := AddUpdateToLog_Refines(tail.s, s', b0.s, r_points, request_ids);
            b := OneB.Stepped(Is', op, b0);
          }
          case EndUpdate_Step(rid: RequestId, return_value: nrifc.ReturnType) => {
            var b0 := ExistsEquivBehaviorRec(tail, r_points);
            var Is' := EndUpdate_Refines(tail.s, s', b0.s, r_points, rid, return_value);
            b := OneB.Stepped(Is', op, b0);
          }
          case IncreaseCtail_Step(new_ctail: nat) => {
            b := CtailRec(a, r_points, new_ctail);
          }
          case StartReadonly_Step(rid: RequestId, rop: nrifc.ReadonlyOp) => {
            var b0 := ExistsEquivBehaviorRec(tail, r_points - {rid});
            var Is' := StartReadonly_Refines(tail.s, s', b0.s, r_points, rid, rop);
            b := OneB.Stepped(Is', op, b0);
          }
          case ReadCtail_Step(rid: RequestId) => {
            var b0 := ExistsEquivBehaviorRec(tail, r_points);
            var Is' := ReadCtail_Refines(tail.s, s', b0.s, r_points, rid);
            b := OneB.Stepped(Is', op, b0);
          }
          case FinishReadonly_Step(rid: RequestId, version: nat, return_value: nrifc.ReturnType) => {
            var b0 := ExistsEquivBehaviorRec(tail, r_points[rid := version]);
            var Is' := FinishReadonly_Refines(tail.s, s', b0.s, r_points, rid, version, return_value);
            b := OneB.Stepped(Is', op, b0);
          }
          case Stutter_Step => {
            b := ExistsEquivBehaviorRec(tail, r_points);
          }
        }
      }
    }
  }

  lemma ExistsEquivBehavior(a: SimpleB.Behavior)
  returns (b: OneB.Behavior)
  requires a.WF()
  ensures b.WF()
  ensures equiv(a, b)
  {
    b := ExistsEquivBehaviorRec(a, map[]);
  }
}
