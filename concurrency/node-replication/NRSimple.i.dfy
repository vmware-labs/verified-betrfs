include "NRSpec.s.dfy"

module NRSimple(nrifc: NRIfc) refines StateMachine(AsyncIfc(nrifc)) {
  import opened RequestIds

  datatype ReadReq = ReadReq(ctail_at_start: nat, op: nrifc.ReadonlyOp)

  datatype UpdateResp = UpdateResp(idx_in_log: nat, ret: nrifc.ReturnType)

  datatype Variables = Variables(
    log: seq<nrifc.UpdateOp>,
    ctail: nat,
    readonly_reqs: map<RequestId, ReadReq>,
    update_reqs: map<RequestId, nrifc.UpdateOp>,
    update_resps: map<RequestId, UpdateResp>
  )

  predicate Init(s: Variables)
  {
    && s == Variables([], 0, map[], map[], map[])
  }

  // Given a log of ops and a version number, compute the state at that version
  function state_at_version(log: seq<nrifc.UpdateOp>, version: nat) : nrifc.NRState
  requires 0 <= version <= |log|
  {
    if version == 0 then
      nrifc.init_state()
    else
      nrifc.update(state_at_version(log, version - 1), log[version-1]).new_state
  }

  // ctail can increase at any moment

  predicate IncreaseCtail(s: Variables, s': Variables, new_ctail: nat)
  {
    && s.ctail <= new_ctail <= |s.log|
    && s' == s.(ctail := new_ctail)
  }

  // When a 'readonly' request begins record the ctail.
  // When it ends, we must return the answer at some version >= the recorded value.

  // Should correspond to point where we insert a ticket...
  predicate StartReadonly(s: Variables, s': Variables, rid: RequestId, op: nrifc.ReadonlyOp)
  {
    && rid !in s.readonly_reqs
    && s' == s.(readonly_reqs := s.readonly_reqs[rid := ReadReq(s.ctail, op)])
  }

  predicate FinishReadonly(s: Variables, s': Variables,
      rid: RequestId, version: nat, return_value: nrifc.ReturnType)
  {
    && rid in s.readonly_reqs
    && s.readonly_reqs[rid].ctail_at_start <= version <= |s.log|
    && s' == s.(readonly_reqs := s.readonly_reqs - {rid})
    && return_value == nrifc.read(state_at_version(s.log, version), s.readonly_reqs[rid].op)
  }

  // For an 'update' request, we put it in the log at some point (giving the total
  // order on updates). However, to complete, the ctail must be > the index where we
  // put the op

  predicate StartUpdate(s: Variables, s': Variables, rid: RequestId, op: nrifc.UpdateOp)
  {
    && rid !in s.update_reqs
    && s' == s.(update_reqs := s.update_reqs[rid := op])
  }

  predicate AddUpdateToLog(s: Variables, s': Variables, rid: RequestId)
  {
    && rid in s.update_reqs
    && var op := s.update_reqs[rid];
    && var ret := nrifc.update(state_at_version(s.log, |s.log|), op).return_value;
    && s' == s.(log := s.log + [s.update_reqs[rid]])
              .(update_reqs := s.update_reqs - {rid})
              .(update_resps := s.update_resps[rid := UpdateResp(|s.log|, ret)])
  }

  predicate EndUpdate(s: Variables, s': Variables,
      rid: RequestId, return_value: nrifc.ReturnType)
  {
    && rid in s.update_resps
    && s.ctail > s.update_resps[rid].idx_in_log
    && s' == s.(update_resps := s.update_resps - {rid})
    && return_value == s.update_resps[rid].ret
  }


  // the stepping throug the state machine

  datatype Step =
    | StartUpdate_Step(rid: RequestId, uop: nrifc.UpdateOp)
    | AddUpdateToLog_Step(rid: RequestId)
    | EndUpdate_Step(rid: RequestId, return_value: nrifc.ReturnType)
    | IncreaseCtail_Step(new_ctail: nat)
    | StartReadonly_Step(rid: RequestId, rop: nrifc.ReadonlyOp)
    | FinishReadonly_Step(rid: RequestId, version: nat, return_value: nrifc.ReturnType)
    | Stutter_Step

  predicate NextStep(s: Variables, s': Variables, op: ifc.Op, step: Step) {
    match step {
      case StartUpdate_Step(rid: RequestId, update_op: nrifc.UpdateOp) =>
          && op == ifc.Start(rid, nrifc.UOp(update_op))
          && StartUpdate(s, s', rid, update_op)

      case AddUpdateToLog_Step(rid: RequestId) =>
          && op == ifc.InternalOp
          && AddUpdateToLog(s, s', rid)

      case EndUpdate_Step(rid: RequestId, return_value: nrifc.ReturnType) =>
          && op == ifc.End(rid, return_value)
          && EndUpdate(s, s', rid, return_value)

      case IncreaseCtail_Step(new_ctail: nat) =>
          && op == ifc.InternalOp
          && IncreaseCtail(s, s', new_ctail)

      case StartReadonly_Step(rid: RequestId, read_op: nrifc.ReadonlyOp) =>
          && op == ifc.Start(rid, nrifc.ROp(read_op))
          && StartReadonly(s, s', rid, read_op)

      case FinishReadonly_Step(rid: RequestId, version: nat, return_value: nrifc.ReturnType) => 
          && op == ifc.End(rid, return_value)
          && FinishReadonly(s, s', rid, version, return_value)

      case Stutter_Step =>
          && op == ifc.InternalOp
          && s' == s
    }
  }

  predicate Next(s: Variables, s': Variables, op: ifc.Op) {
    exists step :: NextStep(s, s', op, step)
  }

  // invariant
  predicate Inv(s: Variables) {
    && s.ctail <= |s.log|
  }


  lemma IncreaseCtail_PreservesInv(s: Variables, s': Variables, new_ctail: nat)
    requires Inv(s)
    requires IncreaseCtail(s, s', new_ctail)
    ensures Inv(s')
  {

  }

  lemma StartReadonly_PreservesInv(s: Variables, s': Variables, rid: RequestId, op: nrifc.ReadonlyOp)
    requires Inv(s)
    requires StartReadonly(s, s', rid, op)
    ensures Inv(s')
  {

  }

  lemma FinishReadonly_PreservesInv(s: Variables, s': Variables,
      rid: RequestId, version: nat, return_value: nrifc.ReturnType)
    requires Inv(s)
    requires FinishReadonly(s, s', rid, version, return_value)
    ensures Inv(s')
  {

  }

  lemma StartUpdate_PreservesInv(s: Variables, s': Variables, rid: RequestId, op: nrifc.UpdateOp)
    requires Inv(s)
    requires StartUpdate(s, s', rid, op)
    ensures Inv(s')
  {

  }

  lemma AddUpdateToLog_PreservesInv(s: Variables, s': Variables, rid: RequestId)
    requires Inv(s)
    requires AddUpdateToLog(s, s', rid)
    ensures Inv(s')
  {

  }

  lemma EndUpdate_PreservesInv(s: Variables, s': Variables, rid: RequestId, return_value: nrifc.ReturnType)
    requires Inv(s)
    requires EndUpdate(s, s', rid, return_value)
    ensures Inv(s')
  {

  }

  lemma NextStep_PreservesInv(s: Variables, s': Variables, op: ifc.Op, step: Step)
    requires Inv(s)
    requires NextStep(s, s', op, step)
    ensures Inv(s')
  {
    match step {
      case StartUpdate_Step(rid: RequestId, op: nrifc.UpdateOp) => StartUpdate_PreservesInv(s, s', rid, op);
      case AddUpdateToLog_Step(rid: RequestId) => AddUpdateToLog_PreservesInv(s, s', rid);
      case EndUpdate_Step(rid: RequestId, return_value: nrifc.ReturnType) => EndUpdate_PreservesInv(s, s', rid, return_value);
      case IncreaseCtail_Step(new_ctail: nat) => IncreaseCtail_PreservesInv(s, s', new_ctail);
      case StartReadonly_Step(rid: RequestId, op: nrifc.ReadonlyOp) => StartReadonly_PreservesInv(s, s', rid, op);
      case FinishReadonly_Step(rid: RequestId, version: nat, return_value: nrifc.ReturnType) => FinishReadonly_PreservesInv(s, s', rid, version, return_value);
      case Stutter_Step => { }
    }
  }

  lemma Next_Implies_inv(s: Variables, s': Variables, op: ifc.Op)
    requires Inv(s)
    requires Next(s, s', op)
    ensures Inv(s')
  {
    var step :| NextStep(s, s', op, step);
    NextStep_PreservesInv(s, s', op, step);
  }

  /// invariance proofs
  lemma Init_Implies_Inv(s: Variables)
    requires Init(s)
    ensures Inv(s)
  {

  }
}
