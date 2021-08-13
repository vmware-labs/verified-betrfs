include "NRSpec.s.dfy"

module NRSimple(nrifc: NRIfc) refines StateMachine(nrifc) {
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
}
