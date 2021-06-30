// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/KeyType.s.dfy"
include "../lib/Base/SequencesLite.s.dfy"
include "Message.s.dfy"
include "Interp.s.dfy"
include "AtomicStateMachine.s.dfy"
include "CrashTolerant.s.dfy"

module MapSpecMod refines AtomicStateMachineMod {
  import opened ValueMessage
  import opened KeyType
  import InterpMod

  // UI
  datatype Input = GetInput(k: Key) | PutInput(k: Key, v: Value) | NoopInput
  datatype Output = GetOutput(v: Value) | PutOutput | NoopOutput

  // State machine
  datatype Variables = Variables(interp: InterpMod.Interp)

  function InitState() : Variables {
    Variables(InterpMod.Empty())
  }

  predicate Query(s: Variables, s': Variables, k: Key, v: Value)
  {
    && v == s.interp.mi[k].value
    && s' == s
  }

  predicate Put(s: Variables, s': Variables, k: Key, v: Value)
  {
    && s' == s.(interp := s.interp.Put(k, Define(v)))
  }

  predicate Next(v: Variables, v': Variables, input: Input, out: Output)
  {
  true
    || (
        && input.GetInput?
        && out.GetOutput?
        && Query(v, v', input.k, out.v)
       )
    || (
        && input.PutInput?
        && out.PutOutput?
        && Put(v, v', input.k, input.v)
       )
    || (
        && input.NoopInput?
        && out.NoopOutput?
        && v' == v
       )
  }
}

module CrashTolerantMapSpecMod refines CrashTolerantMod(MapSpecMod) {
}
