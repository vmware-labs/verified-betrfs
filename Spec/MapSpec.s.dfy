// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/KeyType.s.dfy"
include "../lib/Base/SequencesLite.s.dfy"
include "Message.s.dfy"
include "StampedMap.s.dfy"
include "AtomicStateMachine.s.dfy"
include "CrashTolerant.s.dfy"

module MapSpecMod refines AtomicStateMachineMod {
  import opened ValueMessage
  import opened KeyType
  import StampedMapMod

  // UI
  datatype Input = GetInput(key: Key) | PutInput(key: Key, value: Value) | NoopInput
  datatype Output = GetOutput(value: Value) | PutOutput | NoopOutput

  // State machine
  datatype Variables = Variables(smap: StampedMapMod.StampedMap)

  function InitState() : Variables {
    Variables(StampedMapMod.Empty())
  }

  predicate Query(v: Variables, v': Variables, key: Key, value: Value)
  {
    && value == v.smap.mi[key].value
    && v' == v
  }

  predicate Put(v: Variables, v': Variables, key: Key, value: Value)
  {
    && v' == v.(smap := v.smap.Put(key, Define(value)))
  }

  // TODO JNF
  predicate Next(v: Variables, v': Variables, input: Input, out: Output)
  {
    || (
        && input.GetInput?
        && out.GetOutput?
        && Query(v, v', input.key, out.value)
       )
    || (
        && input.PutInput?
        && out.PutOutput?
        && Put(v, v', input.key, input.value)
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
