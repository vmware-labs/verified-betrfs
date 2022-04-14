// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/KeyType.s.dfy"
include "../lib/Base/SequencesLite.s.dfy"
include "TotalKMMap.s.dfy"
include "AtomicStateMachine.s.dfy"
include "CrashTolerant.s.dfy"

module MapSpecMod refines AtomicStateMachineMod {
  import opened ValueMessage
  import opened KeyType
  import opened TotalKMMapMod

  // UI
  // TODO(jonh): I don't think we need Noops at this layer; we get them from Async & above anyway.
  datatype Input = GetInput(key: Key) | PutInput(key: Key, value: Value) | NoopInput
  datatype Output = GetOutput(value: Value) | PutOutput | NoopOutput

  // State machine
  datatype Variables = Variables(kmmap: TotalKMMap)

  function InitState() : Variables {
    Variables(EmptyTotalMap())
  }

  predicate Query(v: Variables, v': Variables, key: Key, value: Value)
  {
    && assert AnyKey(key);
    && value == v.kmmap[key].value
    && v' == v
  }

  predicate Put(v: Variables, v': Variables, key: Key, value: Value)
  {
    && v' == v.(kmmap := v.kmmap[key := Define(value)])
  }

  predicate Next(v: Variables, v': Variables, input: Input, out: Output)
  {
    match input {
      case GetInput(key) =>
        && out.GetOutput?
        && Query(v, v', key, out.value)
      case PutInput(key, value) =>
        && out.PutOutput?
        && Put(v, v', key, value)
      case NoopInput =>
        && out.NoopOutput?
        && v' == v
    }
  }
}

module CrashTolerantMapSpecMod refines CrashTolerantMod(MapSpecMod) {
}
