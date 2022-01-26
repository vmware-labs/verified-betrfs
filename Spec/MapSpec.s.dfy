// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/KeyType.s.dfy"
include "../lib/Base/SequencesLite.s.dfy"
include "Message.s.dfy"
include "AtomicStateMachine.s.dfy"
include "CrashTolerant.s.dfy"

module FullKMMapMod {
  import opened ValueMessage
  import opened KeyType
  // Defines a fully-populated Key-Message imap

  predicate AnyKey<K>(k: K) { true }
  predicate Defined(kvm: imap<Key, Message>, k: Key) {
    k in kvm && kvm[k].Define?
  }
  predicate KMMapIsFull(kvm: imap<Key, Message>) {
    forall k | AnyKey(k) :: Defined(kvm, k)
  }
  function EmptyKMMap() : imap<Key, Message>
    ensures KMMapIsFull(EmptyKMMap())
  {
    imap k | AnyKey(k) :: DefaultMessage()
  }

  // Dafny demands a compilable witness for FullKMMap, but also doesn't
  // compile imaps. Lucky we're in a .s file so I can just lie with an
  // axiom. This makes me feel uncomfortable.
  function method Witness() : imap<Key,Message> ensures Witness() == EmptyKMMap()
  type FullKMMap = ikv: imap<Key,Message> | KMMapIsFull(ikv) witness Witness()
}

module MapSpecMod refines AtomicStateMachineMod {
  import opened ValueMessage
  import opened KeyType
  import opened FullKMMapMod

  // UI
  datatype Input = GetInput(key: Key) | PutInput(key: Key, value: Value) | NoopInput
  datatype Output = GetOutput(value: Value) | PutOutput | NoopOutput

  // State machine
  datatype Variables = Variables(kmmap: FullKMMap)

  function InitState() : Variables {
    Variables(EmptyKMMap())
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
