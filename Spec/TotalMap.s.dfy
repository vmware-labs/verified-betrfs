// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/KeyType.s.dfy"
include "Message.s.dfy"

// TODO(jonh): Rename to TotalKVMMap
abstract module TotalMapMod {
  type K(!new, ==)
  type V(!new, ==)
  predicate TerminalValue(v: V) // enables exclusion of values that don't terminate (like Updates)
  function DefaultV() : V // "empty" value
    ensures TerminalValue(DefaultV())

  // For triggering syntax
  predicate AnyKey(k: K) { true }

  predicate Defined(kvm: imap<K, V>, k: K) {
    k in kvm && TerminalValue(kvm[k])
  }

  predicate TotalMapIsFull(kvm: imap<K, V>) {
    forall k | AnyKey(k) :: Defined(kvm, k)
  }

  function EmptyTotalMap() : imap<K, V>
    ensures TotalMapIsFull(EmptyTotalMap())
  {
    imap k | AnyKey(k) :: DefaultV()
  }

  function method Witness() : imap<K,V> ensures Witness() == EmptyTotalMap()
  type TotalMap = ikv: imap<K,V> | TotalMapIsFull(ikv) witness Witness()
}
