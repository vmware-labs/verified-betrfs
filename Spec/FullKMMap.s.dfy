// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/KeyType.s.dfy"
include "Message.s.dfy"

// TODO(jonh): Rename to TotalKVMMap
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
