// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Lang/NativeTypes.s.dfy"

// TODO replace this stuff with the real key, value, message definitions

// Messages are high-level Ops over the Betree
module MessageMod {
  type Key(!new,==) // TODO(sowmya): Message shouldn't have key, I think
  type Value(!new)

  //type Message(!new)
  datatype Message = MessagePut(k:Key, v:Value)

  predicate IsAKey(k: Key) { true }  // a term for Dafny to trigger on, to hide the warning.

  function AllKeys() : iset<Key> {
    iset key:Key | IsAKey(key)
  }

  function DefaultValue() : Value
    // TODO

  // QUESTION: We use this to apply the key to map in msgSeq. Does this go here?
  function Combine(oldMsg : Message, newMsg: Message) : Message
   // TODO
}
