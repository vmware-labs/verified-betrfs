// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Lang/NativeTypes.s.dfy"
//include "../lib/Base/total_order_impl.i.dfy"

// TODO replace this stuff with the real key, value, message definitions

// Messages are high-level Ops over the Betree
module MessageMod {

  //import KeysImpl = Lexicographic_Byte_Order_Impl
  //import Keys = KeysImpl.Ord

  //type Key(!new) //= Keys.Element
  type Key(!new,==) // TODO(sowmya): Message shouldn't have key, I think
  type Value(!new)

  //type Message(!new)
  // TODO: Make Messages be more general either terminal updates or
  datatype Message = MessagePut(v:Value)

  predicate IsAKey(k: Key) { true }  // a term for Dafny to trigger on, to hide the warning.

  function AllKeys() : iset<Key> {
    iset key:Key | IsAKey(key)
  }

  function DefaultValue() : Value
    // TODO

  function DefaultMessage() : Message
  {
    MessagePut(DefaultValue())
  }

  // QUESTION: We use this to apply the key to map in msgSeq. Does this go here?
  function Combine(oldMsg : Message, newMsg: Message) : Message
   // TODO
}
