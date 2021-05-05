// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Lang/NativeTypes.s.dfy"

// TODO replace this stuff with the real key, value, message definitions

module MessageMod {
  type Key(!new,==)
  type Value(!new)

  //type Message(!new)
  datatype Message = MessagePut(k:Key, v:Value)

  function AllKeys() : iset<Key> {
    iset key:Key | true
  }

  function DefaultValue() : Value
    // TODO
}

module InterpMod {
  import opened MessageMod

  type LSN = nat // Log sequence number

  datatype Interp = Interp(mi:imap<Key, Value>, seqEnd: LSN)
  {
    predicate WF() {
      // TODO How is ImapComplete not in Maps.i?
      forall k :: k in mi
    }
  }

  predicate InDomain(k: Key) { true }

  function Empty() : Interp
    ensures Empty().WF()
  {
    Interp(imap k | InDomain(k) :: DefaultValue(), 0)
  }
  
}

