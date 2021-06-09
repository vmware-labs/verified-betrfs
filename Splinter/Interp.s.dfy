// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Lang/NativeTypes.s.dfy"
include "Message.s.dfy"

// Basic template for defining map Interpretations
module InterpMod {
  import opened MessageMod

  type LSN = nat // Log sequence number

  datatype Interp = Interp(mi: imap<Key, Message>, seqEnd: LSN)
  {
    predicate WF() {
      // TODO How is ImapComplete not in Maps.i?
      && (forall k :: k in mi)
      // && forall k :: mi[k].TerminalMessage?  -- all messages are values
    }

    // The effect of a put
    function Put(key: Key, value: Message) : Interp
      // requires value.TerminalMessage?  // TODO Interps work with values
    {
      Interp(mi[key := value], seqEnd + 1)
    }
  }

  predicate InDomain(k: Key) { true }

  function Empty() : Interp
    ensures Empty().WF()
  {
    Interp(imap k | InDomain(k) :: MessagePut(k, DefaultValue()) , 0)
  }

}
