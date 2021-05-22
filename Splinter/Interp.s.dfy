// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Lang/NativeTypes.s.dfy"
include "Message.s.dfy"

// Basic template for defining Interpretations
// XXX --- QUESITON: Why don't JournalInterp and BetreeInterp not use this module?
module InterpMod {
  import opened MessageMod

  type LSN = nat // Log sequence number

  datatype Interp = Interp(mi:imap<Key, Value>, seqEnd: LSN)
  {
    predicate WF() {
      // TODO How is ImapComplete not in Maps.i?
      forall k :: k in mi
    }

    // The effect of a put
    function Put(key: Key, value: Value) : Interp
    {
      Interp(mi[key := value], seqEnd + 1)
    }
  }

  predicate InDomain(k: Key) { true }

  function Empty() : Interp
    ensures Empty().WF()
  {
    Interp(imap k | InDomain(k) :: DefaultValue(), 0)
  }

}
