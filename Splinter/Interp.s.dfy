// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Base/KeyType.s.dfy"
include "Message.s.dfy"

// Basic template for defining map Interpretations
module InterpMod {
  import opened ValueMessage
  import opened KeyType


  type LSN = nat // Log sequence number

  // Provide a Triggerable symbol for the quantifier
  predicate AnyKey(k: Key) { true }

  datatype Interp = Interp(mi: imap<Key, Message>, seqEnd: LSN)
  {
    predicate WF() {
      // TODO How is ImapComplete not in Maps.i?
      // Ensures that all messages are terimal in the interp map (aka not deltas)
      && (forall k | AnyKey(k) :: k in mi && mi[k].Define?)
    }

    // The effect of a put
    function Put(key: Key, value: Message) : (outInterp : Interp)
      requires value.Define?
      requires WF()
      ensures outInterp.WF()
    {
      Interp(mi[key := value], seqEnd + 1)
    }
  }

  function Empty() : Interp
    ensures Empty().WF()
  {
    var out := Interp(imap k | AnyKey(k) :: DefaultMessage(), 0);
    out
  }

}
