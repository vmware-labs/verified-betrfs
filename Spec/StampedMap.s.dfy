// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Base/KeyType.s.dfy"
include "Message.s.dfy"

// A "StampedMap" is a full imap "stamped" with an LSN that identifies how many
// operations it represents.
module StampedMapMod {
  import opened ValueMessage
  import opened KeyType

  type LSN = nat // Log sequence number

  // Provide a Triggerable symbol for the quantifier
  predicate AnyKey(k: Key) { true }

  datatype RawStampedMap = RawStampedMap(mi: imap<Key, Message>, seqEnd: LSN)
  {
    predicate secretWF() {
      // TODO How is ImapComplete not in Maps.i?
      // Ensures that all messages are terimal in the interp map (aka not deltas)
      && (forall k | AnyKey(k) :: k in mi && mi[k].Define?)
    }

    // The effect of a put
    function Put(key: Key, value: Message) : (outStampedMap : StampedMap)
      requires value.Define?
      requires secretWF()
      ensures outStampedMap.secretWF()
    {
      RawStampedMap(mi[key := value], seqEnd + 1)
    }
  }

  function RawEmpty() : RawStampedMap
  {
    RawStampedMap(imap k | AnyKey(k) :: DefaultMessage(), 0)
  }

  // Dafny demands a compilable witness for RawStampedMap, but also doesn't
  // compile imaps. Lucky we're in a .s file so I can just lie with an
  // axiom. This makes me feel uncomfortable.
  function method Witness() : RawStampedMap
    ensures Witness() == RawEmpty()

  type StampedMap = ri:RawStampedMap | ri.secretWF() witness Witness()

  function Empty() : StampedMap
  {
    RawEmpty()
  }
}
