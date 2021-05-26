// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/Sequences.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../lib/Base/Option.s.dfy"
include "Allocation.i.dfy"
include "Message.s.dfy"
include "Interp.s.dfy"

// QUESTION: Helper module that contains what exactly?
module MsgSeqMod {
  import opened Sequences
  import opened Maps
  import opened Options
  import opened MessageMod
  import opened InterpMod

  datatype MsgSeq = MsgSeq(msgs: map<LSN, Message>, seqStart: LSN, seqEnd: LSN)
    // seqEnd is exclusive
  {
    predicate Contains(lsn: LSN)
    {
      seqStart <= lsn < seqEnd
    }

    // For use in map comprehensions, where "lsn in msgSeq.Contains()" doesn't
    // satisfy Dafny's bounded set heuristic.
    function {:opaque} LSNSet() : (lsns: set<LSN>)
      ensures forall lsn :: lsn in lsns <==> seqStart <= lsn < seqEnd
    {
      set lsn | seqStart <= lsn < seqEnd
    }

    function Len() : nat
      requires WF()
    {
      seqEnd - seqStart
    }

    predicate WF()
    {
      && seqStart <= seqEnd
      && (seqStart==seqEnd ==> seqStart==0) // normalize Empty.
      && (forall k :: k in msgs <==> Contains(k))
    }

    // Add a single message to the end of the sequence. It gets LSN 'seqEnd', since
    // that's exclusive (points at the next empty slot).
    function Extend(m: Message) : MsgSeq
    {
      MsgSeq(
        map k | k in msgs.Keys + { seqEnd } :: if k == seqEnd then m else msgs[k],
        seqStart,
        seqEnd+1)
    }

    function Concat(other : MsgSeq) : (result : MsgSeq)
      requires WF()
      requires other.WF()
      requires other.Len() == 0 || Len() == 0 ||  other.seqStart == seqEnd
      ensures result.WF()
      // conditions on msgSeq bounds
      ensures result.Len() > 0 ==> result.seqStart == seqStart
      ensures result.Len() > 0 ==> result.seqEnd == other.seqEnd
      ensures Len() == 0 ==> result.seqStart == other.seqStart
      ensures other.Len() == 0 ==> result.seqEnd == seqEnd
    {
        MsgSeq(
          MapDisjointUnion(msgs, other.msgs),
          seqStart,
          other.seqEnd)
    }

    predicate IsEmpty() {
      seqStart == seqEnd
    }

    function ApplyToInterpRecursive(orig: Interp, count: nat) : (out: Interp)
      requires WF()
      requires orig.WF()
      requires count <= Len()
      ensures out.WF()
    {
      if count==0
      then orig
      else
        var lsn := seqStart + count - 1;
        var key := msgs[lsn].k;
        var oldMessage := orig.mi[key];
        var newMessage := msgs[lsn];

        var mapp := ApplyToInterpRecursive(orig, count-1).mi[key := Combine(oldMessage, newMessage)];
        Interp(mapp, lsn)
    }

    function ApplyToInterp(orig: Interp) : Interp
      requires WF()
      requires orig.WF()
    {
      ApplyToInterpRecursive(orig, Len())
    }

    function Truncate(lsn: LSN) : (r: MsgSeq)
      requires seqStart <= lsn < seqEnd
      requires WF()
      ensures r.WF()
      ensures r.seqEnd < lsn
    {
      var keepVersions := lsn - seqStart;
      var trucMap := map k | seqStart <= k < lsn :: msgs[k];
      MsgSeq(trucMap, seqStart, lsn)
    }
  }

  function Empty() : (result: MsgSeq)
    ensures result.WF()
  {
    MsgSeq(map[], 0, 0)
  }


  // QUESTION: Is this supposed to return messages, cuz i changed it to
  function IKey(key:Key, baseValue: Message, ms: MsgSeq) : Message
    requires ms.WF()
    // Gaah look up existing message delta definitions. For
    // replacement/deletion messages, returns the value in the most-recent
    // message matching key else baseValue.

  function Condense(m0: MsgSeq, m1: MsgSeq) : (mo: Option<MsgSeq>)
    ensures mo.Some? ==> mo.value.WF()
  {
    if !m0.WF() || !m1.WF()
      then None   // Bonkers inputs
    else if m0.IsEmpty()
      then Some(m1)
    else if m1.IsEmpty()
      then Some(m0)
    else if m0.seqEnd == m1.seqStart
      then Some(MsgSeq(MapDisjointUnion(m0.msgs, m1.msgs), m0.seqStart, m1.seqEnd))
    else
      None  // Inputs don't stitch
  }

  function CondenseAll(mss: seq<MsgSeq>) : Option<MsgSeq>
  {
    if |mss|==0
    then Some(Empty())
    else
      var prefix := CondenseAll(DropLast(mss));
      if prefix.Some?
      then
        Condense(prefix.value, Last(mss))
      else
        None
  }

  function Concat(interp: Interp, ms:MsgSeq) : Interp
    requires interp.WF()
    requires ms.WF()
    requires interp.seqEnd == ms.seqStart
  {
    Interp(imap k | InDomain(k) :: IKey(k, interp.mi[k], ms), ms.seqEnd)
  }
}
