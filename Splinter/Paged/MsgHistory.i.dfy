// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
include "../../Spec/Message.s.dfy"
include "StampedMap.i.dfy"

include "../../lib/Base/Sequences.i.dfy"
include "../../lib/Base/Maps.i.dfy"
include "../../lib/Base/Option.s.dfy"
include "../../lib/Base/KeyType.s.dfy"


// A MsgHistory is a contiguous sequence of LSN-stamped key-message pairs.
// A MsgHistory can be applied to a StampedMap (if the LSNs line up) to get a
// new StampedMap reflecting the updates from the MsgHistory.
module MsgHistoryMod {
  import opened Sequences
  import opened Maps
  import opened Options
  import opened ValueMessage
  import opened KeyType
  import opened TotalKMMapMod
  import opened LSNMod
  import opened StampedMapMod

  datatype KeyedMessage = KeyedMessage(key: Key, message: Message)

  // A contiguous sequence of messages from seqStart up to (not including) seqEnd.
  datatype MsgHistory = EmptyHistory | MsgHistory(msgs: map<LSN, KeyedMessage>, seqStart: LSN, seqEnd: LSN)
    // seqEnd is exclusive
  {
    predicate WF()
    {
      MsgHistory? ==> (
      // Note that MsgHistory() instances CANNOT be empty, so that empty repr is normalized.
        && seqStart < seqEnd
        && ContainsExactly(msgs.Keys)
      )
    }

    predicate ContainsExactly(lsns: set<LSN>)
    {
      forall lsn :: lsn in lsns <==> Contains(lsn)
    }

    predicate Contains(lsn: LSN)
    {
      && !EmptyHistory?
      && seqStart <= lsn < seqEnd
    }

    // For use in map comprehensions, where "lsn in msgSeq.Contains()" doesn't
    // satisfy Dafny's bounded set heuristic.
    function {:opaque} LSNSet() : set<LSN>
      ensures ContainsExactly(LSNSet())
    {
      if EmptyHistory?
      then {}
      else set lsn | seqStart <= lsn < seqEnd
    }

    function Len() : nat
      requires WF()
    {
      if EmptyHistory?
      then 0
      else seqEnd - seqStart
    }

    predicate CanConcat(other: MsgHistory)
      requires WF()
      requires other.WF()
    {
      EmptyHistory? || other.CanFollow(seqEnd)
    }

    function Concat(other: MsgHistory) : (result : MsgHistory)
      requires WF()
      requires other.WF()
      requires CanConcat(other)
      ensures result.WF()
      ensures result.LSNSet() == LSNSet() + other.LSNSet()
      // conditions on msgSeq bounds
    {
      if EmptyHistory?
        then other
      else if other.EmptyHistory?
      then this
      else
        MsgHistory( MapDisjointUnion(msgs, other.msgs), seqStart, other.seqEnd)
    }

    predicate CanFollow(lsn: LSN)
    {
      || EmptyHistory?
      || seqStart == lsn
    }

    // Where does this journal end if it's concatenated to a map for lsn?
    function SeqEndFor(lsn: LSN) : LSN
    {
        if EmptyHistory? then lsn else seqEnd
    }

    function ApplyToStampedMap(orig: StampedMap) : (out: StampedMap)
      requires WF()
      requires CanFollow(orig.seqEnd)
      ensures out.seqEnd == orig.seqEnd + Len()
      decreases Len()
    {
      if EmptyHistory?
      then orig
      else
        var lastLsn := seqEnd - 1;
        var subMap := DiscardRecent(lastLsn).ApplyToStampedMap(orig);
        var key := msgs[lastLsn].key;
        var newMessage := msgs[lastLsn].message;
        assert AnyKey(key);
        var oldMessage := subMap.mi[key];
        StampedMap(subMap.mi[key := Merge(newMessage, oldMessage)], subMap.seqEnd+1)
    }

    predicate CanDiscardTo(lsn: LSN)
    {
      // NB Pruning allows one more LSN than Contains, because you can
      // DiscardOld all the way to seqEnd (and get an empty) (or DiscardRecent all
      // the way to seqStart).
      EmptyHistory? || seqStart <= lsn <= seqEnd
    }

    // Returns every message in this after and including lsn
    function DiscardOld(lsn: LSN) : (r: MsgHistory)
      requires WF()
      requires CanDiscardTo(lsn)
      ensures r.WF()
    {
      if EmptyHistory? || lsn==seqEnd
      then EmptyHistory
      else
        var keepMap := map k | lsn <= k < seqEnd :: msgs[k];
        MsgHistory(keepMap, lsn, seqEnd)
    }

    // Returns every message in this up to but not including lsn.
    function DiscardRecent(lsn: LSN) : (r: MsgHistory)
      requires CanDiscardTo(lsn)
      requires WF()
      ensures r.WF()
    {
      if EmptyHistory? || lsn==seqStart
      then EmptyHistory
      else
        var keepMap := map k | seqStart <= k < lsn :: msgs[k];
        MsgHistory(keepMap, seqStart, lsn)
    }

    predicate IncludesSubseq(subseq: MsgHistory)
      requires WF()
      requires subseq.WF()
      ensures IncludesSubseq(subseq) && EmptyHistory? ==> subseq.EmptyHistory?
    {
      var result := forall lsn | subseq.Contains(lsn) :: Contains(lsn) && msgs[lsn] == subseq.msgs[lsn];
      assert result && subseq.MsgHistory? ==> Contains(subseq.seqStart);  // seqStart is witness to contradiction
      result
    }
  }

  function Singleton(lsn: LSN, msg: KeyedMessage) : MsgHistory
  {
    MsgHistory(map [lsn := msg], lsn, lsn+1)
  }

  // Wrapper reverses argument list to make "history algebra" easier to read.
  // We might have preferred to write something more infix, like:
  //   stampedMap.Apply(history)
  // ...but stampedMap is trusted (.s); we don't want it to know about the
  // verified (i.) MsgHistory type.
  function MapPlusHistory(stampedMap: StampedMap, history: MsgHistory) : StampedMap
    requires history.WF()
    requires history.CanFollow(stampedMap.seqEnd)
  {
    history.ApplyToStampedMap(stampedMap)
  }
}