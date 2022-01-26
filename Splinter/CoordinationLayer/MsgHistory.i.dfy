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
  import StampedMapMod

  type LSN = StampedMapMod.LSN
  type StampedMap = StampedMapMod.StampedMap

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

    function Concat(other : MsgHistory) : (result : MsgHistory)
      requires WF()
      requires other.WF()
      requires EmptyHistory? || other.CanFollow(seqEnd)
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

    // TODO(jonh): Rewrite as DiscardRecent(lsn-1)
    function ApplyToStampedMapRecursive(orig: StampedMap, count: nat) : (out: StampedMap)
      requires WF()
      requires count <= Len()
      requires CanFollow(orig.seqEnd)
      ensures out.seqEnd == orig.seqEnd + count
    {
      if count==0
      then orig
      else
        var subInterp := ApplyToStampedMapRecursive(orig, count-1);

        var lsn := seqStart + count - 1;
        var key := msgs[lsn].key;
        var newMessage := msgs[lsn].message;
        var oldMessage := subInterp.mi[key];

        var mapp := subInterp.mi[key := Merge(newMessage, oldMessage)];
        StampedMapMod.RawStampedMap(mapp, lsn + 1)
    }

    function ApplyToStampedMap(orig: StampedMap) : (out: StampedMap)
      requires WF()
      requires CanFollow(orig.seqEnd)
      ensures out.seqEnd == orig.seqEnd + Len()
    {
      ApplyToStampedMapRecursive(orig, Len())
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
      requires CanDiscardTo(lsn)
      requires WF()
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

  lemma ApplyToStampedMapRecursiveIsDiscardTail(ms: MsgHistory, orig: StampedMap, count: nat)
    requires ms.WF()
    requires count+1 <= ms.Len()
    requires ms.CanFollow(orig.seqEnd)
    ensures ms.ApplyToStampedMapRecursive(orig, count) == ms.DiscardRecent(ms.seqStart + count).ApplyToStampedMapRecursive(orig, count);
    decreases count;
  {
    if 1 < count {
      var msDiscarded := ms.DiscardRecent(ms.seqStart + count);

      ApplyToStampedMapRecursiveIsDiscardTail(ms, orig, count-1);
      assert ms.DiscardRecent(ms.seqStart + count - 1) == msDiscarded.DiscardRecent(msDiscarded.seqStart + count - 1); // trigger
      ApplyToStampedMapRecursiveIsDiscardTail(msDiscarded, orig, count - 1);
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
