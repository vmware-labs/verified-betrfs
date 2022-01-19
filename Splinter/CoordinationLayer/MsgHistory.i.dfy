// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause
include "../../Spec/Message.s.dfy"
include "../../Spec/StampedMap.s.dfy"

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

  // TODO: Rename the datatype to MsgHistory here to match the module
  // A contiguous sequence of messages from seqStart up to (not including) seqEnd.
  datatype MsgHistory = MsgHistory(msgs: map<LSN, KeyedMessage>, seqStart: LSN, seqEnd: LSN)
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
    function Extend(m: KeyedMessage) : MsgHistory
    {
      MsgHistory(
        map k | k in msgs.Keys + { seqEnd } :: if k == seqEnd then m else msgs[k],
        seqStart,
        seqEnd+1)
    }

    // TODO(jonh): this empty representation is gross. Better to add a datatype constructor
    // that's got no seqStart/seqEnd fields.
    predicate IsEmpty() {
      seqStart == seqEnd
    }

    function Concat(other : MsgHistory) : (result : MsgHistory)
      requires WF()
      requires other.WF()
      requires IsEmpty() || other.CanFollow(seqEnd)
      ensures result.WF()
      ensures result.LSNSet() == LSNSet() + other.LSNSet()
      // conditions on msgSeq bounds
    {
      if IsEmpty()
        then other
      else if other.IsEmpty()
      then this
      else
        MsgHistory( MapDisjointUnion(msgs, other.msgs), seqStart, other.seqEnd)
    }

    predicate CanFollow(lsn: LSN)
    {
      || IsEmpty()
      || seqStart == lsn
    }

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

    // TODO(jonh): rename, because StampedMaps shan't be named that anymore.
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
      IsEmpty() || seqStart <= lsn <= seqEnd
    }

    // TODO(jonh): rename DiscardOld->DiscardOld, DiscardRecent->DiscardRecent
    // Returns every message in this after and including lsn
    function DiscardOld(lsn: LSN) : (r: MsgHistory)
      requires CanDiscardTo(lsn)
      requires WF()
      ensures r.WF()
    {
      if IsEmpty()
      then Empty()
      else if lsn==seqEnd
      then Empty()
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
      if IsEmpty()
      then Empty()
      else if lsn==seqStart
      then Empty()
      else
        var keepMap := map k | seqStart <= k < lsn :: msgs[k];
        MsgHistory(keepMap, seqStart, lsn)
    }

    predicate IncludesSubseq(subseq: MsgHistory)
      requires WF()
      requires subseq.WF()
      ensures IncludesSubseq(subseq) && IsEmpty() ==> subseq.IsEmpty()
    {
      var result := forall lsn | subseq.Contains(lsn) :: Contains(lsn) && msgs[lsn] == subseq.msgs[lsn];
      assert  result && !subseq.IsEmpty() ==> subseq.seqStart in msgs;  // witness to the ensures.
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

  function Empty() : (result: MsgHistory)
    ensures result.WF()
  {
    MsgHistory(map[], 0, 0)
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
