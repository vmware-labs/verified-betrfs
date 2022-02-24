// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PagedJournalIfc.i.dfy"

module PagedJournal(pages: PagedJournalIfc) refines JournalIfc {
  import opened Sequences
  import opened PagedJournalIfc

  // This PagedJournal module constructs a journal out of a chain of page-sized
  // journal records.
  //
  // It satisfyies JournalIfc, so it can enjoy the PagedSystemRefinement result.

  type PersistentJournal = pages.TruncatedJournalType

  /////////////////////////////////////////////////////////////////////////////
  // EphemeralJournal is an TruncatedJournal with an extra unmarshalledTail
  // field to represent entries we have collected in memory but not marhsalled
  // into a JournalRecord yet.

  datatype EphemeralJournal = EphemeralJournal(
    truncatedJournal: TruncatedJournalType,
    unmarshalledTail: MsgHistory
  )
  {
    function tji() : TruncatedJournal
      requires TJ_WF(truncatedJournal)
    {
      TJ_I(truncatedJournal)
    }

    predicate WF() {
      && TJ_WF(truncatedJournal)
      && unmarshalledTail.WF()
      && (unmarshalledTail.MsgHistory? ==>
          tji().I().CanConcat(unmarshalledTail)
         )
    }

    function I() : MsgHistory
      requires WF()
    {
      tji().I().Concat(unmarshalledTail)
    }

    predicate Empty()
      requires TJ_WF(truncatedJournal)
    {
      && tji().freshestRec.None?
      && unmarshalledTail.EmptyHistory?
    }

    function SeqStart() : LSN
      requires WF()
      requires !Empty()
      ensures SeqStart() == I().seqStart
    {
      var out := if tji().freshestRec.Some?
        then tji().boundaryLSN
        else unmarshalledTail.seqStart;
      assert out == I().seqStart by {
        if tji().freshestRec.Some? {
          tji().BuildReceiptTJ().BoundaryLSN();
        }
      }
      out
    }

    function SeqEnd() : LSN
      requires WF()
      requires !Empty()
    {
      if unmarshalledTail.MsgHistory?
      then unmarshalledTail.seqEnd
      else tji().freshestRec.value.messageSeq.seqEnd
    }
  }

  /////////////////////////////////////////////////////////////////////////////
  // implementation of JournalIfc obligations

  predicate PWF(pj: PersistentJournal) {
    TJ_WF(pj)
  }

  predicate EWF(ej: EphemeralJournal) {
    ej.WF()
  }

  function IPJ(pj: PersistentJournal) : (out:MsgHistory) { TJ_I(pj).I() }

  function IEJ(ej: EphemeralJournal) : (out:MsgHistory) { ej.I() }

  function Mkfs() : (out:PersistentJournal)
    //ensures PWF(out)
    //ensures IPJ(out).EmptyHistory?
  {
    TJ_Mkfs()
  }

  function LoadJournal(pj: PersistentJournal) : (out:EphemeralJournal)
    //requires PWF(pj)
    //ensures EWF(out)
    //ensures IEJ(out) == IPJ(pj)
  {
    EphemeralJournal(pj, EmptyHistory)
  }

  function PJournalSeqEnd(pj: PersistentJournal) : Option<LSN>
    // ensures out.Some? == IPJ(pj).MsgHistory?
  {
    // TODO(jonh): export to interface to avoid calls through TJ_I?
    if
      || TJ_I(pj).freshestRec.None?
      || TJ_I(pj).boundaryLSN == TJ_I(pj).freshestRec.value.messageSeq.seqEnd
    then None
    else Some(TJ_I(pj).freshestRec.value.messageSeq.seqEnd)
  }

  predicate JournalIncludesSubseq(ej: EphemeralJournal, msgs: MsgHistory)
    //requires EWF(ej)
    //requires msgs.WF()
  {
    // subseq appears in committed pages
    // TODO(jonh): export to interface to avoid calls through TJ_I?
    var out := (exists i :: ej.tji().IncludesSubseqAt(msgs, i));
    assert out ==> IEJ(ej).IncludesSubseq(msgs) by {
      if out {
        var i :| ej.tji().IncludesSubseqAt(msgs, i);
        ej.tji().SubseqOfEntireInterpretation(msgs, i);
      }
    }
    out
    // We don't bother allowing you to "find" the msgs in unmarshalledTail,
    // since the includes operation is only relevant during recovery time,
    // during which we don't allow the unmarshalledTail.
    // (I mean, we COULD allow Puts during that time, but why bother?)
  }

  function EJournalSeqEnd(ej: EphemeralJournal) : Option<LSN>
  {
    // TODO(jonh): export to interface to avoid calls through TJ_I?
    if ej.unmarshalledTail.MsgHistory?
    then Some(ej.unmarshalledTail.seqEnd)
    else PJournalSeqEnd(ej.truncatedJournal)
  }

  function JournalConcat(ej: EphemeralJournal, msgs: MsgHistory) : (out:EphemeralJournal)
    //requires EWF(ej)
    //requires msgs.WF()
    //requires msgs.EmptyHistory? || EJournalSeqEnd(ej).None? || msgs.CanFollow(EJournalSeqEnd(ej).value)
    // ensures EWF(out)
    // ensures IEJ(ej).Concat(msgs) == IEJ(out)
  {
    EphemeralJournal(ej.truncatedJournal, ej.unmarshalledTail.Concat(msgs))
  }

  predicate CanDiscardOld(ej: EphemeralJournal, lsn: LSN)
  {
    if ej.Empty() then true
    else ej.SeqStart() <= lsn <= ej.SeqEnd()
  }

  function DiscardOld(ej: EphemeralJournal, lsn: LSN) : EphemeralJournal
    // requires EWF(ej)
    // requires CanDiscardOld(ej, lsn)
  {
    if ej.unmarshalledTail.MsgHistory? && ej.unmarshalledTail.seqStart <= lsn
    then
      EphemeralJournal(Mkfs(), ej.unmarshalledTail.DiscardOld(lsn))
    else
      EphemeralJournal(TJ_DiscardOld(ej.truncatedJournal, lsn), ej.unmarshalledTail)
  }

  predicate JournalCanFreezeAt(ej: EphemeralJournal, startLsn: LSN, endLsn: LSN, i: nat)
    requires ej.WF()
  {
    // Can't freeze anything in unmarshalledTail yet!
    && var tj := ej.tji();
    // Anything we freeze must start no later than journal is already truncated.
    && tj.boundaryLSN <= startLsn
    // And must end at an existing page boundary.
    // (In lower layers, that page and those before it must also be clean on disk.)
    && var receipt := tj.BuildReceiptTJ();
    && i < |receipt.lines|
    && assert receipt.lines[i].journalRec.messageSeq.MsgHistory? by { receipt.JournalRecsAllWF(); }
    && endLsn == receipt.lines[i].journalRec.messageSeq.seqEnd
    && startLsn <= endLsn
  }

  predicate JournalCanFreezeInternal(ej: EphemeralJournal, startLsn: LSN, endLsn: LSN)
    requires EWF(ej)
  {
    || startLsn==endLsn // can always freeze to empty
    || (exists i :: JournalCanFreezeAt(ej, startLsn, endLsn, i))
  }

  lemma JournalFreezeLemma(ej: EphemeralJournal, startLsn: LSN, endLsn: LSN)
    requires EWF(ej)
    ensures JournalCanFreezeInternal(ej, startLsn, endLsn) && startLsn < endLsn ==>
      IEJ(ej).CanDiscardTo(startLsn) && IEJ(ej).CanDiscardTo(endLsn)
  {
    if JournalCanFreezeInternal(ej, startLsn, endLsn) && startLsn < endLsn {
      var i:nat :| JournalCanFreezeAt(ej, startLsn, endLsn, i);
      var tj := ej.tji();

      // endLsn-1 is in the interp, so we can discard to endLsn
      var receipt := tj.BuildReceiptTJ();
      receipt.TJFacts();
      tj.SubseqOfEntireInterpretation(receipt.MessageSeqAt(i), i);
      assert receipt.MessageSeqAt(i).Contains(endLsn-1);  // trigger

      // startLsn is in the interp, so we can discard to it
      tj.LsnBelongs(startLsn);
    }
  }

  predicate JournalCanFreeze(ej: EphemeralJournal, startLsn: LSN, endLsn: LSN)
  {
    JournalFreezeLemma(ej, startLsn, endLsn);
    JournalCanFreezeInternal(ej, startLsn, endLsn)
  }

  function JournalFreeze(ej: EphemeralJournal, startLsn: LSN, endLsn: LSN) : PersistentJournal
    // requires EWF(ej);
    // requires JournalCanFreeze(ej, startLsn, endLsn)
    // ensures PWF(out)
    // ensures IPJ(out) == IEJ(ej).DiscardOld(startLsn).DiscardRecent(endLsn)
  {
    JournalFreezeLemma(ej, startLsn, endLsn);
    if startLsn==endLsn
    then
      var out := TJ_EmptyAt(startLsn);
      out
    else
      var tj := ej.tji();
      var receipt := tj.BuildReceiptTJ();
      var i:nat :| JournalCanFreezeAt(ej, startLsn, endLsn, i);

      var discardRecent := TJ_DiscardRecent(ej.truncatedJournal, i);
      receipt.AbbreviatedReceiptTJValid(i, endLsn, TJ_I(discardRecent));
      var out := TJ_DiscardOld(discardRecent, startLsn);
      out
  }

  // TODO(jonh): internal operation to truncate old journal garbage
  // Actually I think this only happens in the refinement. At this layer, the receipt just
  // stops when it gets to the end.

  // A prefix of the unmarshalled tail can be carted off as a new page-sized journal record
  function JournalMarshal(ej: EphemeralJournal, cut: LSN) : (out: EphemeralJournal)
    requires EWF(ej)
    requires ej.unmarshalledTail.MsgHistory?
    requires ej.unmarshalledTail.seqStart < cut // Can't marshall nothing.
    requires ej.unmarshalledTail.CanDiscardTo(cut)
    ensures EWF(out)
    ensures IEJ(out) == IEJ(ej)
  {
    var marshalledMsgs := ej.unmarshalledTail.DiscardRecent(cut);
    var tj := TJ_AppendRecord(ej.truncatedJournal, marshalledMsgs);

    // The new unmarshalled tail is what's left after the cut
    var out := EphemeralJournal(tj, ej.unmarshalledTail.DiscardOld(cut));
    out
  }
}
