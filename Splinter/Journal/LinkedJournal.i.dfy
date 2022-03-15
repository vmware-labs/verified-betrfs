// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../CoordinationLayer/AbstractJournal.i.dfy"

module LinkedJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened Sequences
  import PagedJournal

  datatype CacheView = CacheView(entries: map<Pointer, JournalRecord>) {
    function I(boundaryLSN: LSN, pointer: Pointer, used: set<Pointer>) : Option<PagedJournal.JournalRecord>
      decreases entries.Keys - used, 0
    {
      if pointer in used
      then None // Pointer cycle; fail.
      else if pointer !in entries
      then None
      else
        Some(entries[pointer].CacheI(boundaryLSN, this, used + {pointer}))
    }
  }

  datatype JournalRecord = JournalRecord(
    messageSeq: MsgHistory,
    priorRec: Option<Pointer>
  )
  {
    predicate WF()
    {
      messageSeq.WF()
    }
    
    function CacheI(boundaryLSN: LSN, cacheView: CacheView, used: set<Pointer>) : PagedJournal.JournalRecord
      decreases cacheView.entries.Keys - used, 1
    {
      PagedJournal.JournalRecord(messageSeq,
        if messageSeq.seqStart <= boundaryLSN
        then None // no need to advance
        else if priorRec.None?
        then None // nowhere to go
        else cacheView.I(boundaryLSN, priorRec.value, used))
    }
  }

  datatype TruncatedJournal = TruncatedJournal(
    boundaryLSN : LSN,  // exclusive: lsns <= boundaryLSN are discarded
    freshestRec: Option<Pointer>,
    cacheView: CacheView)
  {
    function I() : PagedJournal.TruncatedJournal
    {
      PagedJournal.TruncatedJournal(boundaryLSN,
        if freshestRec.None? then None
        else cacheView.I(boundaryLSN, freshestRec.value, {}))
    }

    predicate WF()
    {
      I()..BuildReceiptTJ().TJValid()
    }
  }

  function Mkfs() : (out:TruncatedJournal)
  {
    // TODO(jonh): Just making up CacheViews seems like trouble for lower in the stack.
    TruncatedJournal(0, None, CacheView(map[]))
  }

  lemma DiscardOldLemma(cacheView: CacheView, oldBoundary: LSN, newBoundary: LSN, pointer: Pointer, used: set<Pointer>)
    requires cacheView.I(oldBoundary, pointer, used).Some?
    requires TruncatedJournal(oldBoundary, cacheView.I(oldBoundary, pointer, used)).WF()
    requires TruncatedJournal(oldBoundary, cacheView.I(oldBoundary, pointer, used)).I().CanDiscardTo(newBoundary)
    ensures TruncatedJournal(oldBoundary, cacheView.I(oldBoundary, pointer, used)).DiscardOld(newBoundary)
      == TruncatedJournal(newBoundary, cacheView.I(newBoundary, pointer, used))
  {
    if pointer in used {
      // Pointer cycle; fail.
      assert TruncatedJournal(oldBoundary, cacheView.I(oldBoundary, pointer, used)).DiscardOld(newBoundary)
        == TruncatedJournal(newBoundary, cacheView.I(newBoundary, pointer, used));
    } else if pointer !in cacheView.entries {
      assert TruncatedJournal(oldBoundary, cacheView.I(oldBoundary, pointer, used)).DiscardOld(newBoundary)
        == TruncatedJournal(newBoundary, cacheView.I(newBoundary, pointer, used));
    } else {
      var entry := cacheView.entries[pointer];
      if entry.messageSeq.seqStart <= oldBoundary {
        /*
        Wait we've already done all this reasoning before.
        *All* we should be doing right now is showing a connection between the
        linked representation and the nested representation.
        The only time they might diverge is if there's a cycle or missing link,
        but those should look exactly like a None.
        So what I really want is a lemma that says:

        cacheView.I(x, pointer, used) == cacheView.I(y, pointer, used)

        hmm, does the CacheView change if the boundary changes?
        What happens in the nested view? Do we stop nesting? No, or yes -- they
        should have the same interpretation.

        Yeah, at the nested level we buildReceipt, then DiscardOld.
        So maybe we shouldn't have plumbed boundaries through the interp!

        So we'd like to argue that
        buildReceipt(cacheView.I(pointer, used)) == buildReceipt(cacheView.I(pointer, used))

        (1) 
        [10 o 20][20 n 30][30   40]

        [10 o 20][20 n 30][30   40]
        */
        // Need to think here
        calc {
          cacheView.I(oldBoundary, pointer, used);
          entry.CacheI(oldBoundary, cacheView, used + {pointer});
          Some(JournalRecord(entry.messageSeq, None));
        }
        calc {
          cacheView.I(newBoundary, pointer, used);
          entry.CacheI(oldBoundary, cacheView, used + {pointer});
          Some(JournalRecord(entry.messageSeq, None));
        }
        assert TruncatedJournal(oldBoundary, cacheView.I(oldBoundary, pointer, used)).freshestRec
          == Some(JournalRecord(entry.messageSeq, None));
        assert TruncatedJournal(oldBoundary, cacheView.I(oldBoundary, pointer, used)).DiscardOld(newBoundary)
          == TruncatedJournal(newBoundary, cacheView.I(newBoundary, pointer, used));
      } else if entry.priorRec.None? {
        assert TruncatedJournal(oldBoundary, cacheView.I(oldBoundary, pointer, used)).DiscardOld(newBoundary)
          == TruncatedJournal(newBoundary, cacheView.I(newBoundary, pointer, used));
      } else {
        // Need a recursive call here
        assume false;
        assert TruncatedJournal(oldBoundary, cacheView.I(oldBoundary, pointer, used)).DiscardOld(newBoundary)
        == TruncatedJournal(newBoundary, cacheView.I(newBoundary, pointer, used));
      }
    }
  }

  datatype Variables = Variables(
    truncatedJournal: TruncatedJournal,
    unmarshalledTail: MsgHistory
  )
  {
    predicate WF() {
      && truncatedJournal.WF()
      && unmarshalledTail.WF()
      && (unmarshalledTail.MsgHistory? ==>
          truncatedJournal.I().CanConcat(unmarshalledTail)
         )
    }
  }

  predicate Put(v: Variables, v': Variables, msgs: MsgHistory)
  {
    && v.WF()
    && v'.WF()
    && msgs.WF()
    && (v.SeqEnd().None? || msgs.EmptyHistory? || msgs.seqStart == v.SeqEnd().value)  // CanFollow, but without interpreting this.
    && v' == v.(unmarshalledTail := v.unmarshalledTail.Concat(msgs))
  }

  predicate DiscardOld(v: Variables, v': Variables, lsn: LSN)
  {
    && v.WF()
    && v'.WF()
    && (if v.Empty() then true else v.SeqStart() <= lsn <= v.SeqEnd().value)
    && (if v.unmarshalledTail.MsgHistory? && v.unmarshalledTail.seqStart <= lsn
        then v' == Variables(Mkfs(), v.unmarshalledTail.DiscardOld(lsn))
        else v' == v.(truncatedJournal := v.truncatedJournal.DiscardOld(lsn))
       )
  }

  predicate JournalMarshal(v: Variables, v': Variables, cut: LSN)
  {
    && v.WF()
    && v'.WF()
    && v.unmarshalledTail.MsgHistory?
    && v.unmarshalledTail.seqStart < cut // Can't marshall nothing.
    && v.unmarshalledTail.CanDiscardTo(cut)
    && var marshalledMsgs := v.unmarshalledTail.DiscardRecent(cut);
    && v' == Variables(
      v.truncatedJournal.AppendRecord(marshalledMsgs),
      v.unmarshalledTail.DiscardOld(cut))
  }

  predicate Init(v: Variables)
  {
    && v == Variables(Mkfs(), EmptyHistory)
  }

  datatype Step =
      PutStep(msgs: MsgHistory)
    | DiscardOldStep(lsn: LSN)
    | JournalMarshalStep(cut: LSN)

  predicate NextStep(v: Variables, v': Variables, step: Step)
  {
    match step {
      case PutStep(msgs) => Put(v, v', msgs)
      case DiscardOldStep(lsn) => DiscardOld(v, v', lsn)
      case JournalMarshalStep(cut) => JournalMarshal(v, v', cut)
    }
  }

  function TJ_DiscardOld(self: TruncatedJournalType, lsn: LSN) : (out:TruncatedJournalType)
    //requires TJ_WF(self)
    //requires TJ_I(self).I().CanDiscardTo(lsn)
    //ensures TJ_WF(out)
    //ensures TJ_I(out) == TJ_I(self).DiscardOld(lsn)
  {
    var out := TruncatedJournalType(lsn, self.freshestRec, self.cacheView);
    assert out.I() == self.I().DiscardOld(lsn);
    assert TJ_WF(out);
    assert TJ_I(out) == TJ_I(self).DiscardOld(lsn);
    out
  }

  function TJ_DiscardRecent(self: TruncatedJournalType, i: nat) : (out:TruncatedJournalType)
    //requires TJ_WF(self)
    //requires TJ_CanDiscardRecentAtLine(self, i)
    //ensures TJ_WF(out)
    //ensures
    //  var receipt := TJ_I(self).BuildReceiptTJ();
    //  TJ_I(out) == TruncatedJournal(TJ_I(self).boundaryLSN, Some(receipt.lines[i].journalRec))

  function TJ_AppendRecord(self: TruncatedJournalType, msgs: MsgHistory) : (out:TruncatedJournalType)
    //requires TJ_WF(self)
    //requires msgs.MsgHistory?
    //requires TJ_I(self).Empty() || msgs.CanFollow(TJ_I(self).SeqEnd())
    //ensures TJ_WF(out)
    //ensures TJ_I(out) == TruncatedJournal(
    //  TJ_AppendNewBoundary(self, msgs),
    //  Some(JournalRecord(msgs, TJ_I(self).freshestRec)))
}
