// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PagedJournalIfc.i.dfy"

// The plan is something that refines to a TruncatedJournal.

module LinkedJournal refines PagedJournalIfc {
  import PagedJournalIfc

  type Pointer(==,!new)

  datatype CacheView = CacheView(entries: map<Pointer, JournalRecordType>) {
    function I(pointer: Pointer, used: set<Pointer>) : Option<JournalRecord>
      decreases entries.Keys - used, 0
    {
      if pointer in used
      then None // Pointer cycle; fail.
      else if pointer !in entries
      then None
      else
        entries[pointer].CacheI(this, used + {pointer})
    }
  }

  // Kinda refines to PagedJournal.JournalRecord
  datatype JournalRecordType = JournalRecordType(
    messageSeq: MsgHistory,
    priorRec: Option<Pointer>
  )
  {
    function CacheI(cacheView: CacheView, used: set<Pointer>) : Option<JournalRecord>
      decreases cacheView.entries.Keys - used, 1
    {
      Some(JournalRecord(messageSeq,
        if priorRec.None? then None
        else cacheView.I(priorRec.value, used)))
    }
  }

  datatype TruncatedJournalType = TruncatedJournalType(
    boundaryLSN : LSN,  // exclusive: lsns <= boundaryLSN are discarded
    freshestRec: Option<Pointer>,
    cacheView: CacheView)
  {
    function I() : TruncatedJournal
    {
      TruncatedJournal(boundaryLSN,
        if freshestRec.None? then None
        else cacheView.I(freshestRec.value, {}))
    }
  }

  // implementation of JournalIfc obligations
  function Mkfs() : (out:TruncatedJournalType)
  {
    TruncatedJournalType(0, None, CacheView(map[]))
  }

  predicate JR_WF(self: JournalRecordType)
  {
    && self.messageSeq.WF()
  }

  predicate TJ_WF(self: TruncatedJournalType)
  {
    && self.I().BuildReceiptTJ().TJValid()
  }

  function TJ_I(self: TruncatedJournalType) : (out: TruncatedJournal)
    //requires TJ_WF(self)
    //ensures out.WF()
  {
    self.I()
  }

  function TJ_EmptyAt(lsn: LSN) : (out:TruncatedJournalType)
    //ensures TJ_WF(out)
    //ensures TJ_I(out).I().EmptyHistory?
    //ensures TJ_I(out).boundaryLSN == lsn
    //ensures TJ_I(out).freshestRec.None?
  {
    // TODO(jonh): Just making up CacheViews seems like trouble for lower in the stack.
    TruncatedJournalType(lsn, None, CacheView(map[]))
  }

  function TJ_DiscardOld(self: TruncatedJournalType, lsn: LSN) : (out:TruncatedJournalType)
    //requires TJ_WF(self)
    //requires TJ_I(self).I().CanDiscardTo(lsn)
    //ensures TJ_WF(out)
    //ensures TJ_I(out) == TJ_I(self).DiscardOld(lsn)
  {
    var out := TruncatedJournalType(lsn, self.freshestRec, self.cacheView);

    assert self.freshestRec.Some? ==> self.cacheView.I(self.freshestRec.value, {}) == out.cacheView.I(out.freshestRec.value, {});

    assert out.I() == self.I().DiscardOldDefn(lsn) by {
      if self.I().freshestRec.None? {
        assert out.I() == TruncatedJournal(lsn, None);
      } else if lsn == self.I().freshestRec.value.messageSeq.seqEnd {
        //DiscardOldDefn demands too much. What we need is the ability
        // to first discard by adjusting the boundaryLSN, then
        // discard irrelevant records and get equivalence. So DiscardOld
        // isn't a function, it's a predicate. There are lots of valid
        // representations of the same discarded thing.
        assert out.I() == TruncatedJournal(lsn, None);
      } else {
        assert out.I() == TruncatedJournal(lsn, self.I().freshestRec);
      }
    }
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
