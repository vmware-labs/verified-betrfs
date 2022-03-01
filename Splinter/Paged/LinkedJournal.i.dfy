// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PagedJournalIfc.i.dfy"

// The plan is something that refines to a TruncatedJournal.

module LinkedJournal refines PagedJournalIfc {
  import PagedJournalIfc

  type Pointer(==,!new)

  datatype CacheView = CacheView(entries: map<Pointer, JournalRecordType>) {
    function I(opointer: Option<Pointer>, used: set<Pointer>) : Option<PagedJournalIfc.JournalRecord>
      decreases entries.Keys - used
    {
      if opointer.None?
      then None
      else
      var pointer := opointer.value;
      if pointer in used
      then None // Pointer cycle; fail.
      else if pointer !in entries
      then None
      else
        var entry := entries[pointer];
        Some(PagedJournalIfc.JournalRecord(entry.messageSeq, I(entry.priorRec, used + {pointer})))
    }
  }

  // Kinda refines to PagedJournal.JournalRecord
  datatype JournalRecordType = JournalRecordType(
    messageSeq: MsgHistory,
    priorRec: Option<Pointer>
  )

  datatype TruncatedJournalType = TruncatedJournalType(
    boundaryLSN : LSN,  // exclusive: lsns <= boundaryLSN are discarded
    freshestRec: Option<Pointer>,
    cacheView: CacheView)
  {
    function I() : PagedJournalIfc.TruncatedJournal
    {
      PagedJournalIfc.TruncatedJournal(boundaryLSN, cacheView.I(freshestRec, {}))
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

  function JR_I(self: JournalRecordType) : JournalRecord
    //requires JR_WF(self)

  predicate TJ_WF(self: TruncatedJournalType)

  function TJ_I(self: TruncatedJournalType) : (out: TruncatedJournal)
    //requires TJ_WF(self)
    //ensures out.WF()

  function TJ_EmptyAt(lsn: LSN) : (out:TruncatedJournalType)
    //ensures TJ_WF(out)
    //ensures TJ_WF(out)
    //ensures TJ_I(out).I().EmptyHistory?
    //ensures TJ_I(out).boundaryLSN == lsn
    //ensures TJ_I(out).freshestRec.None?

  function TJ_DiscardOld(self: TruncatedJournalType, lsn: LSN) : (out:TruncatedJournalType)
    //requires TJ_WF(self)
    //requires TJ_I(self).I().CanDiscardTo(lsn)
    //ensures TJ_WF(out)
    //ensures TJ_I(out) == TJ_I(self).DiscardOld(lsn)

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
