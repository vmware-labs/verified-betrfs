// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PagedJournal.i.dfy"

// The plan is something that refines to a TruncatedJournal.

module LinkedJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod

  import PagedJournalIfc = PagedJournal // TODO(jonh): crack out ifc

  type Pointer(==,!new)

  datatype CacheView = CacheView(entries: map<Pointer, JournalRecord>) {
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

  datatype JournalRecord = JournalRecord(
    messageSeq: MsgHistory,
    priorRec: Option<Pointer>
  )

  datatype TruncatedJournal = TruncatedJournal(
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
  function Mkfs() : (out:PersistentJournal)
  {
    TruncatedJournal(0, None)
  }
}
