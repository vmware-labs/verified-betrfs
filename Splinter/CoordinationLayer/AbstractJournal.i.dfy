// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "StampedMap.i.dfy"
include "MsgHistory.i.dfy"

module AbstractJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod

  datatype Variables = Variables(journal: MsgHistory)
  {
    predicate WF() {
      && journal.WF()
    }

    // Some parial enabling conditions.
    // TODO(jonh) Not yet sure how to set these up for refinement in a
    // non-funky-module-refinement way.
    predicate SeqEndMatches(lsn: LSN) {
      || journal.EmptyHistory?
      || journal.seqEnd == lsn
    }
    
    predicate IncludesSubseq(messages: MsgHistory) {
      && WF()
      && messages.WF()
      && journal.IncludesSubseq(messages)
    }

    predicate CanFreezeAs(startLsn: LSN, endLsn: LSN, frozenJournal: MsgHistory)
    {
      && WF()
      && startLsn <= endLsn
      && journal.CanDiscardTo(startLsn)
      && journal.CanDiscardTo(endLsn)
      && frozenJournal == (if startLsn==endLsn
          then EmptyHistory
          else journal.DiscardOld(startLsn).DiscardRecent(endLsn))
    }
  }

  // Should I do this as a predicate step with no enabling conditions?
  function LoadJournal(persistentJournal: MsgHistory) : Variables
  {
    Variables(persistentJournal)
  }

  predicate Put(v: Variables, v': Variables, messages: MsgHistory)
  {
    && v.WF()
    && messages.WF()
    && v.journal.CanConcat(messages)
    && v' == v.(journal := v.journal.Concat(messages))
  }

  predicate DiscardOld(v: Variables, v': Variables, startLsn: LSN)
  {
    && v.WF()
    && v.journal.CanDiscardTo(startLsn)
    && v'.journal == v.journal.DiscardOld(startLsn)
  }
}
