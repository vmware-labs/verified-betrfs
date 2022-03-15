// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "StampedMap.i.dfy"
include "MsgHistory.i.dfy"

module JournalLabels {
  import opened MsgHistoryMod
  import opened LSNMod

  datatype TransitionLabel =
      PutLabel(msgs: MsgHistory)
    | DiscardOldLabel(lsn: LSN)
    | InternalLabel()
}

module AbstractJournal {
  import opened Options
  import opened MsgHistoryMod
  import opened LSNMod
  import opened JournalLabels

  // Mkfs is used by CoordinationSystem to define its Init
  function Mkfs() : MsgHistory
  {
    MsgHistoryMod.EmptyHistory
  }

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

  predicate Internal(v: Variables, v': Variables)
  {
    && v' == v
  }

  predicate Init(v: Variables, persistentJournal: MsgHistory)
  {
    v == Variables(persistentJournal)
  }

  predicate Next(v: Variables, v': Variables, lbl: TransitionLabel)
  {
    match lbl {
      case PutLabel(msgs) => Put(v, v', msgs)
      case DiscardOldLabel(lsn) => DiscardOld(v, v', lsn)
      case InternalLabel() => Internal(v, v')
    }
  }
}
