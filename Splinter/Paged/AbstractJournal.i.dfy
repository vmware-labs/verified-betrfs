// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "JournalIfc.i.dfy"

module AbstractJournal refines JournalIfc {
  type PersistentJournal = MsgHistory
  type EphemeralJournal = MsgHistory

  predicate PWF(pj: PersistentJournal) {
    pj.WF()
  }

  predicate EWF(ej: EphemeralJournal) {
    ej.WF()
  }

  function IPJ(pj: PersistentJournal) : (out:MsgHistory)
  { pj }

  function IEJ(ej: EphemeralJournal) : (out:MsgHistory)
  { ej }

  function Mkfs() : (out:PersistentJournal)
    //ensures PWF(out)
    //ensures IPJ(out).EmptyHistory?
  {
    EmptyHistory
  }

  function LoadJournal(pj: PersistentJournal) : (out:EphemeralJournal)
    //requires PWF(pj)
    //ensures EWF(out)
    //ensures IEJ(out) == IPJ(pj)
  {
    pj
  }

  function PJournalSeqEnd(pj: PersistentJournal) : Option<LSN>
  {
    if pj.MsgHistory? then Some(pj.seqEnd) else None
  }

  predicate JournalIncludesSubseq(ej: EphemeralJournal, msgs: MsgHistory)
    //requires EWF(ej)
    //requires msg.WF()
  {
    ej.IncludesSubseq(msgs)
  }

  function EJournalSeqEnd(ej: EphemeralJournal) : Option<LSN>
  {
    if ej.MsgHistory? then Some(ej.seqEnd) else None
  }

  function JournalConcat(ej: EphemeralJournal, msgs: MsgHistory) : EphemeralJournal
    //requires EWF(ej)
    //requires msg.WF()
    //requires msgs.EmptyHistory? || EJournalSeqEnd(ej).None? || msgs.CanFollow(EJournalSeqEnd(ej).value)
    //ensures EWF(JournalConcat(ej, msgs))
  {
    ej.Concat(msgs)
  }

  predicate CanDiscardOld(ej: EphemeralJournal, lsn: LSN)
  {
    ej.CanDiscardTo(lsn)
  }

  function DiscardOld(ej: EphemeralJournal, lsn: LSN) : EphemeralJournal
    // requires EWF(ej)
    // requires CanDiscardOld(ej, lsn)
  {
    ej.DiscardOld(lsn)
  }

  predicate JournalCanFreeze(ej: EphemeralJournal, startLsn: LSN, endLsn: LSN)
  {
    && ej.CanDiscardTo(startLsn)
    && ej.CanDiscardTo(endLsn)
// TODO(jonh): delete this nonsense
//    // TODO(jonh): journal impl tells us what it can freeze.
//    // Here we pretend we can freeze anything in the journal
//    || startLsn==endLsn
//    || (
//      && ej.MsgHistory?
//      && ej.seqStart <= startLsn < endLsn <= ej.seqStart
//      )
  }

  function JournalFreeze(ej: EphemeralJournal, startLsn: LSN, endLsn: LSN) : PersistentJournal
    // requires EWF(ej);
    // requires JournalCanFreeze(ej, startLsn, endLsn)
  {
    if startLsn==endLsn
    then EmptyHistory
    else
      ej.DiscardOld(startLsn).DiscardRecent(endLsn)
  }
}
