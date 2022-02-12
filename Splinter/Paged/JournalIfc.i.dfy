// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "MsgHistory.i.dfy"

abstract module JournalIfc {
  import opened Options
  import opened MsgHistoryMod
  import opened StampedMapMod // LSN TODO(jonh): move

  // TODO(jonh): Recover and document why these are different types.
  type PersistentJournal(==,!new)
  type EphemeralJournal(==,!new)

  predicate PWF(pj: PersistentJournal)
  predicate EWF(ej: EphemeralJournal)

  // Interpretations of these journals, for proof semantics (Refinement file).
  function IPJ(pj: PersistentJournal) : (out:MsgHistory)
    requires PWF(pj)
    ensures out.WF()

  function IEJ(ej: EphemeralJournal) : (out:MsgHistory)
    requires EWF(ej)
    ensures out.WF()

  // Functions used in the runtime specification (this file).

  function Mkfs() : (out:PersistentJournal)
    ensures PWF(out)
    ensures IPJ(out).EmptyHistory?

  function LoadJournal(pj: PersistentJournal) : (out:EphemeralJournal)
    requires PWF(pj)
    ensures EWF(out)
    ensures IEJ(out) == IPJ(pj)

  function PJournalSeqEnd(pj: PersistentJournal) : (out:Option<LSN>)
    requires PWF(pj)
    ensures out.Some? == IPJ(pj).MsgHistory?
    ensures out.Some? ==> out.value == IPJ(pj).seqEnd

  function EJournalSeqEnd(ej: EphemeralJournal) : (out:Option<LSN>)
    requires EWF(ej)
    ensures out.Some? == IEJ(ej).MsgHistory?
    ensures out.Some? ==> out.value == IEJ(ej).seqEnd

  predicate JournalIncludesSubseq(ej: EphemeralJournal, msgs: MsgHistory)
    requires EWF(ej)
    requires msgs.WF()
    ensures JournalIncludesSubseq(ej, msgs) ==> IEJ(ej).IncludesSubseq(msgs)

  function JournalConcat(ej: EphemeralJournal, msgs: MsgHistory) : (out:EphemeralJournal)
    requires EWF(ej)
    requires msgs.WF()
    requires msgs.EmptyHistory? || EJournalSeqEnd(ej).None? || msgs.CanFollow(EJournalSeqEnd(ej).value)
    ensures EWF(out)
    ensures IEJ(ej).Concat(msgs) == IEJ(out)

  predicate JournalCanFreeze(ej: EphemeralJournal, startLsn: LSN, endLsn: LSN)
    requires EWF(ej)
    ensures JournalCanFreeze(ej, startLsn, endLsn) ==>
      (startLsn == endLsn ||
       (IEJ(ej).CanDiscardTo(startLsn) && IEJ(ej).CanDiscardTo(endLsn)))

  function JournalFreeze(ej: EphemeralJournal, startLsn: LSN, endLsn: LSN) : (out:PersistentJournal)
    requires EWF(ej)
    requires JournalCanFreeze(ej, startLsn, endLsn)
    requires startLsn <= endLsn
    ensures PWF(out)
    ensures IPJ(out) == if startLsn==endLsn then EmptyHistory else IEJ(ej).DiscardOld(startLsn).DiscardRecent(endLsn)

  predicate CanDiscardOld(ej: EphemeralJournal, lsn: LSN)
    requires EWF(ej)
    ensures CanDiscardOld(ej, lsn) <==> IEJ(ej).CanDiscardTo(lsn)

  function DiscardOld(ej: EphemeralJournal, lsn: LSN) : (out:EphemeralJournal)
    requires EWF(ej)
    requires CanDiscardOld(ej, lsn)
    ensures EWF(out)
    ensures IEJ(out) == IEJ(ej).DiscardOld(lsn)
}
