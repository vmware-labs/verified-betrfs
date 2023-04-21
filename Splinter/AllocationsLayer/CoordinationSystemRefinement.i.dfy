// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "CoordinationSystem.i.dfy"
include "FullStackBetreeRefinement.i.dfy"
include "FullStackJournalRefinement.i.dfy"

module CoordinationSystemRefinement {
  import opened GenericDisk
  import FullStackJournalRefinement
  import FullStackBetreeRefinement
  import opened CoordinationSystemMod
  import AllocationBetreeMod
  // import AbstractSystem = CoordinationSystem
//   import opened Options
//   import opened MapRemove_s
//   import opened CrashTolerantMapSpecMod
//   import opened MsgHistoryMod
//   import opened KeyType
//   import opened ValueMessage
//   import opened TotalKMMapMod
//   import opened LSNMod
//   import opened CoordinationJournal
//   import opened CoordinationBetree

  predicate KnownEphemeral(v: Variables)
  {
    && v.journal.ephemeral.Known? 
    && v.betree.ephemeral.Known?
  }

  predicate InFlightBetreeOnly(v: Variables)
  {
    && v.journal.ephemeral.Known?
    && v.journal.inFlight.None?
    && v.betree.inFlight.Some? 
    && v.freeset.inFlight.Some?
  }

  predicate InFlightAllReady(v: Variables)
  {
    && v.journal.inFlight.Some? 
    && v.betree.inFlight.Some? 
    && v.freeset.inFlight.Some? 
  }

  predicate DisjointEphemeralComponents(v: Variables)
  {
    && (KnownEphemeral(v) ==> v.freeset.ephemeral !! v.betree.EphemeralAUs() !! v.journal.EphemeralAUs())
  }

  predicate DisjointInFlightComponents(v: Variables)
  {
    && (InFlightBetreeOnly(v) ==> v.freeset.inFlight.value !! v.betree.InFlightAUs() !! v.journal.EphemeralAUs())
    && (InFlightAllReady(v) ==> v.freeset.inFlight.value !! v.betree.InFlightAUs() !! v.journal.InFlightAUs())
  }

  predicate DisjointPersistentComponents(v: Variables)
  {
    && v.freeset.persistent !! v.betree.PersistentAUs() !! v.journal.PersistentAUs()
  }

  function TotalEphemeral(v: Variables) : set<AU>
    requires KnownEphemeral(v)
  {
    v.freeset.ephemeral + v.betree.EphemeralAUs() + v.journal.EphemeralAUs()
  }

  function TotalPersistent(v: Variables) : set<AU>
  {
    v.freeset.persistent + v.betree.PersistentAUs() + v.journal.PersistentAUs()
  }

  function TotalInflight(v: Variables) : set<AU>
    requires InFlightBetreeOnly(v) || InFlightAllReady(v)
  {
    if InFlightAllReady(v)
    then v.freeset.inFlight.value + v.betree.InFlightAUs() + v.journal.InFlightAUs()
    else v.freeset.inFlight.value + v.betree.InFlightAUs() + v.journal.EphemeralAUs()
  }

  predicate StatesPreservesTotalAUs(v: Variables)
  {
    && (KnownEphemeral(v) ==> TotalEphemeral(v) == TotalPersistent(v))
    && (InFlightBetreeOnly(v) || InFlightAllReady(v) ==> TotalInflight(v) == TotalPersistent(v))
  }

  predicate Inv(v: Variables)
  {
    && (v.journal.ephemeral.Known? <==> v.betree.ephemeral.Known?)
    && (v.freeset.inFlight.Some? <==> v.betree.inFlight.Some?)
    && (v.journal.inFlight.Some? ==> v.betree.inFlight.Some?)

    && FullStackJournalRefinement.Inv(v.journal)
    && FullStackBetreeRefinement.Inv(v.betree)

    && DisjointEphemeralComponents(v)
    && DisjointInFlightComponents(v)
    && DisjointPersistentComponents(v)
    && StatesPreservesTotalAUs(v)
  }

  function I(v: Variables) : AbstractSystem.Variables
    requires Inv(v)
  {
    var journal := FullStackJournalRefinement.I(v.journal);
    var mapadt := FullStackBetreeRefinement.I(v.betree);
    AbstractSystem.Variables(journal, mapadt, v.ephemeral)
  } 

  lemma InitRefines(v: Variables, availAUs: set<AU>)
    requires Init(v, availAUs)
    ensures Inv(v)
    ensures AbstractSystem.Init(I(v))
  {
    FullStackBetreeRefinement.InitRefines(v.betree);
  }

  lemma NextRefines(v: Variables, v': Variables, uiop: UIOp)
    requires Inv(v)
    requires Next(v, v', uiop)
    ensures Inv(v')
    ensures AbstractSystem.Next(I(v), I(v'), uiop)
  {
    var step :| NextStep(v, v', uiop, step);
    match step {
      // case LoadEphemeralFromPersistentStep() => LoadEphemeralFromPersistent(v, v', uiop)
      // case RecoverStep(records) => Recover(v, v', uiop, records)
      // case AcceptRequestStep() => AcceptRequest(v, v', uiop)
      // case QueryStep() => Query(v, v', uiop)
      // case PutStep() => Put(v, v', uiop)
      // case DeliverReplyStep() => DeliverReply(v, v', uiop)
      // case JournalInternalStep(allocs, deallocs) => JournalInternal(v, v', uiop, allocs, deallocs)
      // case MapInternalStep(allocs, deallocs) => MapInternal(v, v', uiop, allocs, deallocs)
      // case ReqSyncStep() => ReqSync(v, v', uiop)
      // case ReplySyncStep() => ReplySync(v, v', uiop)
      // case FreezeBetreeStep(unobservedBetree, unobservedJournal) => FreezeBetree(v, v', uiop, unobservedBetree, unobservedJournal)
      // case CommitStartStep(newBoundaryLsn) => CommitStart(v, v', uiop, newBoundaryLsn)
      // case CommitCompleteStep(discardedJournal) => CommitComplete(v, v', uiop, discardedJournal)
      // case CrashStep() => Crash(v, v', uiop)
      case _ => assume false;
    }
    // requires lbl.InternalLabel? ==> AllocationBetreeRefinement.FreshLabel(v.ephemeral.v, AllocLbl(v, v', lbl))
    // FullStackBetreeRefinement.NextRefines(v.betree, v'.betree);
    // FullStackJournalRefinement.NextRefines(v.journal, v'.journal);
  }
}
