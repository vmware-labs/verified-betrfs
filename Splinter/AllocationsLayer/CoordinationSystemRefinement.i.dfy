// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "CoordinationSystem.i.dfy"
include "FullStackBetreeRefinement.i.dfy"
include "FullStackJournalRefinement.i.dfy"

module CoordinationSystemRefinement {
  import opened ValueMessage
  import opened MsgHistoryMod
  import opened GenericDisk
  import opened CoordinationSystemMod
  import FullStackJournalRefinement
  import FullStackBetreeRefinement
  import AllocationJournalRefinement

  // import AllocationBetreeMod
  // import AbstractSystem = CoordinationSystem
//   import opened Options
//   import opened MapRemove_s
//   import opened CrashTolerantMapSpecMod
//   import opened MsgHistoryMod
//   import opened KeyType
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
    // chained disjoint means all pairs are disjoint
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

  function TotalInflightBetreeOnly(v: Variables) : set<AU>
    requires InFlightBetreeOnly(v)
  {
    v.freeset.inFlight.value + v.betree.InFlightAUs() + v.journal.EphemeralAUs()
  }

  function TotalInflight(v: Variables) : set<AU>
    requires InFlightAllReady(v)
  {
    v.freeset.inFlight.value + v.betree.InFlightAUs() + v.journal.InFlightAUs()
  }

  predicate StatesPreservesTotalAUs(v: Variables)
  {
    && (KnownEphemeral(v) ==> TotalEphemeral(v) == TotalPersistent(v))
    && (InFlightBetreeOnly(v) ==> TotalInflightBetreeOnly(v) == TotalPersistent(v))
    && (InFlightAllReady(v) ==> TotalInflight(v) == TotalPersistent(v))
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
    && StatesPreservesTotalAUs(v) // not necessary for pure safety 
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

  lemma LoadEphemeralFromPersistentRefines(v: Variables, v': Variables, uiop: UIOp)
    requires Inv(v)
    requires LoadEphemeralFromPersistent(v, v', uiop)
    ensures Inv(v')
    ensures AbstractSystem.Next(I(v), I(v'), uiop)
  {
    var journalLbl := CoordinationJournal.LoadEphemeralFromPersistentLabel();
    var betreeLbl := CoordinationBetree.LoadEphemeralFromPersistentLabel(v'.ephemeral.mapLsn);
    
    FullStackJournalRefinement.NextRefines(v.journal, v'.journal, journalLbl);
    FullStackBetreeRefinement.NextRefines(v.betree, v'.betree, betreeLbl);

    assert v'.journal.persistent == v.journal.persistent;
    assert v'.betree.persistent == v.betree.persistent;
    assert v'.journal.EphemeralAUs() == v.journal.PersistentAUs() by {
      AllocationJournalRefinement.reveal_LikesJournalInv();
    }
    assume v'.betree.EphemeralAUs() == v.betree.PersistentAUs(); // maintained by betree Inv

    assert DisjointEphemeralComponents(v');
    assert StatesPreservesTotalAUs(v');

    assert AbstractSystem.NextStep(I(v), I(v'), uiop, AbstractSystem.LoadEphemeralFromPersistentStep());
  }

  lemma RecoverRefines(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires step.RecoverStep?
    requires NextStep(v, v', uiop, step)
    ensures Inv(v')
    ensures AbstractSystem.Next(I(v), I(v'), uiop)
  {
    var journalLbl := CoordinationJournal.ReadForRecoveryLabel(step.records);
    var betreeLbl := CoordinationBetree.PutRecordsLabel(step.records);
    
    FullStackJournalRefinement.NextRefines(v.journal, v'.journal, journalLbl);
    FullStackBetreeRefinement.NextRefines(v.betree, v'.betree, betreeLbl);

    CoordinationBetree.EphemeralAUsSameAfterPut(v.betree, v'.betree, betreeLbl);
    assert v'.betree.EphemeralAUs() == v.betree.EphemeralAUs();
    assert v'.journal.EphemeralAUs() == v.journal.EphemeralAUs();

    assert AbstractSystem.NextStep(I(v), I(v'), uiop, AbstractSystem.RecoverStep(step.records));
  }

  lemma QueryRefines(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires step.QueryStep?
    requires NextStep(v, v', uiop, step)
    ensures Inv(v')
    ensures AbstractSystem.Next(I(v), I(v'), uiop)
  {
    var key := uiop.baseOp.req.input.key;
    var value := uiop.baseOp.reply.output.value;
    var journalLbl := CoordinationJournal.QueryEndLsnLabel(v.ephemeral.mapLsn);
    var betreeLbl := CoordinationBetree.QueryLabel(v.ephemeral.mapLsn, key, value);
    
    FullStackJournalRefinement.NextRefines(v.journal, v'.journal, journalLbl);
    FullStackBetreeRefinement.NextRefines(v.betree, v'.betree, betreeLbl);

    assert AbstractSystem.NextStep(I(v), I(v'), uiop, AbstractSystem.QueryStep());
  }

  lemma PutRefines(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires step.PutStep?
    requires NextStep(v, v', uiop, step)
    ensures Inv(v')
    ensures AbstractSystem.Next(I(v), I(v'), uiop)
  {
    var key := uiop.baseOp.req.input.key;
    var val := uiop.baseOp.req.input.value;
    var singleton := MsgHistoryMod.SingletonAt(v.ephemeral.mapLsn, KeyedMessage(key, Define(val)));
    var journalLbl := CoordinationJournal.PutLabel(singleton);
    var betreeLbl := CoordinationBetree.PutRecordsLabel(singleton);

    FullStackJournalRefinement.NextRefines(v.journal, v'.journal, journalLbl);
    FullStackBetreeRefinement.NextRefines(v.betree, v'.betree, betreeLbl);
    CoordinationBetree.EphemeralAUsSameAfterPut(v.betree, v'.betree, betreeLbl);
    assert v'.betree.EphemeralAUs() == v.betree.EphemeralAUs();
    assert v'.journal.EphemeralAUs() == v.journal.EphemeralAUs();
    
    assert AbstractSystem.NextStep(I(v), I(v'), uiop, AbstractSystem.PutStep());
  }

  lemma ReqSyncRefines(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires step.ReqSyncStep?
    requires NextStep(v, v', uiop, step)
    ensures Inv(v')
    ensures AbstractSystem.Next(I(v), I(v'), uiop)
  {
    var journalLbl := CoordinationJournal.QueryEndLsnLabel(v.ephemeral.mapLsn);
    FullStackJournalRefinement.NextRefines(v.journal, v'.journal, journalLbl);
    assert v'.journal.EphemeralAUs() == v.journal.EphemeralAUs();
    assert AbstractSystem.NextStep(I(v), I(v'), uiop, AbstractSystem.ReqSyncStep());
  }

  lemma ReplySyncRefines(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires step.ReplySyncStep?
    requires NextStep(v, v', uiop, step)
    ensures Inv(v')
    ensures AbstractSystem.Next(I(v), I(v'), uiop)
  {
    var journalLbl := CoordinationJournal.QueryLsnPersistenceLabel(v.ephemeral.syncReqs[uiop.syncReqId]);
    FullStackJournalRefinement.NextRefines(v.journal, v'.journal, journalLbl);
    assert v'.journal.EphemeralAUs() == v.journal.EphemeralAUs();
    assert AbstractSystem.NextStep(I(v), I(v'), uiop, AbstractSystem.ReplySyncStep());
  }

  lemma CrashRefines(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires step.CrashStep?
    requires NextStep(v, v', uiop, step)
    ensures Inv(v')
    ensures AbstractSystem.Next(I(v), I(v'), uiop)
  {
    var journalLbl := CoordinationJournal.CrashLabel();
    var betreeLbl := CoordinationBetree.CrashLabel();

    FullStackJournalRefinement.NextRefines(v.journal, v'.journal, journalLbl);
    FullStackBetreeRefinement.NextRefines(v.betree, v'.betree, betreeLbl);
    assert AbstractSystem.NextStep(I(v), I(v'), uiop, AbstractSystem.CrashStep());
  }

  lemma JournalInternalRefines(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires step.JournalInternalStep?
    requires NextStep(v, v', uiop, step)
    ensures Inv(v')
    ensures AbstractSystem.Next(I(v), I(v'), uiop)
  {
    assert v'.journal.inFlight == v.journal.inFlight;
    assert v'.journal.persistent == v.journal.persistent;

    var journalLbl := CoordinationJournal.InternalLabel(step.allocs, step.deallocs);
    assert FullStackJournalRefinement.FreshLabel(v.journal, journalLbl);

    FullStackJournalRefinement.NextRefines(v.journal, v'.journal, journalLbl);
    FullStackJournalRefinement.InternalLabelAccessibleAUs(v.journal, v'.journal, journalLbl);

    assert v.journal.EphemeralAUs() + step.allocs - step.deallocs == v'.journal.EphemeralAUs();

    if InFlightBetreeOnly(v) {
      assert InFlightBetreeOnly(v'); 

      /*
      predicate DisjointInFlightComponents(v: Variables) {
        && (InFlightBetreeOnly(v) ==> v.freeset.inFlight.value !! v.betree.InFlightAUs() !! v.journal.EphemeralAUs())
      }
        
      predicate preserves total AUs
        && (InFlightBetreeOnly(v) ==> TotalInflightBetreeOnly(v) == TotalPersistent(v)

      TotalInflightBetreeOnly(v) == v.freeset.inFlight.value + v.betree.InFlightAUs() + v.journal.EphemeralAUs()
      
      */
          // assert step.allocs !! v'.betree.EphemeralAUs();
    // assert step.allocs !! v'.freeset.ephemeral;
    // assert step.allocs !! v.journal.EphemeralAUs();
    
    }

    //   && (InFlightBetreeOnly(v) ==> TotalInflightBetreeOnly(v) == TotalPersistent(v))
    // && ((v) ==> TotalInflight(v) == TotalPersistent(v))

    // if InFlightBetreeOnly(v) {
    //   assert InFlightBetreeOnly(v');
    //   assert TotalInflight(v) == TotalPersistent(v);
    //   assert TotalInflight(v') == TotalPersistent(v');

  //   function TotalInflight(v: Variables) : set<AU>
  //   requires InFlightBetreeOnly(v) || InFlightAllReady(v)
  // {
  //   if InFlightAllReady(v)
  //   then v.freeset.inFlight.value + v.betree.InFlightAUs() + v.journal.InFlightAUs()
  //   else v.freeset.inFlight.value + v.betree.InFlightAUs() + v.journal.EphemeralAUs()
  // }

    // }

    // assert StatesPreservesTotalAUs(v');

    assume false;
    assert DisjointEphemeralComponents(v');
    assert AbstractSystem.NextStep(I(v), I(v'), uiop, AbstractSystem.JournalInternalStep());

  }


  lemma NextRefines(v: Variables, v': Variables, uiop: UIOp)
    requires Inv(v)
    requires Next(v, v', uiop)
    ensures Inv(v')
    ensures AbstractSystem.Next(I(v), I(v'), uiop)
  {
    var step :| NextStep(v, v', uiop, step);
    match step {
      case LoadEphemeralFromPersistentStep() => LoadEphemeralFromPersistentRefines(v, v', uiop);
      case RecoverStep(records) => RecoverRefines(v, v', uiop, step);
      case AcceptRequestStep() => assert AbstractSystem.NextStep(I(v), I(v'), uiop, AbstractSystem.AcceptRequestStep());
      case QueryStep() => QueryRefines(v, v', uiop, step);
      case PutStep() => PutRefines(v, v', uiop, step);
      case DeliverReplyStep() => assert AbstractSystem.NextStep(I(v), I(v'), uiop, AbstractSystem.DeliverReplyStep());
      // case JournalInternalStep(allocs, deallocs) => JournalInternal(v, v', uiop, allocs, deallocs)
      // case MapInternalStep(allocs, deallocs) => MapInternal(v, v', uiop, allocs, deallocs)
      case ReqSyncStep() => ReqSyncRefines(v, v', uiop, step);
      case ReplySyncStep() => ReplySyncRefines(v, v', uiop, step);
      // case FreezeBetreeStep(unobservedBetree, unobservedJournal) => FreezeBetree(v, v', uiop, unobservedBetree, unobservedJournal)
      // case CommitStartStep(newBoundaryLsn) => CommitStart(v, v', uiop, newBoundaryLsn)
      // case CommitCompleteStep(discardedJournal) => CommitComplete(v, v', uiop, discardedJournal)
      case CrashStep() => CrashRefines(v, v', uiop, step);
      case _ => assume false;
    }
  }
}
