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

  predicate DisjointEphemeralComponents(v: Variables)
    requires v.WF()
    requires v.ephemeral.Known?
  {
    // chained disjoint means all pairs are disjoint
    &&  v.freeset.ephemeral !! v.betree.EphemeralAUs() !! v.journal.EphemeralAUs()
  }

  predicate DisjointInFlightComponents(v: Variables)
    requires v.WF()
    requires v.journal.inFlight.Some?
  {
    && v.freeset.inFlight.value !! v.betree.InFlightAUs() !! v.journal.InFlightAUs()
  }

  predicate DisjointPersistentComponents(v: Variables)
  {
    && v.freeset.persistent !! v.betree.PersistentAUs() !! v.journal.PersistentAUs()
  }

  // cross state disjoints
  predicate DisjointAcrossStates(v: Variables)
    requires v.WF()
  {
    && (v.ephemeral.Known? ==> v.betree.PersistentAUs() !! v.journal.EphemeralAUs())
    && (v.ephemeral.Known? && v.betree.inFlight.Some? ==> v.betree.InFlightAUs() !! v.journal.EphemeralAUs()) 
  }

  function TotalEphemeral(v: Variables) : set<AU>
    requires v.WF()
    requires v.ephemeral.Known?
  {
    v.freeset.ephemeral + v.betree.EphemeralAUs() + v.journal.EphemeralAUs()
  }

  function TotalInflight(v: Variables) : set<AU>
    requires v.WF()
    requires v.journal.inFlight.Some?
  {
    v.freeset.inFlight.value + v.betree.InFlightAUs() + v.journal.InFlightAUs()
  }

  function TotalPersistent(v: Variables) : set<AU>
  {
    v.freeset.persistent + v.betree.PersistentAUs() + v.journal.PersistentAUs()
  }

  predicate StatesPreservesTotalAUs(v: Variables)
    requires v.WF()
  {
    && (v.ephemeral.Known? ==> TotalEphemeral(v) == v.freeset.total)
    && (v.journal.inFlight.Some? ==> TotalInflight(v) == v.freeset.total)
    && (v.betree.inFlight.Some? ==> v.betree.InFlightAUs() <= v.freeset.total)
    && TotalPersistent(v) == v.freeset.total
  }

  predicate Inv(v: Variables)
  {
    && v.WF()
    && FullStackJournalRefinement.Inv(v.journal)
    && FullStackBetreeRefinement.Inv(v.betree)

    && (v.ephemeral.Known? ==> DisjointEphemeralComponents(v))
    && (v.journal.inFlight.Some? ==> DisjointInFlightComponents(v))
    && DisjointPersistentComponents(v)
    && DisjointAcrossStates(v)  // exists in order to deal with inflight journal set after betree
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
    FullStackBetreeRefinement.LoadEphemeralFromPersistentAUs(v.betree, v'.betree, betreeLbl);

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
    
    assert v'.betree.EphemeralAUs() == v.betree.EphemeralAUs();
    assert v'.journal.EphemeralAUs() == v.journal.EphemeralAUs();
    
    FullStackJournalRefinement.NextRefines(v.journal, v'.journal, journalLbl);
    FullStackBetreeRefinement.NextRefines(v.betree, v'.betree, betreeLbl);

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
    
    assert v'.betree.EphemeralAUs() == v.betree.EphemeralAUs();
    assert v'.journal.EphemeralAUs() == v.journal.EphemeralAUs();

    FullStackJournalRefinement.NextRefines(v.journal, v'.journal, journalLbl);
    FullStackBetreeRefinement.NextRefines(v.betree, v'.betree, betreeLbl);
    
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
    var journalLbl := CoordinationJournal.InternalLabel(step.allocs, step.deallocs);
    assert step.allocs !! step.deallocs;
    assert FullStackJournalRefinement.FreshLabel(v.journal, journalLbl);
    
    FullStackJournalRefinement.NextRefines(v.journal, v'.journal, journalLbl);
    FullStackJournalRefinement.InternalLabelAccessibleAUs(v.journal, v'.journal, journalLbl);
    assert AbstractSystem.NextStep(I(v), I(v'), uiop, AbstractSystem.JournalInternalStep());
  }

  lemma BetreeInternalRefines(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires step.BetreeInternalStep?
    requires NextStep(v, v', uiop, step)
    ensures Inv(v')
    ensures AbstractSystem.Next(I(v), I(v'), uiop)
  {
    assert v.ephemeral.Known?;
    assert v'.ephemeral.Known?;
    assert v'.journal == v.journal;

    var betreeLbl := CoordinationBetree.InternalLabel(step.allocs, step.deallocs);
    var betreeStep :| CoordinationBetree.NextStep(v.betree, v'.betree, betreeLbl, betreeStep);
    assume step.deallocs <= v.betree.EphemeralAUs(); // TODO: by alloc betree inv
    assert step.allocs !! step.deallocs;
    assert FullStackBetreeRefinement.FreshLabel(v.betree, betreeLbl);

    assert v.WF();
    assert v'.WF();

    FullStackBetreeRefinement.NextRefines(v.betree, v'.betree, betreeLbl);
    FullStackBetreeRefinement.InternalLabelAccessibleAUs(v.betree, v'.betree, betreeLbl);

    if betreeStep.EphemeralInternalStep? {
      calc {
        v.freeset.ephemeral !! v.betree.EphemeralAUs() !! v.journal.EphemeralAUs();
        v.freeset.ephemeral - step.allocs !! v.betree.EphemeralAUs() + step.allocs !! v'.journal.EphemeralAUs();
        v'.freeset.ephemeral !! v'.betree.EphemeralAUs() !! v'.journal.EphemeralAUs();
        DisjointEphemeralComponents(v');
      }
      assert DisjointPersistentComponents(v');
    } else if betreeStep.FreezeFromPersistentInternalStep? {
      assert Inv(v');
    } else {
      FullStackBetreeRefinement.FreezeBetreeInternalLemma(v.betree, v'.betree, betreeLbl, betreeStep);
      assert v.journal.inFlight.None?;
      assert DisjointEphemeralComponents(v');
      assert DisjointPersistentComponents(v');
      assert DisjointAcrossStates(v');  // exists in order to deal with inflight journal set after betree
      assert StatesPreservesTotalAUs(v'); // not necessary for pure safety 
    }

    assert AbstractSystem.NextStep(I(v), I(v'), uiop, AbstractSystem.MapInternalStep());
  }

  lemma CommitStartRefines(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires step.CommitStartStep?
    requires NextStep(v, v', uiop, step)
    ensures Inv(v')
    ensures AbstractSystem.Next(I(v), I(v'), uiop)
  {
    var journalLbl := CoordinationJournal.CommitStartLabel(step.newBoundaryLsn, v.ephemeral.mapLsn);
    var betreeLbl := CoordinationBetree.CommitStartLabel(step.newBoundaryLsn);

    assert DisjointEphemeralComponents(v');
    assert DisjointPersistentComponents(v');

    FullStackJournalRefinement.CommitStartAccessibleAUs(v.journal, v'.journal, journalLbl);
    assert v'.journal.InFlightAUs() <= v.journal.EphemeralAUs();
    assert DisjointInFlightComponents(v');
    assert DisjointAcrossStates(v');

    var imageAddrs := v'.betree.InFlightAUs() + v'.journal.InFlightAUs();
    assert imageAddrs <= v.freeset.total;
    assert v.freeset.total - imageAddrs + imageAddrs == v.freeset.total;
    assert StatesPreservesTotalAUs(v');

    FullStackJournalRefinement.NextRefines(v.journal, v'.journal, journalLbl);
    FullStackBetreeRefinement.NextRefines(v.betree, v'.betree, betreeLbl);
    assert AbstractSystem.NextStep(I(v), I(v'), uiop, AbstractSystem.CommitStartStep(step.newBoundaryLsn));
  }

  lemma CommitCompleteRefines(v: Variables, v': Variables, uiop: UIOp, step: Step)
    requires Inv(v)
    requires step.CommitCompleteStep?
    requires NextStep(v, v', uiop, step)
    ensures Inv(v')
    ensures AbstractSystem.Next(I(v), I(v'), uiop)
  {
    assert v'.betree.persistent == v.betree.inFlight.value;
    assert v'.journal.persistent == v.journal.inFlight.value;
    assert v'.betree.ephemeral == v.betree.ephemeral;

    var journalLbl := CoordinationJournal.CommitCompleteLabel(v.ephemeral.mapLsn, step.discardedJournal);
    var betreeLbl := CoordinationBetree.CommitCompleteLabel();

    calc {
      DisjointEphemeralComponents(v);
      v.freeset.ephemeral !! v.betree.EphemeralAUs() !! v.journal.EphemeralAUs();
      v.freeset.ephemeral !! v'.betree.EphemeralAUs() !! v.journal.EphemeralAUs();
      v.freeset.ephemeral + step.discardedJournal !! v'.betree.EphemeralAUs() !! v.journal.EphemeralAUs() - step.discardedJournal;
      { FullStackJournalRefinement.CommitCompleteAccessibleAUs(v.journal, v'.journal, journalLbl); }
      v'.freeset.ephemeral !! v'.betree.EphemeralAUs() !! v'.journal.EphemeralAUs();
      DisjointEphemeralComponents(v');
    }

    calc {
      DisjointInFlightComponents(v);
      v.freeset.inFlight.value !! v.betree.InFlightAUs() !! v.journal.InFlightAUs();
      v'.freeset.persistent !! v'.betree.PersistentAUs() !! v'.journal.PersistentAUs();
      DisjointPersistentComponents(v');
    }

    calc {
      DisjointAcrossStates(v);
      v.betree.InFlightAUs() !! v.journal.EphemeralAUs();
      v'.betree.PersistentAUs() !! v.journal.EphemeralAUs();
      { FullStackJournalRefinement.CommitCompleteAccessibleAUs(v.journal, v'.journal, journalLbl); }
      v'.betree.PersistentAUs() !! v'.journal.EphemeralAUs();
      { assert v'.betree.inFlight.None?; }
      DisjointAcrossStates(v');
    }

    calc {
      TotalEphemeral(v) == v.freeset.total;
      v.freeset.ephemeral + v.betree.EphemeralAUs() + v.journal.EphemeralAUs() == v'.freeset.total;
      v.freeset.ephemeral + v'.betree.EphemeralAUs() + v.journal.EphemeralAUs() == v'.freeset.total;
      v'.freeset.ephemeral + v'.betree.EphemeralAUs() + (v.journal.EphemeralAUs() - step.discardedJournal)  == v'.freeset.total;
      { FullStackJournalRefinement.CommitCompleteAccessibleAUs(v.journal, v'.journal, journalLbl); }
      v'.freeset.ephemeral + v'.betree.EphemeralAUs() + v'.journal.EphemeralAUs() == v'.freeset.total;
      StatesPreservesTotalAUs(v');
    }

    assert v'.journal.inFlight.None?;
    assert TotalPersistent(v') == v'.freeset.total;

    FullStackJournalRefinement.NextRefines(v.journal, v'.journal, journalLbl);
    FullStackBetreeRefinement.NextRefines(v.betree, v'.betree, betreeLbl);
    assert AbstractSystem.NextStep(I(v), I(v'), uiop, AbstractSystem.CommitCompleteStep());
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
      case JournalInternalStep(_, _) => JournalInternalRefines(v, v', uiop, step);
      case BetreeInternalStep(_, _) => BetreeInternalRefines(v, v', uiop, step);
      case ReqSyncStep() => ReqSyncRefines(v, v', uiop, step);
      case ReplySyncStep() => ReplySyncRefines(v, v', uiop, step);
      case CommitStartStep(_) => CommitStartRefines(v, v', uiop, step);
      case CommitCompleteStep(_) => CommitCompleteRefines(v, v', uiop, step);
      case CrashStep() => CrashRefines(v, v', uiop, step);
    }
  }
}
