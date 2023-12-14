include "IOSystem.s.dfy"
include "ProgramInterp.i.dfy"
include "ProofObligations.s.dfy"
include "JournalInterp.i.dfy"
include "SplinterTreeInvariants.i.dfy"
include "CacheLemmas.i.dfy"

// TODO(jonh) update this file and ProofObligations to use module functor syntax
module VeribetrIOSystem refines IOSystem {
  import P = ProgramMachineMod
}

module Proof refines ProofObligations {
  import opened DiskTypesMod
  import MapSpecMod
  import StampedMapMod
  import AllocationMod
  import opened SequenceSetsMod

  import ConcreteSystem = VeribetrIOSystem // ProgramMachineMod is imported here
  import JournalMachineMod
  import SplinterTreeMachineMod

  import JournalInterpMod
  import ProgramInterpMod
  import SplinterTreeInterpMod
  import SplinterTreeInvariantMod

  import CacheIfc
  import CacheLemmasMod

  function I(v: ConcreteSystem.Variables) : CrashTolerantMapSpecMod.Variables
  {
    if !v.program.WF()
    then
      CrashTolerantMapSpecMod.InitState()
    else
      ProgramInterpMod.IM(v.program, v.disk.contents)
  }

  // NOTE: These are all program invariants. Maybe we should change the argument
  predicate Inv(v: ConcreteSystem.Variables)
  {
    && v.program.WF()
    && (!v.program.phase.SuperblockUnknown? ==> ( // These invariants over the splinter tree / journal only have to hold when the system is recovered/inited and in the running phase
              && JournalInterpMod.Invariant(v.program.journal, v.program.cache)

              // ties together the updates flowing from the journal to the tree
              && SplinterTreeInterpMod.IM(v.program.cache, v.program.betree).seqEnd == v.program.journal.boundaryLSN

              // Journal start point stays synchronized with betree end point
              && v.program.betree.endSeq == v.program.journal.boundaryLSN
            )
      )
    && ProgramInterpMod.Invariant(v.program)
  }

  lemma EnsureInductive(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables)
    requires Inv(v)
    ensures Inv(v')
  {
    assume false; // TODO
  }

  // Remember that this is the init of a p
  lemma InitRefines(v: ConcreteSystem.Variables)
  {
  }

  lemma SplinterInternalRefines(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp, cacheOps : CacheIfc.Ops, pstep: ConcreteSystem.P.Step, sk: SplinterTreeMachineMod.Skolem)
    requires Inv(v)
    requires v.program.WF()
    requires ConcreteSystem.P.NextStep(v.program, v'.program, uiop, cacheOps, pstep)
    requires pstep == ConcreteSystem.P.SplinterTreeInternalStep(sk)

    // Is this a problem with using imports?
    ensures Inv(v')
    ensures CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
  {
    EnsureInductive(v, v');

    var betreeInterp := SplinterTreeInterpMod.IM(v.program.cache, v.program.betree);

    // BeTree changes in an interpretation-preserving way.
    SplinterTreeInterpMod.InternalStepLemma(v.program.betree, v'.program.betree, v.program.cache, v'.program.cache, cacheOps, sk);
    assert SplinterTreeInterpMod.IM(v.program.cache, v.program.betree)
      == SplinterTreeInterpMod.IM(v'.program.cache, v'.program.betree);

    // Journal doesn't change (framing argument)
    var journalReads := JournalInterpMod.IReads(v.program.cache, v.program.journal.CurrentSuperblock());
    assume Members(journalReads) <= JournalMachineMod.Alloc(v.program.journal); // framing helper
    assume AllocationMod.DiskViewsEquivalentForSeq(v.program.cache.dv, v'.program.cache.dv, journalReads);  // framing helper
    JournalInterpMod.Framing(v.program.journal, v.program.cache, v'.program.cache);

    // Sum of betree and journal doesn't change
    if (v.program.phase.Running?) {
      var sb := ProgramInterpMod.ISuperblock(v.program.cache.dv).value;
      var sb' := ProgramInterpMod.ISuperblock(v'.program.cache.dv).value;
      assume sb' == sb; // framing argument here
      assert ProgramInterpMod.IM(v.program, v.disk.contents) == ProgramInterpMod.IM(v'.program, v'.disk.contents);
    } else {
      assume ProgramInterpMod.IMRunning(ProgramInterpMod.SynthesizeRunningVariables(v.disk.contents))
          == ProgramInterpMod.IMRunning(ProgramInterpMod.SynthesizeRunningVariables(v'.disk.contents)); // Framing argument: when we wrote the cache (and flushed to the disk), we didn't 
      assert ProgramInterpMod.IM(v.program, v.disk.contents) == ProgramInterpMod.IM(v'.program, v'.disk.contents);
    }
    assert I(v) == I(v');
    assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), CrashTolerantMapSpecMod.NoopOp);
//    assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
  }

  lemma JournalInternalRefines(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp, cacheOps : CacheIfc.Ops, pstep: ConcreteSystem.P.Step, sk: JournalMachineMod.Skolem)
    requires Inv(v)
    requires v.program.WF()
    requires ConcreteSystem.P.NextStep(v.program, v'.program, uiop, cacheOps, pstep)
    requires pstep == ConcreteSystem.P.JournalInternalStep(sk)

    // Is this a problem with using imports?
    ensures Inv(v')
    ensures CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
  {
    EnsureInductive(v, v');

    // Journal changes in an interpretation-preserving way.
//    JournalInterpMod.InternalStepLemma(v.program.journal, v'.program.journal, v.program.cache, v'.program.cache, cacheOps, sk);
    assert SplinterTreeInterpMod.IM(v.program.cache, v.program.betree)
      == SplinterTreeInterpMod.IM(v'.program.cache, v'.program.betree);

    // Journal doesn't change (framing argument)
    var journalReads := JournalInterpMod.IReads(v.program.cache, v.program.journal.CurrentSuperblock());
    assume Members(journalReads) <= JournalMachineMod.Alloc(v.program.journal); // framing helper
    assume AllocationMod.DiskViewsEquivalentForSeq(v.program.cache.dv, v'.program.cache.dv, journalReads);  // framing helper
//    JournalInterpMod.Framing(v.program.journal, v.program.cache, v'.program.cache, betreeInterp);

    // Sum of betree and journal doesn't change
    if (v.program.phase.Running?) {
      var sb := ProgramInterpMod.ISuperblock(v.program.cache.dv).value;
      var sb' := ProgramInterpMod.ISuperblock(v'.program.cache.dv).value;
      assume sb' == sb; // framing argument here
      assert ProgramInterpMod.IM(v.program, v.disk.contents) == ProgramInterpMod.IM(v'.program, v'.disk.contents);
    } else {
      assume ProgramInterpMod.IMRunning(ProgramInterpMod.SynthesizeRunningVariables(v.disk.contents))
          == ProgramInterpMod.IMRunning(ProgramInterpMod.SynthesizeRunningVariables(v'.disk.contents)); // Framing argument: when we wrote the cache (and flushed to the disk), we didn't 
      assert ProgramInterpMod.IM(v.program, v.disk.contents) == ProgramInterpMod.IM(v'.program, v'.disk.contents);
    }
    assert I(v) == I(v');
    assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), CrashTolerantMapSpecMod.NoopOp);
//    assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
  }

  // Ensures that commiting a new superblock does not change the interpretation
  lemma CommitCompleteRefines(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp, cacheOps : CacheIfc.Ops, pstep: ConcreteSystem.P.Step)
    // The super block has to be known for us to take a valid JournalInternal step
    requires !v.program.phase.SuperblockUnknown?
    requires Inv(v)

    requires ConcreteSystem.P.NextStep(v.program, v'.program, uiop, cacheOps, pstep)
    requires pstep == ConcreteSystem.P.CommitCompleteStep

    ensures !v'.program.phase.SuperblockUnknown?
    ensures Inv(v')
    ensures ProgramInterpMod.IMRunning(v.program) ==  ProgramInterpMod.IMRunning(v'.program)
  {
    assume !v'.program.phase.SuperblockUnknown?; // QUESTION: Can we just assume this???

    EnsureInductive(v, v'); // TODO : prove inductive lemma


    var sbOld := ProgramInterpMod.ISuperblock(v.program.cache.dv);
    var sbNew := ProgramInterpMod.ISuperblock(v'.program.cache.dv);

    assert sbOld.None? ==> ( ProgramInterpMod.IMRunning(v.program) == CrashTolerantMapSpecMod.InitState());
    assert sbNew.None? ==> ( ProgramInterpMod.IMRunning(v'.program) == CrashTolerantMapSpecMod.InitState());
    assert sbOld.None? ==> sbNew.None?; // cuz we're at a commit step?

    var splinterTreeInterp := SplinterTreeInterpMod.IM(v.program.cache, v.program.betree);
    assume SplinterTreeInterpMod.IM(v'.program.cache, v'.program.betree) == splinterTreeInterp;

    assume JournalInterpMod.I(v.program.journal, v.program.cache) ==
     JournalInterpMod.I(v'.program.journal, v'.program.cache);

    assert JournalInterpMod.I(v.program.journal, v.program.cache).AsCrashTolerantMapSpec(splinterTreeInterp) ==
     JournalInterpMod.I(v'.program.journal, v'.program.cache).AsCrashTolerantMapSpec(splinterTreeInterp);


    // hmm.... doesn't believe this -- assume for now
    assume ProgramInterpMod.IMRunning(v.program) ==  ProgramInterpMod.IMRunning(v'.program);
  }

  lemma PutRefines(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp, cacheOps : CacheIfc.Ops, pstep: ConcreteSystem.P.Step, sk: SplinterTreeMachineMod.Skolem)
    // Requires needed for IM to work
    requires Inv(v)

    // Actual requires
    ensures Inv(v')
    requires ConcreteSystem.P.NextStep(v.program, v'.program, uiop, cacheOps, pstep)
    requires pstep == ConcreteSystem.P.PutStep(sk)
    requires uiop.OperateOp?
    requires uiop.baseOp.ExecuteOp?
    requires uiop.baseOp.req.input.PutInput?
    ensures  CrashTolerantMapSpecMod.Operate(I(v), I(v'), uiop.baseOp)
  {
    // Here we need talk about the journal -- TODO
    assume CrashTolerantMapSpecMod.Operate(I(v), I(v'), uiop.baseOp);

  }

  lemma QueryRefines(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp, cacheOps : CacheIfc.Ops, pstep: ConcreteSystem.P.Step, sk: SplinterTreeMachineMod.Skolem)
    // Requires needed for IM to work
    requires Inv(v)

    // Actual requires
    ensures Inv(v')
    requires ConcreteSystem.P.NextStep(v.program, v'.program, uiop, cacheOps, pstep)
    //requires pstep == ConcreteSystem.P.QueryStep(sk)
    requires uiop.OperateOp?
    requires uiop.baseOp.ExecuteOp?
    requires uiop.baseOp.req.input.GetInput?
    ensures  CrashTolerantMapSpecMod.Operate(I(v), I(v'), uiop.baseOp)
  {
    assume CrashTolerantMapSpecMod.Operate(I(v), I(v'), uiop.baseOp);// TODO

  }


  lemma ProgramMachineStepRefines(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp, step : ConcreteSystem.Step)
    requires Inv(v)

    // TODO: should probably take the invariant out of journalInterp
    requires ConcreteSystem.Next(v, v', uiop)
    requires ConcreteSystem.NextStep(v, v', uiop, step)
    requires step.MachineStep?
    ensures CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop)
    ensures Inv(v')
  {
     var cacheOps, pstep :| ConcreteSystem.P.NextStep(v.program, v'.program, uiop, cacheOps, pstep);
    match pstep {
      case RecoverStep(puts, newbetree) => {
        // Only argue about IMStable == IM of CrashTolerantMapSpecMod
        assume CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop); // NOT DONE!!!!!
      }
      case QueryStep(key, val, sk) => {
        assert uiop.OperateOp?;
        assert uiop.baseOp.req.input.GetInput?;
        QueryRefines(v, v', uiop, cacheOps, pstep, sk);

        // Need to leverage Lookup here
        assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case PutStep(sk) => {
        assert uiop.OperateOp?;
        assert uiop.baseOp.req.input.PutInput?;
        PutRefines(v, v', uiop, cacheOps, pstep, sk);
        assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case JournalInternalStep(sk) => {
        JournalInternalRefines(v, v', uiop, cacheOps, pstep, sk);
        assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case SplinterTreeInternalStep(sk) => {
        SplinterInternalRefines(v, v', uiop, cacheOps, pstep, sk);
        assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case ReqSyncStep(syncReqId) => {

          // here uiop is not a NoOp
          assume CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop); // NOT DONE!!!!!
          assume Inv(v');
      }
      case CompleteSyncStep(syncReqId) => {
        // Discovery of a stable point in the line of updates

        // here uiop is not a NoOp
        assume CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop); // NOT DONE!!!!!
        assume Inv(v');
      }
      case CommitStartStep(seqBoundary) => {
          // Start pushing subperblock to disk
          assert uiop.NoopOp?;

          assert v.program.journal == v'.program.journal;
          assert v.program.betree == v'.program.betree;
          assume I(v) ==  I(v'); // TODO: Here we need to show that the cache's interpretation has not changed

          assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), CrashTolerantMapSpecMod.NoopOp);
          assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);

          EnsureInductive(v, v');

          assert Inv(v');
      }
      case CommitCompleteStep() => {
        // We have a new stable subperblock
        assert uiop.NoopOp?;
        assert v.program.phase.Running?; // believes this

        var sb := v.program.inFlightSuperblock.value;
        assert JournalMachineMod.CommitComplete(v.program.journal, v'.program.journal, v.program.cache, sb.journal);
        assert SplinterTreeMachineMod.CommitComplete(v.program.betree, v'.program.betree, v.program.cache, sb.betree);

        CommitCompleteRefines(v, v', uiop, cacheOps, pstep);

        assert I(v) ==  I(v');
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), CrashTolerantMapSpecMod.NoopOp);
        assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);

        assert Inv(v');
      }
    }

  }

  lemma NextRefines(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp)
    // requires Inv(v)
    // requires ConcreteSystem.Next(v, v', uiop)
    // ensures Inv(v')
    // ensures CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop)
  {
    // cases to anyalze

    // choose a step such that statifieds NextStep
    var step :| ConcreteSystem.NextStep(v, v', uiop, step);

    match step {
      case MachineStep(_) => {
        // This is basically shows refinement for all the program steps
        ProgramMachineStepRefines(v, v', uiop, step);
        assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case DiskInternalStep(step) => {
        assume  CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case CrashStep => {
        // here we need to ensure that I(v) == I(v') -- we need to verify that recovery works here?
        assume  CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case AcceptRequestStep => {
        assume false; // TODO
      }
      case DeliverReplyStep => {
        assume false; // TODO
      }
    }

  }
}
