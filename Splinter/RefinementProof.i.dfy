include "IOSystem.s.dfy"
include "ProgramInterp.i.dfy"
include "ProofObligations.s.dfy"
include "JournalInterp.i.dfy"
include "SplinterTreeInvariants.i.dfy"
include "CacheLemmas.i.dfy"

module VeribetrIOSystem refines IOSystem {
  import P = ProgramMachineMod
}

module Proof refines ProofObligations {
  import opened DiskTypesMod
  import MapSpecMod
  import InterpMod

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
    ProgramInterpMod.IM(v.program)
  }

  // NOTE: These are all program invariants. Maybe we should change the argument
  predicate Inv(v: ConcreteSystem.Variables)
  {
    && v.program.WF()
    && !v.program.phase.SuperblockUnknown? ==> ( // These invariants over the splinter tree / journal only have to hold when the system is recovered/inited and in the running phase
              && JournalInterpMod.Invariant(v.program.journal, v.program.cache)

              // ties together the updates flowing from the journal to the tree
              && SplinterTreeInterpMod.IMStable(v.program.cache, v.program.stableSuperblock.betree).seqEnd == v.program.journal.boundaryLSN
            )
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


  // This is complicated
  lemma BetreeInternalRefined(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp, cacheOps : CacheIfc.Ops, pstep: ConcreteSystem.P.Step, sk: SplinterTreeMachineMod.Skolem)
      requires Inv(v)
      requires v.program.WF()

      requires ConcreteSystem.P.NextStep(v.program, v'.program, uiop, cacheOps, pstep)
      requires pstep == ConcreteSystem.P.BetreeInternalStep(sk)

      // Is this a problem with using imports?
      ensures Inv(v')
      ensures SplinterTreeInterpMod.IM(v.program.cache, v.program.betree) ==
       SplinterTreeInterpMod.IM(v'.program.cache, v'.program.betree)
  {
    SplinterTreeInterpMod.Framing(v.program.betree, v.program.cache, v'.program.cache, v.program.stableSuperblock.betree);
    assert v.program.betree.nextSeq == v'.program.betree.nextSeq;

    // Need to fix this later
    assume SplinterTreeInterpMod.IM(v.program.cache, v.program.betree).mi ==
     SplinterTreeInterpMod.IM(v'.program.cache, v'.program.betree).mi; // doesn't believe this -- Might need to finish ValidLookup for this?

    assert SplinterTreeInterpMod.IM(v.program.cache, v.program.betree) ==
     SplinterTreeInterpMod.IM(v'.program.cache, v'.program.betree);

    EnsureInductive(v, v');
  }

  lemma JournalInternalRefined(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp, cacheOps : CacheIfc.Ops, pstep: ConcreteSystem.P.Step, sk: JournalMachineMod.Skolem)
    // The super block has to be known for us to take a valid JournalInternal step
    requires !v.program.phase.SuperblockUnknown?
    // Requires needed for IM to work
    requires Inv(v)


    // Actual requires
    requires ConcreteSystem.P.NextStep(v.program, v'.program, uiop, cacheOps, pstep)
    requires pstep == ConcreteSystem.P.JournalInternalStep(sk)

    // base should be stable betree in disk.
    ensures !v'.program.phase.SuperblockUnknown? // QUESTION : Should this be an ensures or requires
    ensures Inv(v')
    ensures JournalInterpMod.IM(v.program.journal, v.program.cache, SplinterTreeInterpMod.IMStable(v.program.cache, v.program.stableSuperblock.betree)) ==
    JournalInterpMod.IM(v'.program.journal, v'.program.cache, SplinterTreeInterpMod.IMStable(v'.program.cache, v'.program.stableSuperblock.betree))
  {

    // needs Some framing argument around DiskViewsEquivalentForSet
    // TODO: check this
    SplinterTreeInvariantMod.StableFraming(v.program.betree, v.program.cache, v'.program.cache, v.program.stableSuperblock.betree);

    // XXXX=== TODO: var some of these
    // the superblock is the same
    assume  !v'.program.phase.SuperblockUnknown? ;
    assert v'.program.stableSuperblock == v.program.stableSuperblock;
    EnsureInductive(v, v');

    //assert BetreeInterpMod.IMStable(v.program.cache, v.program.stableSuperblock.betree) == BetreeInterpMod.IMStable(v'.program.cache, v'.program.stableSuperblock.betree);

    // Only thing new is the journal -- make a lemma journal on Internal step
    JournalInterpMod.InternalStepLemma(v.program.journal, v.program.cache, v'.program.journal, v'.program.cache,  v.program.stableSuperblock.journal, SplinterTreeInterpMod.IMStable(v.program.cache, v.program.stableSuperblock.betree), cacheOps, sk);

    assert JournalInterpMod.IM(v.program.journal, v.program.cache, SplinterTreeInterpMod.IMStable(v.program.cache, v.program.stableSuperblock.betree)) ==
      JournalInterpMod.IM(v'.program.journal, v'.program.cache, SplinterTreeInterpMod.IMStable(v'.program.cache, v'.program.stableSuperblock.betree));


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

    assert sbOld.None? ==> ( ProgramInterpMod.IMRunning(v.program) == CrashTolerantMapSpecMod.Empty());
    assert sbNew.None? ==> ( ProgramInterpMod.IMRunning(v'.program) == CrashTolerantMapSpecMod.Empty());
    assert sbOld.None? ==> sbNew.None?; // cuz we're at a commit step?

    assume SplinterTreeInterpMod.IMStable(v.program.cache, v.program.stableSuperblock.betree) ==
     SplinterTreeInterpMod.IMStable(v'.program.cache, v'.program.stableSuperblock.betree);

    var splinterTreeInterp := SplinterTreeInterpMod.IMStable(v'.program.cache, v'.program.stableSuperblock.betree);

    assume JournalInterpMod.IM(v.program.journal, v.program.cache, splinterTreeInterp) ==
     JournalInterpMod.IM(v'.program.journal, v'.program.cache,  splinterTreeInterp);


    // hmm.... doesn't believe this 
    assert ProgramInterpMod.IMRunning(v.program) ==  ProgramInterpMod.IMRunning(v'.program);
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
    // Here we need talk about the journal
    assert CrashTolerantMapSpecMod.Operate(I(v), I(v'), uiop.baseOp);

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
    assert CrashTolerantMapSpecMod.Operate(I(v), I(v'), uiop.baseOp);

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

        assert pstep == ConcreteSystem.P.JournalInternalStep(sk);
        JournalInternalRefined(v, v', uiop, cacheOps, pstep, sk);

        var sb := ProgramInterpMod.ISuperblock(v.program.cache.dv);
        if sb.Some? {} // TRIGGER

        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), CrashTolerantMapSpecMod.NoopOp); // WITNESS

      }
      case BetreeInternalStep(sk) => {
          // TODO: there's lots to do here and we need to finish the betree
          BetreeInternalRefined(v, v', uiop, cacheOps, pstep, sk);

          var sb := ProgramInterpMod.ISuperblock(v.program.cache.dv);
          if sb.Some? {} // TRIGGER

          assert uiop.NoopOp?;
          assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), CrashTolerantMapSpecMod.NoopOp); // NOT DONE!!!!!
          assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);  // believes this i think
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
  // ensures CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop)
  //requires JournalInterpMod.Invariant(v.program.journal, v.program.cache)
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
