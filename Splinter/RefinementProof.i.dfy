include "IOSystem.s.dfy"
include "ProgramInterp.i.dfy"
include "ProofObligations.s.dfy"
include "JournalInterp.i.dfy"
include "BetreeInvariants.i.dfy"

module Proof refines ProofObligations {
  import opened DiskTypesMod
  import MapSpecMod
  import InterpMod

  import ConcreteSystem = VeribetrIOSystem // ProgramMachineMod is imported here
  import JournalMachineMod
  import BetreeMachineMod

  import JournalInterpMod
  import ProgramInterpMod
  import BetreeInterpMod
  import BetreeInvariantMod

  import CacheIfc

  function I(v: ConcreteSystem.Variables) : CrashTolerantMapSpecMod.Variables
  {
    ProgramInterpMod.IM(v.program)
  }

  // NOTE: These are all program invariants. Maybe we should change the argument
  predicate Inv(v: ConcreteSystem.Variables)
  {
    // These invariants over the splinter tree / journal only have to hold when the system is recovered/inited and in the running phase
    &&  v.program.phase.Running? ==> BetreeInterpMod.IMStable(v.program.cache, v.program.stableSuperblock.betree).seqEnd == v.program.journal.persistentLSN
    &&  v.program.phase.Running? ==> JournalInterpMod.Invariant(v.program.journal, v.program.cache)
    //&& BetreeInvariantMod.Invariant(v.program.cache, v.program) // TODO: Maybe have to add a betree invariant
  }

  // Remember that this is the init of a p
  lemma InitRefines(v: ConcreteSystem.Variables)
    //requires ConcreteSystem.Init(v)
    //ensures CrashTolerantMapSpecMod.Init(I(v))
    //ensures Inv(v)
  {
    // assert !v.program.phase.Running?;
    // var sb := ProgramInterpMod.ISuperblock(v.program.cache.dv);
    // assert !sb.Some?;
    // assert I(v) == CrashTolerantMapSpecMod.Empty();
    //
    // // Sowmya: We might need to rewrite the invariants for this?
    // assert Inv(v); // Does not believe this
  }


  // This is complicated
  lemma BetreeInternalRefined(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp, cacheOps : CacheIfc.Ops, pstep: ConcreteSystem.P.Step, sk: BetreeMachineMod.Skolem)
      requires Inv(v)
      requires v.program.WF()

      requires ConcreteSystem.P.NextStep(v.program, v'.program, uiop, cacheOps, pstep)
      requires pstep == ConcreteSystem.P.BetreeInternalStep(sk)

      // Is this a problem with using imports?
      ensures Inv(v')
      ensures BetreeInterpMod.IM(v.program.cache, v.program.betree) ==
       BetreeInterpMod.IM(v'.program.cache, v'.program.betree)
  {
    BetreeInterpMod.Framing(v.program.betree, v.program.cache, v'.program.cache, v.program.stableSuperblock.betree);
    assert v.program.betree.nextSeq == v'.program.betree.nextSeq;

    // Need to fix this later
    assume BetreeInterpMod.IM(v.program.cache, v.program.betree).mi ==
     BetreeInterpMod.IM(v'.program.cache, v'.program.betree).mi; // doesn't believe this -- Might need to finish ValidLookup for this?

    assert BetreeInterpMod.IM(v.program.cache, v.program.betree) ==
     BetreeInterpMod.IM(v'.program.cache, v'.program.betree);
  }

  lemma JournalInternalRefined(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp, cacheOps : CacheIfc.Ops, pstep: ConcreteSystem.P.Step, sk: JournalMachineMod.Skolem)
    // Requires needed for IM to work
    requires v.program.WF()
    requires Inv(v)

    // Actual requires
    requires ConcreteSystem.P.NextStep(v.program, v'.program, uiop, cacheOps, pstep)
    requires pstep == ConcreteSystem.P.JournalInternalStep(sk)

    // base should be stable betree in disk.
    ensures Inv(v')
    ensures JournalInterpMod.IM(v.program.journal, v.program.cache, v.program.stableSuperblock.journal, BetreeInterpMod.IMStable(v.program.cache, v.program.stableSuperblock.betree)) ==
    JournalInterpMod.IM(v'.program.journal, v'.program.cache, v'.program.stableSuperblock.journal, BetreeInterpMod.IMStable(v'.program.cache, v'.program.stableSuperblock.betree))
  {

    // needs Some framing argument around DiskViewsEquivalentForSet
    // TODO: check this
    BetreeInvariantMod.StableFraming(v.program.betree, v.program.cache, v'.program.cache, v.program.stableSuperblock.betree);

    // XXXX=== TODO: var some of these
    // the superblock is the same
    assert v'.program.stableSuperblock == v.program.stableSuperblock;

    //assert BetreeInterpMod.IMStable(v.program.cache, v.program.stableSuperblock.betree) == BetreeInterpMod.IMStable(v'.program.cache, v'.program.stableSuperblock.betree);

    // Only thing new is the journal -- make a lemma journal on Internal step
    JournalInterpMod.InternalStepLemma(v.program.journal, v.program.cache, v'.program.journal, v'.program.cache,  v.program.stableSuperblock.journal, BetreeInterpMod.IMStable(v.program.cache, v.program.stableSuperblock.betree));

    assert JournalInterpMod.IM(v.program.journal, v.program.cache, v.program.stableSuperblock.journal, BetreeInterpMod.IMStable(v.program.cache, v.program.stableSuperblock.betree)) ==
      JournalInterpMod.IM(v'.program.journal, v'.program.cache, v'.program.stableSuperblock.journal, BetreeInterpMod.IMStable(v'.program.cache, v'.program.stableSuperblock.betree));
  }

  lemma PutRefines(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp, cacheOps : CacheIfc.Ops, pstep: ConcreteSystem.P.Step, sk: BetreeMachineMod.Skolem)
    // Requires needed for IM to work
    requires v.program.WF()
    requires Inv(v)
    requires Inv(v')

    // Actual requires
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

  // CrashTolerantMapSpecMod : OP1 OP2 ReqSync NOOP ..            AsyncCommit ... Nop      Nop  ..                 SyncComplete
  // PROGRAM :                 P1 P2      ....                    write hits Disk   Program discovers commit

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
        assume CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case QueryStep(key, val, sk) => {

        // Need to leverage Lookup here
        assume CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case PutStep(sk) => {
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
          assume CrashTolerantMapSpecMod.NextStep(I(v), I(v'), CrashTolerantMapSpecMod.NoopOp);
          assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);  // believes this i think
      }
      case ReqSyncStep(syncReqId) => {

          // here uiop is not a NoOp
          assume CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case CompleteSyncStep(syncReqId) => {
        // Discovery of a stable point in the line of updates

        // here uiop is not a NoOp
        assume CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case CommitStartStep(seqBoundary) => {
          // Start pushing subperblock to disk
          assert uiop.NoopOp?;
          //assert I(v) ==  I(v');
          assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), CrashTolerantMapSpecMod.NoopOp);
          assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case CommitCompleteStep() => {
        // We have a new stable subperblock
        assert uiop.NoopOp?;
        assert I(v) ==  I(v');
        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), CrashTolerantMapSpecMod.NoopOp);
        assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
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
    }

  }
}
