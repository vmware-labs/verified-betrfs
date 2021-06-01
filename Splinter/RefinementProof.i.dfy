include "IOSystem.s.dfy"
include "ProgramInterp.i.dfy"
include "ProofObligations.s.dfy"
include "JournalInterp.i.dfy"

module VeribetrIOSystem refines IOSystem {
  import P = ProgramMachineMod
}

module Proof refines ProofObligations {
  import opened DiskTypesMod
  import MapSpecMod
  import InterpMod
  import ProgramInterpMod
  import ConcreteSystem = VeribetrIOSystem
  import JournalMachineMod
  import BetreeMachineMod
  import JournalInterpMod


  import BetreeInterpMod

  import CacheIfc

  function I(v: ConcreteSystem.Variables) : CrashTolerantMapSpecMod.Variables
  {
    ProgramInterpMod.IM(v.program)
  }

  predicate Inv(v: ConcreteSystem.Variables)
  {
    true
  }

  // Remember that this is the init of a p
  lemma InitRefines(v: ConcreteSystem.Variables)
//    requires ConcreteSystem.Init(v)
    ensures CrashTolerantMapSpecMod.Init(I(v))
  {
    //assert !v.program.phase.Running?;
    //var sb := ProgramInterpMod.ISuperblock(v.program.cache.dv);
    //assert !sb.Some?;
    //assert I(v) == CrashTolerantMapSpecMod.Empty();
  }

  lemma InvInductive(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp)
//    requires ConcreteSystem.Inv(v)
//    requires ConcreteSystem.Next(v, v')
//    ensures ConcreteSystem.Inv(v')
  {}

  lemma BetreeInternalRefined(v: ConcreteSystem.P.Variables, v': ConcreteSystem.P.Variables, uiop: ConcreteSystem.UIOp, cacheOps : CacheIfc.Ops, pstep: ConcreteSystem.P.Step, sk: BetreeMachineMod.Skolem)
      requires ConcreteSystem.P.NextStep(v, v', uiop, cacheOps, pstep)
      requires pstep == ConcreteSystem.P.BetreeInternalStep(sk)
      // Is this a problem with using imports?
      ensures BetreeInterpMod.IM(v.cache, v.betree) ==
       BetreeInterpMod.IM(v'.cache, v'.betree)
  {

  }

  lemma PutRefines(v: ConcreteSystem.P.Variables, v': ConcreteSystem.P.Variables, uiop: ConcreteSystem.UIOp, cacheOps : CacheIfc.Ops, pstep: ConcreteSystem.P.Step, sk: JournalMachineMod.Skolem)
    // Requires needed for IM to work
    requires v.WF()
    requires JournalInterpMod.Invariant(v.journal, v.cache)
    requires JournalInterpMod.Invariant(v'.journal, v'.cache)
    requires BetreeInterpMod.IM(v.cache, v.betree).seqEnd == v.journal.persistentLSN
    requires BetreeInterpMod.IM(v'.cache, v'.betree).seqEnd == v'.journal.persistentLSN
    // Actual requires
    requires ConcreteSystem.P.NextStep(v, v', uiop, cacheOps, pstep)
    requires pstep == ConcreteSystem.P.JournalInternalStep(sk)
    ensures JournalInterpMod.IM(v.journal, v.cache, v.stableSuperblock.journal, BetreeInterpMod.IM(v.cache, v.betree)) ==
      JournalInterpMod.IM(v'.journal, v'.cache, v'.stableSuperblock.journal, BetreeInterpMod.IM(v'.cache, v'.betree))
  {
  }

  lemma JournalInternalRefined(v: ConcreteSystem.P.Variables, v': ConcreteSystem.P.Variables, uiop: ConcreteSystem.UIOp, cacheOps : CacheIfc.Ops, pstep: ConcreteSystem.P.Step, sk: JournalMachineMod.Skolem)
    // Requires needed for IM to work
    requires v.WF()
    requires JournalInterpMod.Invariant(v.journal, v.cache)
    requires JournalInterpMod.Invariant(v'.journal, v'.cache)
    requires BetreeInterpMod.IM(v.cache, v.betree).seqEnd == v.journal.persistentLSN
    requires BetreeInterpMod.IM(v'.cache, v'.betree).seqEnd == v'.journal.persistentLSN
    // Actual requires
    requires ConcreteSystem.P.NextStep(v, v', uiop, cacheOps, pstep)
    requires pstep == ConcreteSystem.P.JournalInternalStep(sk)
    ensures JournalInterpMod.IM(v.journal, v.cache, v.stableSuperblock.journal, BetreeInterpMod.IM(v.cache, v.betree)) ==
      JournalInterpMod.IM(v'.journal, v'.cache, v'.stableSuperblock.journal, BetreeInterpMod.IM(v'.cache, v'.betree))
  {

    // needs Some framing argument around DiskViewsEquivalentForSet
    BetreeInterpMod.Framing(v.betree, v.cache, v'.cache, v.stableSuperblock.betree);

    // XXXX=== TODO: var some of these

    assert BetreeInterpMod.IM(v.cache, v.betree) == BetreeInterpMod.IM( v'.cache, v'.betree);

    // the superblock is the same
    assert v'.stableSuperblock == v.stableSuperblock;

    // Only thing new is the journal -- make a lemma journal on Internal step
    JournalInterpMod.InternalStepLemma(v.journal, v.cache, v'.journal, v'.cache,  v.stableSuperblock.journal, BetreeInterpMod.IM(v.cache, v.betree));

    assert JournalInterpMod.IM(v.journal, v.cache, v.stableSuperblock.journal, BetreeInterpMod.IM(v.cache, v.betree)) ==
      JournalInterpMod.IM(v'.journal, v'.cache, v'.stableSuperblock.journal, BetreeInterpMod.IM(v'.cache, v'.betree));
  }

// This is a ghost method
  lemma MachineStepRefines(v: ConcreteSystem.Variables, v': ConcreteSystem.Variables, uiop: ConcreteSystem.UIOp, step : ConcreteSystem.Step)
    requires Inv(v)
    // TODO: should probably take the invariant out of journalInterp
    requires JournalInterpMod.Invariant(v.program.journal, v.program.cache)
    requires JournalInterpMod.Invariant(v'.program.journal, v'.program.cache) // should be an ensures?
    requires ConcreteSystem.Next(v, v', uiop)
    requires ConcreteSystem.NextStep(v, v', uiop, step)
    requires step.MachineStep?
    ensures CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop)
  {
     var cacheOps, pstep :| ConcreteSystem.P.NextStep(v.program, v'.program, uiop, cacheOps, pstep);
    match pstep {
      case RecoverStep(puts, newbetree) => {

        assume CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case QueryStep(key, val, sk) => {

        assume CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case PutStep(sk) => {

        PutRefines(v.program, v'.program, uiop, cacheOps, pstep, sk);
        assume CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case JournalInternalStep(sk) => {

        assert pstep == ConcreteSystem.P.JournalInternalStep(sk);
        JournalInternalRefined(v.program, v'.program, uiop, cacheOps, pstep, sk);

        var sb := ProgramInterpMod.ISuperblock(v.program.cache.dv);
        if sb.Some? {} // TRIGGER

        assert CrashTolerantMapSpecMod.NextStep(I(v), I(v'), CrashTolerantMapSpecMod.NoopOp); // WITNESS

      }
      case BetreeInternalStep(sk) => {
          BetreeInternalRefined(v.program, v'.program, uiop, cacheOps, pstep, sk);

          //

          assume CrashTolerantMapSpecMod.NextStep(I(v), I(v'), CrashTolerantMapSpecMod.NoopOp);
          assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);  // believes this i think
      }
      case ReqSyncStep(syncReqId) => {

          assume CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case CompleteSyncStep(syncReqId) => {
        assume CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case CommitStartStep(seqBoundary) => {

          assume CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case CommitCompleteStep() => {

          assume CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
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
          MachineStepRefines(v, v', uiop, step);
          assert CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
        }
      case DiskInternalStep(step) => {
          assume  CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
      case CrashStep => {
        assume  CrashTolerantMapSpecMod.Next(I(v), I(v'), uiop);
      }
    }

  }
}
