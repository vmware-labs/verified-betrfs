// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Journal.i.dfy"
include "JournalInterp.i.dfy"
include "SplinterTree.i.dfy"
include "SplinterTreeInterp.i.dfy"
include "CacheIfc.i.dfy"

include "AsyncDisk.s.dfy"
include "AsyncDiskProgram.s.dfy"
include "IOSystem.s.dfy"
include "ProgramMachine.i.dfy"

module ProgramInterpMod {
  import opened Options
  import opened MessageMod
  import opened InterpMod
  import opened DiskTypesMod
  import opened AllocationMod
  import opened MsgSeqMod
  import AllocationTableMod
  //import JournalMod
  import SplinterTreeInterpMod
  import JournalInterpMod
  import opened ProgramMachineMod

  function ISuperblock(dv: DiskView) : Option<Superblock>
  {
    var bcu0 := CU(0, 0);
    var bcu1 := CU(0, 1);
    if bcu0 in dv && bcu1 in dv
    then
      var sb0 := parseSuperblock(dv[bcu0]);
      var sb1 := parseSuperblock(dv[bcu1]);
      if sb0.Some? && sb1.Some? && sb0.value.serial == sb1.value.serial
      then
        sb0
      else
        None  // Stop! Recovery should ... copy the newer one?
          // well I think I() of that should be the newer one, but we should just
          // not be allowed to write anything until we've got them back in sync.
    else
      None  // silly expression: DV has holes in it
  }

  function ISuperblockReads(dv: DiskView) : seq<CU>
  {
    [ SUPERBLOCK_ADDRESS() ]
  }

  // Program will have a runtime view of what (ghost) alloc each subsystem thinks it's using,
  // and use that to filter the dvs here.
  // Those ghost views will invariantly match the IReads functions of the actual disk -- that is,
  // * if we were to recover after a crash (when the physical alloc is empty), we'd fault in
  // an alloc table for the subsystem.
  // * that alloc table would invariantly match IReads.
  //
  // IM == Interpret as InterpMod
  // TODO NEXT well actually we need a chain of Interps; see CrashTolerantMapSpecMod
  // Journal interprets to a MsgSeq. The not-yet-sb-persistent part of that chain
  // is the set of versions. Yeah we need to put richer interps down in JournalInterp
  // before we try to add them here?
  function IMNotRunning(dv: DiskView) : (iv:CrashTolerantMapSpecMod.Variables)
    ensures iv.WF()
  {
    var pretendCache := CacheIfc.Variables(dv);
    var sb := ISuperblock(dv);
    if sb.Some?
    then
      var splinterTreeInterp := SplinterTreeInterpMod.IMNotRunning(pretendCache, sb.value.betree);
      var journalInterp := JournalInterpMod.IMNotRunning(pretendCache, sb.value.journal, splinterTreeInterp);
      journalInterp
    else
      CrashTolerantMapSpecMod.Empty()
  }

  function IMRunning(v: Variables) : (iv:CrashTolerantMapSpecMod.Variables)
    ensures iv.WF()
  {
    var sb := ISuperblock(v.cache.dv);
    if sb.Some?
    then
      var splinterTreeInterp := SplinterTreeInterpMod.IMStable(v.cache, sb.value.betree);
      var journalInterp := JournalInterpMod.IM(v.journal, v.cache, splinterTreeInterp);
      journalInterp
    else
      CrashTolerantMapSpecMod.Empty()
  }

  function IM(v: Variables) : (iv:CrashTolerantMapSpecMod.Variables)
  {
    if v.phase.Running?
    then IMRunning(v)
    else IMNotRunning(v.cache.dv) // fresh start or recovered
  }

  function IMReads(v: Variables) : seq<CU> {
    var sbreads := ISuperblockReads(v.cache.dv);
    var sb := ISuperblock(v.cache.dv);
    if sb.Some?
    then
      sbreads
        + JournalInterpMod.IReads(v.journal, v.cache, sb.value.journal)
        + SplinterTreeInterpMod.IReads(v.betree, v.cache, sb.value.betree)
    else
      sbreads
  }

  function IReads(v: Variables) : seq<CU> {
    IMReads(v)
  }

  lemma Framing(v0: Variables, v1: Variables)
    requires DiskViewsEquivalentForSet(v0.cache.dv, v1.cache.dv, IReads(v0))
    requires v0.betree == v1.betree
    requires v0.journal == v1.journal
    ensures IM(v0) == IM(v1)
  {
    assert ISuperblock(v0.cache.dv) == ISuperblock(v1.cache.dv);
    var sb := ISuperblock(v0.cache.dv);
    if sb.Some? {
      SplinterTreeInterpMod.Framing(v0.betree, v0.cache, v1.cache, sb.value.betree);
      var betreeInterp := SplinterTreeInterpMod.IMStable(v0.cache, sb.value.betree);
      JournalInterpMod.Framing(v0.journal, v0.cache, v1.cache, betreeInterp);
    }
  }

  // Next step is to write the refinement proof, using obligation placeholders
  // in Betree & Journal so we can see the outer structure -- including the
  // framing argument -- early.
  // Here's a quick and dirty approximation: it ignores crashes, but lets us
  // get to the framing issue right away.

  predicate Inv(v: Variables)
  {
    && AllocsDisjoint(v)
  }

  // Not gonna think about Init in this fakey little simulation, since we want
  // mkfs init (behavior start), not program init (crash recovery).
  lemma InvNext(v: Variables, v': Variables, uiop: UIOp, dop: DiskOp)
    requires Inv(v)
    requires Next(v, v', uiop, dop)
    ensures Inv(v')
  {
  }

}

/*
Okay, so the magic is going to be that
- most of the time when we change a block in RAM we'll prove that it's
  not in use in any other view
  - that'll depend on an invariant between the allocation table
    and the IReads functions
  - And we'll need a proof that, if IReads doesn't change, I doesn't
    change, of course.
- when we write a non-superblock back to disk, we inherit that no-change
  property; the persistent view doesn't change because the thing
  we wrote back was dirty and hence outside of the IReads of the
  persistent view.
- when we update the superblock, we're creating a frozen view.
- when we write a superblock back, it's easy again, because the persistent
  view just vanishes, replaced by the frozen view.
  The vanishing old persistent view implicitly creates some free nodes,
  which can be detected because the available nodes are computed at
  runtime by reading the active AllocationTables, and one just became
  empty.
  (that is, the union of allocationTables will cover the IReads sets.)
*/
