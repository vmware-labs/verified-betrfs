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
include "../lib/Base/KeyType.s.dfy"


module ProgramInterpMod {
  import opened Options
  import opened ValueMessage
  import opened KeyType
  import opened InterpMod
  import opened DiskTypesMod
  import opened AllocationMod
  import opened MsgHistoryMod
  import AllocationTableMod
  //import JournalMod
  import SplinterTreeInterpMod
  import JournalInterpMod
  import opened ProgramMachineMod

  function ISuperblock(dv: DiskView) : Option<Superblock>
  {
    if (
      var cu0 := SUPERBLOCK_ADDRESSES()[0];
      && cu0 in dv
      && var sb0 := parseSuperblock(dv[cu0]);
      && (forall cu | cu in SUPERBLOCK_ADDRESSES() ::
          && cu in dv
          && sb0.Some?
          && parseSuperblock(dv[cu]) == sb0)
      )
    then
      // all the superblocks are present, parseable, and match each other.
      parseSuperblock(dv[SUPERBLOCK_ADDRESSES()[0]])
    else
      // Stop! Recovery should ... copy the newer one?
      // well I think I() of that should be the newer one, but we should just
      // not be allowed to write anything until we've got them back in sync.
      None
  }

  function ISuperblockReads(dv: DiskView) : seq<CU>
  {
    SUPERBLOCK_ADDRESSES()
  }

  predicate Invariant(v: Variables)
  {
    && v.WF()
    && ISuperblock(v.cache.dv).Some?
//    && v.journal.boundaryLSN == v.betree.nextSeq
  }

// TODO deleteme
//  // Program will have a runtime view of what (ghost) alloc each subsystem thinks it's using,
//  // and use that to filter the dvs here.
//  // Those ghost views will invariantly match the IReads functions of the actual disk -- that is,
//  // * if we were to recover after a crash (when the physical alloc is empty), we'd fault in
//  // an alloc table for the subsystem.
//  // * that alloc table would invariantly match IReads.
//  //
//  // IM == Interpret as InterpMod
//  // TODO NEXT well actually we need a chain of Interps; see CrashTolerantMapSpecMod
//  // Journal interprets to a MsgSeq. The not-yet-sb-persistent part of that chain
//  // is the set of versions. Yeah we need to put richer interps down in JournalInterp
//  // before we try to add them here?
//  function IMNotRunning(dv: DiskView) : (iv:CrashTolerantMapSpecMod.Variables)
//    requires NotRunningInvariant(dv)
//    ensures iv.WF()
//  {
//    var pretendCache := CacheIfc.Variables(dv);
//    var sb := ISuperblock(dv);
//    var splinterTreeInterp := SplinterTreeInterpMod.IMNotRunning(pretendCache, sb.value.betree);
//    var journalInterp := JournalInterpMod.IMNotRunning(pretendCache, sb.value.journal, splinterTreeInterp);
//    journalInterp
//  }

  function IMRunning(v: Variables) : (iv:CrashTolerantMapSpecMod.Variables)
    requires Invariant(v)
    requires v.phase.Running?
    ensures iv.WF()
  {
    var sb := ISuperblock(v.cache.dv).value;
    var splinterTreeInterp := SplinterTreeInterpMod.IM(v.cache, v.betree);
    var journalInterp := JournalInterpMod.I(v.journal, v.cache).AsCrashTolerantMapSpec(splinterTreeInterp);
    journalInterp
  }

  // Dummy values for when we can't decode the disk. Not actually used in real behaviors
  // since the Invariant keeps us from needing it; used to complete definitions when
  // knowledge of the Invariant isn't at hand.
  function EmptyVars() : (ev: Variables)
    ensures Invariant(ev)
  {
    var sb := Superblock(
      0,
      JournalMachineMod.MkfsSuperblock(),
      SplinterTreeMachineMod.MkfsSuperblock(TREE_ROOT_ADDRESS()));
    var sbPage := marshalSuperblock(sb);
    var fakeDv := map cu | cu in CUsInDisk() :: sbPage;
    var v := Variables(
      Running,
      sb,
      CacheIfc.Variables(fakeDv),
      JournalInterpMod.EmptyVars(),
      SplinterTreeInterpMod.EmptyVars(sb.betree),
      None
      );
    v
  }

  // Any given view of the disk implies some set of Variables that we'd get if we were
  // to Init from that disk image.
  function SynthesizeRunningVariables(dv: DiskView) : (sv: Variables)
    ensures Invariant(sv)
  {
    var sb := ISuperblock(dv);
    if sb.Some?
    then
      Variables(
        Running,
        sb.value,
        CacheIfc.Variables(dv),
        JournalInterpMod.SynthesizeRunningVariables(dv, sb.value.journal),
        SplinterTreeInterpMod.SynthesizeRunningVariables(dv, sb.value.betree),
        None
        )
    else
      EmptyVars()
  }

  function IM(v: Variables, dv: DiskView) : (iv:CrashTolerantMapSpecMod.Variables)
    requires v.WF()
    ensures iv.WF()
  {
    if !Invariant(v)  // keep Invariant out of requires by providing a dummy answer.
    then
      CrashTolerantMapSpecMod.InitState()
    else if !v.phase.Running?
      // Until we're running, there's no state in memory that's not also on the
      // disk.
    then IMRunning(SynthesizeRunningVariables(dv))
      // Once Program is running, stitch together the ephemeral state of the journal & tree.
      // Generally they'll agree, but during recovery, the journal may be ahead of the tree.
    else IMRunning(v)
  }

  function IMReads(v: Variables) : seq<CU> {
    var sbreads := ISuperblockReads(v.cache.dv);
    var sb := ISuperblock(v.cache.dv);
    if sb.Some?
    then
      sbreads
        + JournalInterpMod.IReads(v.cache, sb.value.journal)
        + SplinterTreeMachineMod.IReadsSeq(v.betree, v.cache)
    else
      sbreads
  }

  function IReads(v: Variables) : seq<CU> {
    IMReads(v)
  }

  lemma Framing(v0: Variables, v1: Variables)
    requires v0.WF()
    requires v1.WF()
    requires DiskViewsEquivalentForSeq(v0.cache.dv, v1.cache.dv, IReads(v0))
    requires v0.betree == v1.betree
    requires v0.journal == v1.journal
    ensures IMRunning(v0) == IMRunning(v1)
  {
    assert CU(0, 0) in IReads(v0);
    assert CU(0, 1) in IReads(v0);
    assert ISuperblock(v0.cache.dv) == ISuperblock(v1.cache.dv);
    var sb := ISuperblock(v0.cache.dv);
    if sb.Some? {
      assert IReads(v0) == ISuperblockReads(v0.cache.dv)
        + JournalInterpMod.IReads(v0.cache, sb.value.journal)
        + SplinterTreeMachineMod.IReadsSeq(v0.betree, v0.cache);
      assert forall cu | cu in SplinterTreeMachineMod.IReads(v0.betree, v0.cache) :: cu in IReads(v0);
      assert DiskViewsEquivalent(v0.cache.dv, v1.cache.dv, SplinterTreeMachineMod.IReads(v0.betree, v0.cache));
      SplinterTreeInterpMod.Framing(v0.betree, v0.cache, v1.cache);
      var betreeInterp := SplinterTreeInterpMod.IMStable(v0.cache, sb.value.betree);

      assert ISuperblock(v0.cache.dv).value.journal == v0.journal.CurrentSuperblock();
      assert forall cu | cu in JournalInterpMod.IReads(v0.cache, v0.journal.CurrentSuperblock()) :: cu in IReads(v0);
      assert DiskViewsEquivalentForSeq(v0.cache.dv, v1.cache.dv, JournalInterpMod.IReads(v0.cache, v0.journal.CurrentSuperblock()));
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
