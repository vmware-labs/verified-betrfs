// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "SequenceSets.i.dfy"
include "Journal.i.dfy"
include "CacheLemmas.i.dfy"

// The Module that Interprets the Journal.
module JournalInterpMod {

  import opened ValueMessage
  import opened KeyType
  import opened Options
  import opened Sequences
  import opened Maps
  import opened MsgHistoryMod
  import MapSpecMod
  import opened DiskTypesMod
  import opened AllocationMod
  import opened JournalMachineMod
  import opened InterpMod
  import opened SequenceSetsMod
  import CacheLemmasMod

  predicate Invariant(v: Variables, cache: CacheIfc.Variables)
  {
    && v.WF()
    && v.marshalledLookup.ValidForSB(cache, v.CurrentSuperblock())
    && v.marshalledLookup.Complete()
    && v.marshalledLookup.success() // TODO will have to condition this when coming up after a crash; disk may be broken.
  }

  // XXX was ChainAsMsgSeq now v.marshalledLookup.interp

  function SyncReqsAt(v: Variables, lsn: LSN) : set<CrashTolerantMapSpecMod.SyncReqId>
    //requires v.persistentLSN <= lsn < v.unmarshalledLSN()
    //requires v.WF()
  {
    //set syncReqId | v.syncReqs[syncReqId] == lsn //&& (syncReqId in nat)
    set lsns |  v.persistentLSN <= lsns <= lsn
  }

  function UnmarshalledMessageSeq(v: Variables, cache:CacheIfc.Variables) : MsgSeq
    requires v.WF()
  {
    v.marshalledLookup.interp().Concat(TailToMsgSeq(v))
  }

  function InterpFor(v: Variables, cache:CacheIfc.Variables, base: InterpMod.Interp, lsn: LSN) : Interp
    requires v.WF()
    requires Invariant(v, cache)
    requires base.seqEnd == v.boundaryLSN
    requires v.boundaryLSN <= lsn <= v.unmarshalledLSN()
  {
    UnmarshalledMessageSeq(v, cache).Truncate(lsn).ApplyToInterp(base)
  }

   function VersionFor(v: Variables, cache:CacheIfc.Variables, base: InterpMod.Interp, lsn: LSN) : CrashTolerantMapSpecMod.Version
     requires v.WF()
     requires Invariant(v, cache)
     requires base.seqEnd == v.boundaryLSN
     requires v.boundaryLSN <= lsn <= v.unmarshalledLSN() // we only need versions for the journal for the unapplied suffix of entries
   {
     // TODO No accounting for v.syncReqs < boundaryLSN; hrmm.
     var mapspec := MapSpecMod.Variables(InterpFor(v, cache, base, lsn));
     var asyncmapspec := CrashTolerantMapSpecMod.async.Variables(mapspec, {}, {});
     CrashTolerantMapSpecMod.Version(asyncmapspec, SyncReqsAt(v, lsn))
   }

  function Versions(v: Variables, cache:CacheIfc.Variables, base: InterpMod.Interp) : seq<CrashTolerantMapSpecMod.Version>
    requires v.WF()
    requires base.seqEnd == v.boundaryLSN // Can we require this here?
    requires Invariant(v, cache)
   {
     // TODO: check
     var numVersions := v.unmarshalledLSN() - v.boundaryLSN + 1;
     seq(numVersions, i requires 0 <= i < numVersions =>
        var lsn := i + v.boundaryLSN;
        assert v.boundaryLSN <= lsn;
        assert lsn <= v.unmarshalledLSN();
        VersionFor(v, cache, base, lsn)
     )
   }

   // TDODO: may have to lemma for the journal internal step

  function IMNotRunning(cache: CacheIfc.Variables, sb: Superblock, base: InterpMod.Interp) : (iv: CrashTolerantMapSpecMod.Variables)
    requires base.seqEnd == sb.boundaryLSN  // This crash-invariant condition should probably not be a requires; just return nonsense if it fails.
    ensures iv.WF()
  {
    assume false; // this is all nonsense
    var pretendVariables := Variables(sb.boundaryLSN, sb.boundaryLSN, sb.boundaryLSN, sb.boundaryLSN, [], map[], EmptyChainLookup(Superblock(None, 0), 0));
    var versions := Versions(pretendVariables, cache, base);
    CrashTolerantMapSpecMod.Variables(versions, 0) // TODO Sowmya pick up here
  }

  function IM(v: Variables, cache:CacheIfc.Variables, base: InterpMod.Interp)
    : (iv: CrashTolerantMapSpecMod.Variables)
    requires v.WF()
    requires Invariant(v, cache)
    requires base.seqEnd == v.boundaryLSN
    ensures iv.WF()
  {
    assert v.boundaryLSN <= v.unmarshalledLSN(); // Follows from WF & defn unmarshalledLSN
    var versions := Versions(v, cache, base);
    CrashTolerantMapSpecMod.Variables(versions, 0)
  }

  // TODO(jonh): Try porting this from recursive style to Travis' suggested
  // repr-state style (see ReprsAsSets.i.dfy).
  function IReads(cache:CacheIfc.Variables, sb: Superblock) : seq<CU>
  {
    ChainFrom(cache, sb).last().cumulativeReadCUs
  }

  lemma CuInIReads(cl: ChainLookup, idx: nat)
    requires cl.WF()
    requires cl.Chained()
    requires 0 <= idx < |cl.rows|
    requires cl.rows[idx].sb.freshestCU.Some?
    ensures cl.rows[idx].sb.freshestCU.value in cl.last().cumulativeReadCUs
    decreases |cl.rows|
  {
    var cu := cl.rows[idx].sb.freshestCU.value;
    assert cl.Linked(|cl.rows|-1); // trigger
    if idx != |cl.rows|-1 {
      ChainedPrior(cl);
      CuInIReads(cl.DropLast(), idx);
    }
  }
  
  // This lemma dominates UniqueChainLookup.
  lemma FrameOneChainInductive(cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, sb: Superblock, cl0: ChainLookup, cl1: ChainLookup)
    requires cl0.ValidForSB(cache0, sb)
    requires cl1.ValidForSB(cache1, sb)
    requires DiskViewsEquivalentForSeq(cache0.dv, cache1.dv, cl0.last().cumulativeReadCUs)
    requires cl0.last().expectedEnd == cl1.last().expectedEnd
    ensures cl0 == cl1
    decreases |cl0.rows|
  {
    assert cl0.Linked(|cl0.rows|-1);  // trigger
    assert cl0.Linked(|cl0.rows|-1);  // trigger

    if sb.freshestCU.Some? {
      assert sb.freshestCU.value in cl0.last().cumulativeReadCUs; // observe trigger
    }
    assert cl1.Linked(|cl1.rows| - 1);  // observe trigger -- lets us conclude cl1 has ==1 or >1 rows based on FirstRow() properties.

    if 1 < |cl0.rows| {
      ChainedPrior(cl0);
      assert sb.freshestCU.value in cl0.last().cumulativeReadCUs; // observe trigger
      ChainedPrior(cl1);
      var priorSB := cl0.rows[|cl0.rows|-2].sb;
      assert cl1.DropLast().ValidForSB(cache1, priorSB);  // trigger

//      assert cl0.DropLast().last().cumulativeReadCUs <= cl0.last().cumulativeReadCUs; // observe trigger
      FrameOneChainInductive(cache0, cache1, priorSB, cl0.DropLast(), cl1.DropLast()); // recurse
    }
  }

  lemma FrameOneChain(cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, sb: Superblock)
    requires DiskViewsEquivalentForSeq(cache0.dv, cache1.dv, IReads(cache0, sb))
    ensures ChainFrom(cache0, sb) == ChainFrom(cache1, sb)
  {
    var cl0 := ChainFrom(cache0, sb);
    var cl1 := ChainFrom(cache1, sb);
    if sb.freshestCU.Some? {
      CuInIReads(cl0, |cl0.rows|-1);  // triggers DiskViewsEquivalentForSeq
    }
    FrameOneChainInductive(cache0, cache1, sb, cl0, cl1);
    UniqueChainLookup(cache0, cl0, cl1);
  }

  // Add comment about what this supposed to do the TODOS here
  lemma InternalStepLemma(v: Variables, cache: CacheIfc.Variables, v': Variables, cache': CacheIfc.Variables, base: InterpMod.Interp, cacheOps: CacheIfc.Ops, sk: Skolem)
    requires v.WF()
    requires v'.WF()
    requires DiskViewsEquivalentForSeq(cache.dv, cache'.dv, IReads(cache, v.CurrentSuperblock()))
    requires base.seqEnd == v.boundaryLSN
    requires Invariant(v, cache)
    requires Internal(v, v', cache, cacheOps, sk);
    requires CacheIfc.WritesApplied(cache, cache', cacheOps)
    ensures Invariant(v', cache')
    ensures v.boundaryLSN == v'.boundaryLSN
    ensures v.unmarshalledLSN() == v'.unmarshalledLSN()
    ensures IM(v, cache, base) == IM(v', cache', base)
  {
    match sk {
      case AdvanceMarshalledStep(newCU) => {
        var sb := v.marshalledLookup.last().sb;
        var chain := ChainFrom(cache, sb);
        var sb' := Superblock(Some(newCU), v.boundaryLSN);
        var chain' := ChainFrom(cache', sb');

        var priorCU := (v.marshalledLookup.LsnMapDomain(); if v.marshalledLSN == v.boundaryLSN then None else Some(v.lsnMap()[v.marshalledLSN-1]));
        var jr := JournalRecord(TailToMsgSeq(v), priorCU);
        assert CacheIfc.Read(cache', newCU, marshal(jr)) by {
          assert cacheOps[0] == CacheIfc.Write(newCU, marshal(jr)); // observe trigger
          CacheIfc.reveal_ApplyWrites();
        }
        assert chain'.Linked(|chain'.rows| - 1); // trigger: chain' has more than 1 row
        assert chain'.Linked(|chain'.rows|-2);   // trigger

        FrameOneChain(cache, cache', chain'.last().priorSB());
        assert chain'.DropLast().Valid(cache') by { ChainedPrior(chain'); }

        UniqueChainLookup(cache', chain, chain'.DropLast());
      }
      case AdvanceCleanStep(newClean) => {
        assert cache' == cache by { CacheIfc.reveal_ApplyWrites(); }
      }
    }
  }

  lemma Framing(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, base: InterpMod.Interp)
    requires v.WF()
    requires DiskViewsEquivalentForSeq(cache0.dv, cache1.dv, IReads(cache0, v.CurrentSuperblock()))
    requires base.seqEnd == v.boundaryLSN

    // QUESTION: We need to require these right?, Need to figure this out for later
    requires Invariant(v, cache0)
    requires Invariant(v, cache1)
    requires base.seqEnd == v.persistentLSN
    requires v.persistentLSN < v.unmarshalledLSN()
    ensures IM(v, cache0, base) == IM(v, cache1, base)
  {
//    assume false; // there's a timeout here that seems to point at opaque WFChainInner. That's weird.
    FrameOneChain(cache0, cache1, v.CurrentSuperblock());
    // This works --- I'm suspicious -- Sowmya
    calc {
      IM(v, cache0, base);
      IM(v, cache1, base);
    }
  }
}
