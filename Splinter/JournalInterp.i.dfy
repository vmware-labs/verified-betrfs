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
  import CrashTolerantMapSpecMod

  predicate DiskSupportsChainLookup(chainLookup: ChainLookup, dv: DiskView, sb: Superblock)
  {
    && chainLookup.ValidForSB(CacheIfc.Variables(dv), sb)
    && chainLookup.Complete()
    && chainLookup.success()
  }

  predicate Invariant(v: Variables, cache: CacheIfc.Variables)
  {
    && v.WF()
    && DiskSupportsChainLookup(v.marshalledLookup, cache.dv, v.CurrentSuperblock())
  }

  // Interpret just the journaled messages
  function IMsgSeq(v: Variables, cache:CacheIfc.Variables) : MsgSeq
    requires v.WF()
  {
    v.marshalledLookup.interp().Concat(TailToMsgSeq(v))
  }

  //////////////////////////////////////////////////////////////////////
  // Interpret an Interp + JournalInterp -> spec Versions
  // This perhaps belongs higher up?
  //////////////////////////////////////////////////////////////////////

  datatype JournalInterp = JournalInterp(msgSeq: MsgSeq, syncReqs: map<CrashTolerantMapSpecMod.SyncReqId, LSN>)
  {
    predicate WF() {
      && msgSeq.WF()
    }

    function SyncReqsAt(lsn: LSN) : set<CrashTolerantMapSpecMod.SyncReqId>
      requires WF()
    {
      set id | id in syncReqs && syncReqs[id] == lsn
    }
    
    function VersionFor(base: InterpMod.Interp, lsn: LSN) : CrashTolerantMapSpecMod.Version
      requires WF()
      requires base.seqEnd == msgSeq.seqStart
      requires msgSeq.seqStart <= lsn <= msgSeq.seqEnd
    {
      // TODO No accounting for v.syncReqs < boundaryLSN; hrmm.
      var mapspec := MapSpecMod.Variables(msgSeq.Truncate(lsn).ApplyToInterp(base));
      var asyncmapspec := CrashTolerantMapSpecMod.async.Variables(mapspec, {}, {}); // TODO um, no reqs & replies!?
      CrashTolerantMapSpecMod.Version(asyncmapspec, SyncReqsAt(lsn))
    }

    function VersionsFromBase(base: InterpMod.Interp) : seq<CrashTolerantMapSpecMod.Version>
      requires WF()
      requires base.seqEnd == msgSeq.seqStart
    {
      var numVersions := msgSeq.Len()+1;  // Can apply zero to Len() messages.
      seq(msgSeq.Len()+1, i requires 0 <= i < numVersions => VersionFor(base, i + msgSeq.seqStart))
    }

    function AsCrashTolerantMapSpec(base: InterpMod.Interp) : CrashTolerantMapSpecMod.Variables
      requires WF()
      requires base.seqEnd == msgSeq.seqStart
    {
      CrashTolerantMapSpecMod.Variables(VersionsFromBase(base), 0)  // 0 is always the stable idx; why do we allow others in spec?
    }
  }

  function I(v: Variables, cache:CacheIfc.Variables) : JournalInterp
    requires v.WF()
  {
    JournalInterp(IMsgSeq(v, cache), v.syncReqs)
  }

  function EmptyVars() : (ev: Variables)
    ensures forall cache :: Invariant(ev, cache)
  {
    Variables(
      0,
      0,
      0,
      0,
      [], // unmarshalledTail
      map[], // syncReqs
      EmptyChainLookup(Superblock(None, 0), 0)
    )
  }

  function SynthesizeRunningVariables(dv: DiskView, sb: Superblock) : (sv: Variables)
    ensures Invariant(sv, CacheIfc.Variables(dv))
  {
    if exists chainLookup :: DiskSupportsChainLookup(chainLookup, dv, sb)
    then
      var chainLookup :| DiskSupportsChainLookup(chainLookup, dv, sb);
      var sv := Variables(
        chainLookup.interp().seqStart,
        chainLookup.interp().seqEnd,
        chainLookup.interp().seqEnd,
        chainLookup.interp().seqEnd,
        [], // unmarshalledTail
        map[], // syncReqs
        chainLookup
      );
      assert chainLookup.ValidForSB(CacheIfc.Variables(dv), sb);
      assert chainLookup.ForSB(sb);
      assert sb.boundaryLSN == chainLookup.interp().seqStart by {
        forall row | row in chainLookup.rows ensures row.sb.boundaryLSN == sb.boundaryLSN {
        }
        assert chainLookup.rows[0].sb.boundaryLSN == chainLookup.interp().seqStart;
      }
      assert sb.freshestCU == sv.FreshestMarshalledCU();
      assert DiskSupportsChainLookup(chainLookup, dv, sv.CurrentSuperblock()) by {
        assert sv.marshalledLookup.ForSB(sv.CurrentSuperblock());
        assert sv.marshalledLookup.ForSB(sv.CurrentSuperblock());
      }
//      assert sv.FreshestMarshalledCU() == sb.freshestCU by {
//        assume false;
//        if sv.marshalledLSN == sv.boundaryLSN {
//          assert sb.freshestCU.None?;
//        } else {
//          assert sb.freshestCU == Some(sv.marshalledLookup.lsnMap()[sv.marshalledLSN-1]);
//        }
//      }
//      assert sv.boundaryLSN == sb.boundaryLSN by {
//        assert chainLookup.interp().seqStart == boundaryLSN;
//        calc {
//          chainLookup.interp().seqStart;
//          Last(chainLookup.rows).sb.boundaryLSN;
//          sb.boundaryLSN;
//        }
//      }
//      calc {
//        sv.CurrentSuperblock();
//        Superblock(sv.FreshestMarshalledCU(), sv.boundaryLSN);
//        sb;
//      }
//      assert chainLookup.ForSB(sb);
      assert Invariant(sv, CacheIfc.Variables(dv));
      sv
    else
      // Eww, the journal on the disk is nonsense!
      EmptyVars()
  }

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
  lemma InternalStepLemma(v: Variables, cache: CacheIfc.Variables, v': Variables, cache': CacheIfc.Variables, cacheOps: CacheIfc.Ops, sk: Skolem)
    requires v.WF()
    requires v'.WF()
    requires DiskViewsEquivalentForSeq(cache.dv, cache'.dv, IReads(cache, v.CurrentSuperblock()))
    requires Invariant(v, cache)
    requires Internal(v, v', cache, cacheOps, sk);
    requires CacheIfc.WritesApplied(cache, cache', cacheOps)
    ensures Invariant(v', cache')
    ensures v.boundaryLSN == v'.boundaryLSN
    ensures v.unmarshalledLSN() == v'.unmarshalledLSN()
    ensures I(v, cache) == I(v', cache')
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

  lemma Framing(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables)
    requires v.WF()
    requires DiskViewsEquivalentForSeq(cache0.dv, cache1.dv, IReads(cache0, v.CurrentSuperblock()))
    ensures I(v, cache0) == I(v, cache1)
  {
//    assume false; // there's a timeout here that seems to point at opaque WFChainInner. That's weird.
    FrameOneChain(cache0, cache1, v.CurrentSuperblock());
  }
}
