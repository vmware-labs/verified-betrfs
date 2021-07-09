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

  function FreshestMarshalledCU(v: Variables) : Option<CU>
    requires v.WF()
  {
    if v.marshalledLSN == v.boundaryLSN
    then None
    else Some(v.lsnToCU[v.marshalledLSN-1])
  }

  // This is the superblock that v would use if it all the marshalled stuff were clean
  function CurrentSuperblock(v: Variables) : Superblock
    requires v.WF()
  {
    Superblock(FreshestMarshalledCU(v), v.boundaryLSN)
  }

  predicate Invariant(v: Variables, cache: CacheIfc.Variables)
  {
    && v.WF()
    && var optChain := ChainFrom(cache.dv, CurrentSuperblock(v)).chain;
    && optChain.Some?
    && ValidJournalChain(cache.dv, optChain.value)
    // Superblocks says chain ends where variables says it should
    && v.marshalledLSN == (
        if |optChain.value.recs|==0
        then v.boundaryLSN
        else optChain.value.recs[0].messageSeq.seqEnd
      )
  }

  // Interpret the chain of marshalled LSNs plus the unmarshalledTail as a MsgSeq
  function ChainAsMsgSeq(v: Variables, cache:CacheIfc.Variables) : (result : MsgSeq)
    requires v.WF()
    requires Invariant(v, cache)
    ensures result.WF()
    ensures result.IsEmpty() ==> v.boundaryLSN == v.unmarshalledLSN()
    ensures !result.IsEmpty() ==> result.seqEnd == v.unmarshalledLSN()
    ensures !result.IsEmpty() ==> v.boundaryLSN == result.seqStart
  {
    // chain has all the marshalled messages
    var chain := ChainFrom(cache.dv, CurrentSuperblock(v)).chain.value;

    // tail has all the unmarshalled messages
    var tailMsgs := TailToMsgSeq(v);

    // we need to return all the messages in the journal. So let's join them together
    assert !chain.interp.IsEmpty() && !tailMsgs.IsEmpty() ==>
      chain.interp.seqEnd == tailMsgs.seqStart by {
      if !chain.interp.IsEmpty() && !tailMsgs.IsEmpty() {
        calc {
          chain.interp.seqEnd;
          chain.recs[0].messageSeq.seqEnd;
          v.marshalledLSN;
          tailMsgs.seqStart;
        }
      }
    }
    var result := chain.interp.Concat(tailMsgs);
    assert !chain.interp.IsEmpty() ==> v.boundaryLSN == chain.interp.seqStart;
    assert chain.interp.IsEmpty() && !tailMsgs.IsEmpty()
      ==> v.boundaryLSN == tailMsgs.seqStart by {
      if (chain.interp.IsEmpty() && !tailMsgs.IsEmpty()) {
        calc {
          v.boundaryLSN;
//          sb.boundaryLSN;
          tailMsgs.seqStart;
        }
      }
    }
//    assert chain.interp.IsEmpty() && tailMsgs.IsEmpty()
//      ==> v.boundaryLSN == tailMsgs.seqStart;
    assert !result.IsEmpty() ==> result.seqEnd == v.unmarshalledLSN();
    result
  }

  function SyncReqsAt(v: Variables, lsn: LSN) : set<CrashTolerantMapSpecMod.SyncReqId>
    //requires v.persistentLSN <= lsn < v.unmarshalledLSN()
    //requires v.WF()
  {
    //set syncReqId | v.syncReqs[syncReqId] == lsn //&& (syncReqId in nat)
    set lsns |  v.persistentLSN <= lsns <= lsn
  }

  function InterpFor(v: Variables, cache:CacheIfc.Variables, base: InterpMod.Interp, lsn: LSN) : Interp
    requires v.WF()
    requires Invariant(v, cache)
    requires base.seqEnd == v.boundaryLSN
    requires v.boundaryLSN <= lsn < v.unmarshalledLSN()
  {
    var newMsqSeq := ChainAsMsgSeq(v, cache);
    assert newMsqSeq.seqStart <= lsn < newMsqSeq.seqEnd;

    var trucatedSeq := newMsqSeq.Truncate(lsn);
    var interp := trucatedSeq.ApplyToInterp(base);
    interp
  }

   function VersionFor(v: Variables, cache:CacheIfc.Variables, base: InterpMod.Interp, lsn: LSN) : CrashTolerantMapSpecMod.Version
     requires v.WF()
     requires Invariant(v, cache)
     requires base.seqEnd == v.boundaryLSN
     requires v.boundaryLSN <= lsn < v.unmarshalledLSN() // we only need versions for the journal for the unapplied suffix of entries
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
     var numVersions := v.unmarshalledLSN() - v.boundaryLSN;
     seq(numVersions, i requires 0 <= i < numVersions =>
        var lsn := i + v.boundaryLSN;
        assert v.boundaryLSN <= lsn;
        assert lsn < v.unmarshalledLSN();
        VersionFor(v, cache, base, lsn)
     )
   }

   // TDODO: may have to lemma for the journal internal step

  function IMNotRunning(cache: CacheIfc.Variables, sb: Superblock, base: InterpMod.Interp) : CrashTolerantMapSpecMod.Variables
    requires base.seqEnd == sb.boundaryLSN  // This crash-invariant condition should probably not be a requires; just return nonsense if it fails.
  {
    var pretendVariables := Variables(sb.boundaryLSN, sb.boundaryLSN, sb.boundaryLSN, sb.boundaryLSN, [], map[], map[]);
    var versions := Versions(pretendVariables, cache, base);
    CrashTolerantMapSpecMod.Variables(versions, 0) // TODO Sowmya pick up here
  }

  function IM(v: Variables, cache:CacheIfc.Variables, base: InterpMod.Interp)
    : CrashTolerantMapSpecMod.Variables
    requires v.WF()
    requires Invariant(v, cache)
    requires base.seqEnd == v.boundaryLSN
  {
    assert v.boundaryLSN <= v.unmarshalledLSN(); // Follows from WF & defn unmarshalledLSN
    var versions := Versions(v, cache, base);
    CrashTolerantMapSpecMod.Variables(versions, 0)
  }

  // TODO(jonh): Try porting this from recursive style to Travis' suggested
  // repr-state style (see ReprsAsSets.i.dfy).
  function IReads(v: Variables, cache:CacheIfc.Variables, sb: Superblock) : seq<CU>
  {
    ChainFrom(cache.dv, sb).readCUs
  }

  lemma DiskViewsEquivalentAfterRemove(cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, cus: seq<CU>, removedCU: CU, cusr: seq<CU>)
    requires DiskViewsEquivalentForSet(cache0.dv, cache1.dv, cus)
    requires SequenceSubset(cusr, cus)
    ensures DiskViewsEquivalentForSet(MapRemove1(cache0.dv, removedCU), MapRemove1(cache1.dv, removedCU), cusr)
  {
  }

  // TODO(jonh): delete chain parameter.
  lemma FrameOneChain(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, sb: Superblock)
    requires DiskViewsEquivalentForSet(cache0.dv, cache1.dv, IReads(v, cache0, sb))
    ensures ChainFrom(cache0.dv, sb).chain == ChainFrom(cache1.dv, sb).chain
    decreases |cache0.dv|
  {
    if sb.freshestCU.Some? {
      assert sb.freshestCU.value in IReads(v, cache1, sb); // trigger
      assert sb.freshestCU.value in IReads(v, cache0, sb); // trigger
      assert IReads(v, cache0, sb)[0] == sb.freshestCU.value; // trigger
      if sb.freshestCU.value in cache0.dv {
        var firstRec := parse(cache0.dv[sb.freshestCU.value]);
        if firstRec.Some? { // Recurse to follow chain
          if firstRec.value.messageSeq.seqEnd <= sb.boundaryLSN {
          } else if firstRec.value.messageSeq.seqStart <= sb.boundaryLSN  {
          } else {
            // TODO wrapping these back up in CacheIfcs seems clumsy. (and demands the stupid decreases clause)
            var cache0r := CacheIfc.Variables(MapRemove1(cache0.dv, sb.freshestCU.value));
            var cache1r := CacheIfc.Variables(MapRemove1(cache1.dv, sb.freshestCU.value));
            var priorCU := firstRec.value.priorCU;
            var priorSB := firstRec.value.priorSB(sb);
            var cus := IReads(v, cache0, sb);
            var cusr := if priorCU.Some?
              then IReads(v, cache0r, priorSB)
              else [];

            forall i | 0<=i<|cusr| ensures cusr[i] in cus {
              assert cus[i+1] == cusr[i]; // witness to SequenceSubset(ausr, aus)
            }
            DiskViewsEquivalentAfterRemove(cache0, cache1, cus, sb.freshestCU.value, cusr);
            FrameOneChain(v, cache0r, cache1r, priorSB);
          }
        }
      }
    }
  }

  // Add comment about what this supposed to do the TODOS here
  lemma InternalStepLemma(v: Variables, cache: CacheIfc.Variables, v': Variables, cache': CacheIfc.Variables,  sb:Superblock, base: InterpMod.Interp, cacheOps: CacheIfc.Ops, sk: Skolem)
    requires DiskViewsEquivalentForSet(cache.dv, cache'.dv, IReads(v, cache, sb))
    requires v.WF()
    requires base.seqEnd == v.boundaryLSN
    requires Invariant(v, cache)
    requires Invariant(v', cache')
    requires v.boundaryLSN < v.unmarshalledLSN()
    requires Internal(v, v', cache, cacheOps, sk);
    requires CacheIfc.ApplyWrites(cache, cache', cacheOps)
    ensures v.boundaryLSN == v'.boundaryLSN
    ensures v.unmarshalledLSN() == v'.unmarshalledLSN()
    ensures IM(v, cache, base) == IM(v', cache', base)
  {
    assert v.boundaryLSN == v'.boundaryLSN;
    assert v.unmarshalledLSN() == v'.unmarshalledLSN();
    forall lsn | v.boundaryLSN <= lsn < v.unmarshalledLSN()
      ensures InterpFor(v, cache, base, lsn) == InterpFor(v', cache', base, lsn)
    {
      match sk {
        case AdvanceMarshalledStep(newCU) => {
          assert ChainFrom(cache'.dv, CurrentSuperblock(v')).chain.Some?;
          var sb := CurrentSuperblock(v);
          var sb' := CurrentSuperblock(v');
          var orig_chain_msgseq := ChainFrom(cache.dv, sb).chain.value.interp;
          var orig_tail_msgseq := TailToMsgSeq(v);
          var new_chain_msgseq := ChainFrom(cache'.dv, sb').chain.value.interp;
          var new_tail_msgseq := TailToMsgSeq(v');

          var priorCU := if v.marshalledLSN == v.boundaryLSN then None else Some(v.lsnToCU[v.marshalledLSN-1]);
          var jr := JournalRecord(TailToMsgSeq(v), priorCU);
          var sb_old := jr.priorSB(sb');
          assert sb_old == sb;
          calc {
            ChainFrom(cache'.dv, sb').chain.value.recs;
              {
                assert sb'.freshestCU.Some?;
                assert sb'.freshestCU.value in cache'.dv;
                assert parse(cache'.dv[sb'.freshestCU.value]).Some?;
                assert v'.marshalledLSN == v.unmarshalledLSN();
                assert v'.lsnToCU[v'.marshalledLSN - 1] == newCU; // CorrectMapping isn't defined
                assert newCU == FreshestMarshalledCU(v').value;
                assert sb'.freshestCU.value == newCU;
                assert jr == parse(cache'.dv[sb'.freshestCU.value]).value;  // CorrectMapping isn't defined.
                assert !(jr.messageSeq.seqEnd <= sb'.boundaryLSN);
                assert !(jr.messageSeq.seqStart <= sb.boundaryLSN);
                assert !(jr.priorCU.None?);
              }
            [jr] + ChainFrom(MapRemove1(cache'.dv, sb'.freshestCU.value), jr.priorSB(sb')).chain.value.recs;
            [jr] + ChainFrom(MapRemove1(cache'.dv, sb'.freshestCU.value), sb).chain.value.recs;
            [jr] + ChainFrom(cache.dv, sb).chain.value.recs;
              // Framing argument here
            [jr] + ChainFrom(cache.dv, sb).chain.value.recs;
          }
          calc {
            ChainAsMsgSeq(v', cache');
            ChainFrom(cache'.dv, sb').chain.value.interp.Concat(TailToMsgSeq(v'));
            new_chain_msgseq.Concat(new_tail_msgseq);
            new_chain_msgseq;
            orig_chain_msgseq.Concat(orig_tail_msgseq);
            ChainFrom(cache.dv, sb).chain.value.interp.Concat(TailToMsgSeq(v));
            ChainAsMsgSeq(v, cache);
          }
          assume false; // this is the slightly harder case, because the chain actually changes.
          assert ChainAsMsgSeq(v, cache) == ChainAsMsgSeq(v', cache');
        }
        case AdvanceCleanStep(newClean) => {
          assert cacheOps == [];
          CacheLemmasMod.EquivalentCaches(cache, cache', cacheOps);
          assert ChainAsMsgSeq(v, cache) == ChainAsMsgSeq(v', cache');
        }
      }
      assert ChainAsMsgSeq(v, cache) == ChainAsMsgSeq(v', cache');
    }
    assert IM(v, cache, base) == IM(v', cache', base);
  }

  lemma Framing(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, base: InterpMod.Interp)
    requires DiskViewsEquivalentForSet(cache0.dv, cache1.dv, IReads(v, cache0, CurrentSuperblock(v)))
    requires v.WF()
    requires base.seqEnd == v.boundaryLSN

    // QUESTION: We need to require these right?, Need to figure this out for later
    requires Invariant(v, cache0)
    requires Invariant(v, cache1)
    requires base.seqEnd == v.persistentLSN
    requires v.persistentLSN < v.unmarshalledLSN()
    ensures IM(v, cache0, base) == IM(v, cache1, base)
  {
//    assume false; // there's a timeout here that seems to point at opaque WFChainInner. That's weird.
    FrameOneChain(v, cache0, cache1, CurrentSuperblock(v));
    // This works --- I'm suspicious -- Sowmya
    calc {
      IM(v, cache0, base);
      IM(v, cache1, base);
    }
  }
}
