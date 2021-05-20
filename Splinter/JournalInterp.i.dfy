// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Journal.i.dfy"

module JournalInterpMod {
  import opened MessageMod
  import opened Options
  import opened Sequences
  import opened Maps
  import opened MsgSeqMod
  import MapSpecMod
  import opened AllocationMod
  import opened JournalMachineMod
  import opened InterpMod

  // TODO redo: return a seq of Message, with a prefix of None.
  function MessageMaps(journalChain: JournalChain) : seq<MsgSeq> {
    seq(|journalChain.recs|,
      i requires 0<=i<|journalChain.recs|
        => var mm := journalChain.recs[i].messageSeq; mm)
  }

  function TailAsMsgSeq(v: Variables) : MsgSeq {
    var asMap := map[]; // aaargh fine i'll do it later TODO
    MsgSeq(asMap, v.marshalledLSN, v.marshalledLSN + |v.unmarshalledTail|)
  }

//  // TODO(jonh): collapse to return MsgSeq
//  function IMinner(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock) : seq<MsgSeq>
//  {
//    var chain := ChainFrom(cache.dv, sb).chain;
//    if chain.Some?
//    then
//      MessageMaps(chain.value) + [TailAsMsgSeq(v)]
//    else
//      []
//  }

//  function MessageAt(chain: JournalChain, lsn: LSN) : Message
//    requires ValidChain(cache.dv, chain)
//    requires chain.sb == sb

//  function MessageAt(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, lsn: LSN) : Message
//  {
//    var chainResult := ChainFrom(cache.dv, sb);
//    var m:Message :| true; m  // TODO placeholder to parse
////    var JournalChain
//  }

  function SyncReqsAt(v: Variables, lsn: LSN) : set<CrashTolerantMapSpecMod.SyncReqId>
//  {
//    set syncReqId | v.syncReqs[syncReqId] == lsn
//  }

//  function VersionFor(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, base: InterpMod.Interp, lsn: LSN) : CrashTolerantMapSpecMod.Version
//    requires base.seqEnd == v.persistentLSN
//    requires v.persistentLSN <= lsn < v.unmarshalledLSN()
//  {
//    if lsn == v.persistentLSN
//    then
//      // TODO No accounting for v.syncReqs < persistentLSN; hrmm.
//      CrashTolerantMapSpecMod.Version(MapSpecMod.Variables(base), SyncReqsAt(v, lsn))
//    else
//      var prior := VersionFor(v, cache, sb, base, lsn - 1);
//      CrashTolerantMapSpecMod.Version(
//        ApplyOneMessage(prior.mapp.interp, MessageAt(v, lsn)),
//        SyncReqsAt(v, lsn))
//  }

  function IM(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, base: InterpMod.Interp)
    : CrashTolerantMapSpecMod.Variables
  requires base.seqEnd == v.persistentLSN
//  {
//    // one version for persistentLSN, plus one for every LSN that we're aware of, because syncReqs
//    // may point to any of those.
//    var numVersions := v.unmarshalledLSN() - v.persistentLSN;
//    var versions := seq(numVersions, i requires i<numVersions =>
//      var lsn := i + v.persistentLSN;
//      VersionFor(v, cache, sb, base, lsn)
//    );
//    CrashTolerantMapSpecMod.Variables(versions, 0)
//  }

  // TODO(jonh): Try porting this from recursive style to Travis' suggested
  // repr-state style (see ReprsAsSets.i.dfy).
  function IReads(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock) : seq<CU>
  {
    ChainFrom(cache.dv, sb).readCUs
  }

  predicate SequenceSubset<T>(a:seq<T>, b:seq<T>)
  {
    forall i | 0<=i<|a| :: a[i] in b
  }

  lemma DiskViewsEquivalentAfterRemove(cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, cus: seq<CU>, removedCU: CU, cusr: seq<CU>)
    requires DiskViewsEquivalentForSet(cache0.dv, cache1.dv, cus)
    requires SequenceSubset(cusr, cus)
    ensures DiskViewsEquivalentForSet(MapRemove1(cache0.dv, removedCU), MapRemove1(cache1.dv, removedCU), cusr)
  {
  }

  // TODO(jonh): delete chain parameter.
  lemma FrameOneChain(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, sb: CoreSuperblock)
    requires DiskViewsEquivalentForSet(cache0.dv, cache1.dv, IReads(v, cache0, sb))
    ensures ChainFrom(cache0.dv, sb).chain == ChainFrom(cache1.dv, sb).chain
    decreases |cache0.dv|
  {
    if sb.freshestCU.Some? {
      assert IReads(v, cache1, sb)[0] == sb.freshestCU.value; // trigger
      assert IReads(v, cache0, sb)[0] == sb.freshestCU.value; // trigger
      assert sb.freshestCU.value in IReads(v, cache1, sb); // trigger
      assert sb.freshestCU.value in IReads(v, cache0, sb); // trigger
      assert IReads(v, cache0, sb)[0] == sb.freshestCU.value; // trigger
      if sb.freshestCU.value in cache0.dv {
        var firstRec := parse(cache0.dv[sb.freshestCU.value]);
        if firstRec.Some? { // Recurse to follow chain
          if firstRec.value.messageSeq.seqEnd <= sb.boundaryLSN {
          } else if firstRec.value.messageSeq.seqStart <= sb.boundaryLSN  {
          } else {
            assert !(firstRec.value.messageSeq.seqStart <= sb.boundaryLSN);
            // TODO wrapping these back up in CacheIfcs seems clumsy. (and demands the stupid decreases clause)
            var cache0r := CacheIfc.Variables(MapRemove1(cache0.dv, sb.freshestCU.value));
            var cache1r := CacheIfc.Variables(MapRemove1(cache1.dv, sb.freshestCU.value));
            var priorCU := firstRec.value.priorCU;
            var priorSB := firstRec.value.priorSB(sb);
            var cus := IReads(v, cache0, sb);
            var cusr := if priorCU.Some?
              then IReads(v, cache0r, priorSB)
              else [];

            assert cache0r.dv == MapRemove1(cache0.dv, sb.freshestCU.value);
            assert firstRec.value.priorSB(sb) == priorSB;

            calc {
              ChainFrom(cache0.dv, sb).readCUs;
              ChainFromRecurse(cache0.dv, sb, firstRec).readCUs;
              [sb.freshestCU.value] + ChainFrom(cache0r.dv, priorSB).readCUs;
            }
            assert ChainFrom(cache0.dv, sb).readCUs == [sb.freshestCU.value] + ChainFrom(cache0r.dv, priorSB).readCUs;

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

  lemma Framing(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, sb:CoreSuperblock, base: InterpMod.Interp)
    requires DiskViewsEquivalentForSet(cache0.dv, cache1.dv, IReads(v, cache0, sb))
    ensures IM(v, cache0, sb, base) == IM(v, cache1, sb, base)
  {
    FrameOneChain(v, cache0, cache1, sb);
  }
}
