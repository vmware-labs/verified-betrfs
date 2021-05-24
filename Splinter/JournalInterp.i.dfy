// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Journal.i.dfy"

// The Module that Interprets the Journal.
module JournalInterpMod {
  import opened MessageMod
  import opened Options
  import opened Sequences
  import opened Maps
  import opened MsgSeqMod
  import MapSpecMod
  import AsyncMapSpecMod
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

  // TODO(jonh): collapse to return MsgSeq
  function MsgSeqs(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock) : seq<MsgSeq>
  {
    var chain := ChainFrom(cache.dv, sb).chain;
    if chain.Some?
    then
      MessageMaps(chain.value) + [TailAsMsgSeq(v)]
    else
      []
  }

  // Return all set
  function RequestSet(msgs : seq<Message>) : set<Requests>
  {

  }


  function IMinner(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, base: InterpMod.Interp) : AsyncMapSpecMod.Variables
  {
    if chain.Some? // should be called only when  v.persistentLSN < lsn
    then
      var: msgSequences = MesgSeqs(v, cache, sb)
      var: msgs = CondenseAll(msgSequences)
      var: pending = RequestSet(msgs.value)
      AsyncMapSpecMod.Variables(MapSpecMod.Variables(base), pending, {})
    else
      AsyncMapSpecMod.Variables(MapSpecMod.Variables(base), {}, {})
  }

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
    //requires v.persistentLSN <= lsn < v.unmarshalledLSN()
    //requires v.WF()
  {
    //set syncReqId | v.syncReqs[syncReqId] == lsn //&& (syncReqId in nat)
    set lsns |  v.persistentLSN <= lsns <= lsn
  }

  // function VersionFor(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, base: InterpMod.Interp, lsn: LSN) : CrashTolerantMapSpecMod.Version
  //   requires base.seqEnd == v.persistentLSN
  //   requires v.persistentLSN <= lsn < v.unmarshalledLSN()
  // {
  // // if lsn == v.persistentLSN
  //   then
  //     // TODO No accounting for v.syncReqs < persistentLSN; hrmm.
  //     CrashTolerantMapSpecMod.Version(MapSpecMod.Variables(base), SyncReqsAt(v, lsn))
  //   else
  //     var prior := VersionFor(v, cache, sb, base, lsn - 1);
  //     CrashTolerantMapSpecMod.Version(
  //       ApplyOneMessage(prior.mapp.interp, MessageAt(v, lsn)),
  //       SyncReqsAt(v, lsn))
  // }

  function AsMsgSeq(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock) : MsgSeq
  {
    CondenseAll(MsgSeqs(v, cache, sb))
  }

  function InterpFor(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, base: InterpMod.Interp, lsn: LSN) : Interp
    requires base.seqEnd == v.persistentLSN
    requires v.persistentLSN <= lsn <= v.unmarshalledLSN()
  {
    var newMi := AsMsgSeq(v, cache, sb).Truncate(lsn).ApplyToKeyMap(base.mi);
    var newInterp := Interp(newMi, lsn);
  }

  function InterpSeqFor(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, base: InterpMod.Interp) : seq<Interp>
  {
    seq(numVersions, i requires i < numVersions =>
      var lsn := i + v.persistentLSN;
      InterpFor(v, cache, sb, base, lsn)
    )
  }

   function VersionFor(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, base: InterpMod.Interp, lsn: LSN) : CrashTolerantMapSpecMod.Version
     requires base.seqEnd == v.persistentLSN
     requires v.persistentLSN <= lsn <= v.unmarshalledLSN() // we only need versions for the journal for the unapplied suffix of entries
   {
     if lsn == v.persistentLSN
      then
       // TODO No accounting for v.syncReqs < persistentLSN; hrmm.
       CrashTolerantMapSpecMod.Version(AsyncMapSpecMod.Variables(MapSpecMod.Variables(base), {}, {}), SyncReqsAt(v, lsn))
    else
       CrashTolerantMapSpecMod.Version(
       IMinner(v, cache, sb, base),
       SyncReqsAt(v, lsn))
   }

  // function VersionFor(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, base: InterpMod.Interp, lsn: LSN) : CrashTolerantMapSpecMod.Version
  //   requires base.seqEnd == v.persistentLSN
  //   //requires v.persistentLSN <= lsn < v.unmarshalledLSN()
  //   requires v.persistentLSN <= lsn
  //  {
  //     if lsn == v.persistentLSN
  //       then
  //      // TODO No accounting for v.syncReqs < persistentLSN; hrmm.
  //      CrashTolerantMapSpecMod.Version(AsyncMapSpecMod.Variables(MapSpecMod.Variables(base), {}, {}), SyncReqsAt(v, lsn))
  //    else
  //      var prior := VersionFor(v, cache, sb, base, lsn - 1);
  //      CrashTolerantMapSpecMod.Version(
  //        AsyncMapSpecMod.Variables(MapSpecMod.Variables(base),
  //        {} ,
  //        {}),
  //        SyncReqsAt(v, lsn))
  // }

  // TODO: Clean up this function ... The curr here is ugly
  function VersionMaps(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, base: InterpMod.Interp, curr : LSN, currseq: seq<CrashTolerantMapSpecMod.Version>) : seq<CrashTolerantMapSpecMod.Version>
  requires base.seqEnd == v.persistentLSN
  requires v.persistentLSN <= curr+ v.persistentLSN <= v.unmarshalledLSN()
  {
    if curr <= 0
      then
      currseq
    else
      VersionMaps(v, cache, sb, base, curr-1, currseq + [VersionFor(v, cache, sb, base, curr+ v.persistentLSN)] )
  }

  function IM(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, base: InterpMod.Interp)
    : CrashTolerantMapSpecMod.Variables
  requires base.seqEnd == v.persistentLSN
  requires v.persistentLSN < v.unmarshalledLSN()
  {
    // one version for persistentLSN, plus one for every LSN that we're aware of, because syncReqs
    // may point to any of those.
    var numVersions := v.unmarshalledLSN() - v.persistentLSN;
    //var versions := seq(numVersions, i requires i < numVersions =>
    //  var lsn := i + v.persistentLSN;
    //  VersionFor(v, cache, sb, base, lsn)
    //);
    var versions := VersionMaps(v, cache, sb, base, numVersions, []);
    CrashTolerantMapSpecMod.Variables(versions, 0)
  }

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

  lemma Framing(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, sb:CoreSuperblock, base: InterpMod.Interp)
    requires DiskViewsEquivalentForSet(cache0.dv, cache1.dv, IReads(v, cache0, sb))
    requires base.seqEnd == v.persistentLSN
    requires v.persistentLSN < v.unmarshalledLSN()
    ensures IM(v, cache0, sb, base) == IM(v, cache1, sb, base)
  {
    FrameOneChain(v, cache0, cache1, sb);
    calc {
      IM(v, cache0, sb, base);
      IM(v, cache1, sb, base);
    }
  }
}
