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

  // function TailAsMsgSeq(v: Variables) : MsgSeq
  // {
  //   var asMap := map |   //[]; // aaargh fine i'll do it later TODO-- Sowmya: What's the TODO?
  //   MsgSeq(asMap, v.marshalledLSN, v.marshalledLSN + |v.unmarshalledTail|)
  // }

  // Make sure that the suoperblock contains all the marshalled messages
  predicate ValidSuperBlock(v: Variables, cache: CacheIfc.Variables, sb: CoreSuperblock)
  {
    && sb.freshestCU.Some? ==> sb.freshestCU.value in cache.dv
    && parse(cache.dv[sb.freshestCU.value]).Some? ==> (v.marshalledLSN == parse(cache.dv[sb.freshestCU.value]).value.messageSeq.seqEnd)
    && v.boundaryLSN == sb.boundaryLSN
  }

  function EntireJournalChain(v: Variables, cache: CacheIfc.Variables, sb: CoreSuperblock) : (result : JournalChain)
    requires ValidSuperBlock(v, cache, sb)
    ensures WFChain(result)
    ensures result.interp.Len() > 0 ==> result.interp.seqEnd == v.marshalledLSN
    ensures result.interp.Len() > 0 ==> v.boundaryLSN == result.interp.seqStart
  {
    var chain := ChainFrom(cache.dv, sb).chain;
    if chain.Some?
    then
      var result :=  chain.value;
      result
    else
      var result := EmptyChain(sb);
      result
  }

  function AsMsgSeq(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock) : (result : MsgSeq)
    requires ValidSuperBlock(v, cache, sb)
    ensures result.WF()
    ensures result.Len() > 0 ==> result.seqEnd == v.unmarshalledLSN()
    ensures result.Len() > 0 ==> v.boundaryLSN == result.seqStart
  {
      var chain := EntireJournalChain(v, cache, sb);
      //assert v.boundaryLSN <= chain.interp.seqStart || chain.interp.Len() == 0 ;
      // freshest CU in the super block (end seq of that) === v.marshalledLSN
      // persistnet in the superblock (make sure we're passing in the right superblock) + unmarshalled
      //assert chain.interp.seqEnd <= v.marshalledLSN || chain.interp.Len() == 0;

      // believes these bounds
      assert chain.interp.Len() > 0 ==> chain.interp.seqEnd == v.marshalledLSN;
      assert chain.interp.Len() > 0 ==> v.boundaryLSN == chain.interp.seqStart;

      var tailMsgs := TailToMsgSeq(v);

      // believes these bounds
      assert tailMsgs.seqStart == v.marshalledLSN;
      assert tailMsgs.seqEnd == v.unmarshalledLSN();
      chain.interp.Concat(tailMsgs)
  }

  function SyncReqsAt(v: Variables, lsn: LSN) : set<CrashTolerantMapSpecMod.SyncReqId>
    //requires v.persistentLSN <= lsn < v.unmarshalledLSN()
    //requires v.WF()
  {
    //set syncReqId | v.syncReqs[syncReqId] == lsn //&& (syncReqId in nat)
    set lsns |  v.persistentLSN <= lsns <= lsn
  }


  function InterpFor(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, base: InterpMod.Interp, lsn: LSN) : Interp
    requires base.seqEnd == v.persistentLSN
    requires v.persistentLSN <= lsn < v.unmarshalledLSN()
  {

    var newMsqSeq := AsMsgSeq(v, cache, sb);
    assert newMsqSeq.seqStart <= lsn < newMsqSeq.seqEnd;
    var trucatedSeq := newMsqSeq.Truncate(lsn).ApplyToInterp(base);
    trucatedSeq
  }

   function VersionFor(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, base: InterpMod.Interp, lsn: LSN) : CrashTolerantMapSpecMod.Version
     requires base.seqEnd == v.persistentLSN
     requires v.persistentLSN <= lsn < v.unmarshalledLSN() // we only need versions for the journal for the unapplied suffix of entries
   {
       // TODO No accounting for v.syncReqs < persistentLSN; hrmm.
       var mapspec := MapSpecMod.Variables(InterpFor(v, cache, sb, base, lsn));
       var asyncmapspec := AsyncMapSpecMod.Variables(mapspec, {}, {});
       CrashTolerantMapSpecMod.Version(asyncmapspec, SyncReqsAt(v, lsn))
   }

  // TODO: Clean up this function ... The curr here is ugly
  // function VersionMaps(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, base: InterpMod.Interp, curr : LSN, currseq: seq<CrashTolerantMapSpecMod.Version>) : seq<CrashTolerantMapSpecMod.Version>
  // requires base.seqEnd == v.persistentLSN
  // requires v.persistentLSN <= curr+ v.persistentLSN <= v.unmarshalledLSN()
  // {
  //   if curr <= 0
  //     then
  //     currseq
  //   else
  //     VersionMaps(v, cache, sb, base, curr-1, currseq + [VersionFor(v, cache, sb, base, curr+ v.persistentLSN)] )
  // }
  //

  function Versions(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, base: InterpMod.Interp) : seq<CrashTolerantMapSpecMod.Version>
   {
     var numVersions := v.unmarshalledLSN() - v.boundaryLSN;
     seq(numVersions, i requires i < numVersions =>
        var lsn := i + v.persistentLSN;
        VersionFor(v, cache, sb, base, lsn)
     )
   }

  function IM(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock, base: InterpMod.Interp)
    : CrashTolerantMapSpecMod.Variables
  requires base.seqEnd == v.persistentLSN
  requires v.persistentLSN < v.unmarshalledLSN()
  {
    // one version for persistentLSN, plus one for every LSN that we're aware of, because syncReqs
    // may point to any of those.
    var numVersions := v.unmarshalledLSN() - v.persistentLSN;

    var versions := Versions(v, cache, sb, base);
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
