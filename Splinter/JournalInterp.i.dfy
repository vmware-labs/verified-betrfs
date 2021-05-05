// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "Journal.i.dfy"

module JournalInterpMod {
  import opened Options
  import opened Sequences
  import opened Maps
  import opened MsgSeqMod
  import opened AllocationMod
  import opened JournalMachineMod

  // TODO redo: return a seq of Message, with a prefix of None.
  function MessageMaps(journalChain: JournalChain) : seq<MsgSeq> {
    seq(|journalChain.recs|,
      i requires 0<=i<|journalChain.recs|
        => var mm := journalChain.recs[i].messageSeq; mm)
  }

  // TODO(jonh): collapse to return MsgSeq
  function IMinner(dv: DiskView, sb: CoreSuperblock) : seq<MsgSeq>
  {
    var chain := ChainFrom(dv, sb).chain;
    if chain.Some?
    then
      MessageMaps(chain.value)
    else
      []
  }

  function IM(dv: DiskView, sb: Superblock) : Option<MsgSeq>
  {
    CondenseAll(IMinner(dv, sb.core))
  }

  function ReadAt(cus: seq<CU>, i: nat) : AU
    requires i<|cus|
  {
    cus[i].au
  }

  // TODO(jonh): Try porting this from recursive style to Travis' suggested
  // repr-state style (see ReprsAsSets.i.dfy).
  function IReads(dv: DiskView, sb: CoreSuperblock) : seq<AU>
  {
    var cus := ChainFrom(dv, sb).readCUs;
    // wanted to write:
    // seq(|cus|, i requires 0<=i<|cus| => cus[i].au)
    // but Dafny bug, so:
    seq(|cus|, i requires 0<=i<|cus| => ReadAt(cus, i))
  }

  predicate SequenceSubset<T>(a:seq<T>, b:seq<T>)
  {
    forall i | 0<=i<|a| :: a[i] in b
  }

  lemma DiskViewsEquivalentAfterRemove(dv0: DiskView, dv1: DiskView, aus: seq<AU>, removedCU: CU, ausr: seq<AU>)
    requires DiskViewsEquivalentForSet(dv0, dv1, aus)
    requires SequenceSubset(ausr, aus)
    ensures DiskViewsEquivalentForSet(MapRemove1(dv0, removedCU), MapRemove1(dv1, removedCU), ausr)
  {
  }

  // TODO(jonh): delete chain parameter.
  lemma FrameOneChain(dv0: DiskView, dv1: DiskView, sb: CoreSuperblock, chain: Option<JournalChain>)
    requires chain == ChainFrom(dv0, sb).chain
    requires DiskViewsEquivalentForSet(dv0, dv1, IReads(dv0, sb))
    ensures chain == ChainFrom(dv1, sb).chain
    // ensures ChainFrom(dv0, sb).chain == ChainFrom(dv1, sb).chain
  {
    if sb.freshestCU.Some? {
      assert IReads(dv0, sb)[0] == sb.freshestCU.value.au; // trigger
      if sb.freshestCU.value in dv0 {
        var firstRec := parse(dv0[sb.freshestCU.value]);
        if firstRec.Some? { // Recurse to follow chain
          if firstRec.value.messageSeq.seqEnd <= sb.boundaryLSN {
          } else if firstRec.value.messageSeq.seqStart == sb.boundaryLSN {
          } else {
            var dv0r := MapRemove1(dv0, sb.freshestCU.value);
            var priorCU := firstRec.value.priorCU;
            var priorSB := firstRec.value.priorSB(sb);
            var aus := IReads(dv0, sb);
            var ausr := if priorCU.Some?
              then IReads(dv0r, priorSB)
              else [];

            forall i | 0<=i<|ausr| ensures ausr[i] in aus {
              assert aus[i+1] == ausr[i]; // witness to SequenceSubset(ausr, aus)
            }
            DiskViewsEquivalentAfterRemove(dv0, dv1, aus, sb.freshestCU.value, ausr);
            FrameOneChain(dv0r, MapRemove1(dv1, sb.freshestCU.value),
              priorSB, ChainFrom(dv0r, priorSB).chain);
          }
        }
      }
    }
  }

  lemma Framing(sb:CoreSuperblock, dv0: DiskView, dv1: DiskView)
    requires DiskViewsEquivalentForSet(dv0, dv1, IReads(dv0, sb))
    ensures IMinner(dv0, sb) == IMinner(dv1, sb)
  {
    FrameOneChain(dv0, dv1, sb, ChainFrom(dv0, sb).chain);
  }
}
