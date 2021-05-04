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

  function TailAsMsgSeq(v: Variables) : MsgSeq {
    var asMap := map[]; // aaargh fine i'll do it later TODO
    MsgSeq(asMap, v.marshalledLSN, v.marshalledLSN + |v.unmarshalledTail|)
  }

  // TODO(jonh): collapse to return MsgSeq
  function IMinner(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock) : seq<MsgSeq>
  {
    var chain := ChainFrom(cache.dv, sb).chain;
    if chain.Some?
    then
      MessageMaps(chain.value) + [TailAsMsgSeq(v)]
    else
      []
  }

  function IM(v: Variables, cache:CacheIfc.Variables, sb: Superblock) : Option<MsgSeq>
  {
    CondenseAll(IMinner(v, cache, sb.core))
  }

  function ReadAt(cus: seq<CU>, i: nat) : AU
    requires i<|cus|
  {
    cus[i].au
  }

  // TODO(jonh): Try porting this from recursive style to Travis' suggested
  // repr-state style (see ReprsAsSets.i.dfy).
  function IReads(v: Variables, cache:CacheIfc.Variables, sb: CoreSuperblock) : seq<AU>
  {
    var cus := ChainFrom(cache.dv, sb).readCUs;
    // wanted to write:
    // seq(|cus|, i requires 0<=i<|cus| => cus[i].au)
    // but Dafny bug, so:
    seq(|cus|, i requires 0<=i<|cus| => ReadAt(cus, i))
  }

  predicate SequenceSubset<T>(a:seq<T>, b:seq<T>)
  {
    forall i | 0<=i<|a| :: a[i] in b
  }

  lemma DiskViewsEquivalentAfterRemove(cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, aus: seq<AU>, removedCU: CU, ausr: seq<AU>)
    requires DiskViewsEquivalentForSet(cache0.dv, cache1.dv, aus)
    requires SequenceSubset(ausr, aus)
    ensures DiskViewsEquivalentForSet(MapRemove1(cache0.dv, removedCU), MapRemove1(cache1.dv, removedCU), ausr)
  {
  }

  // TODO(jonh): delete chain parameter.
  lemma FrameOneChain(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, sb: CoreSuperblock, chain: Option<JournalChain>)
    requires chain == ChainFrom(cache0.dv, sb).chain
    requires DiskViewsEquivalentForSet(cache0.dv, cache1.dv, IReads(v, cache0, sb))
    ensures chain == ChainFrom(cache1.dv, sb).chain
    // ensures ChainFrom(cache0, sb).chain == ChainFrom(cache1, sb).chain
    decreases |cache0.dv|
  {
    if sb.freshestCU.Some? {
      assert IReads(v, cache0, sb)[0] == sb.freshestCU.value.au; // trigger
      if sb.freshestCU.value in cache0.dv {
        var firstRec := parse(cache0.dv[sb.freshestCU.value]);
        if firstRec.Some? { // Recurse to follow chain
          if firstRec.value.messageSeq.seqEnd <= sb.boundaryLSN {
          } else if firstRec.value.messageSeq.seqStart == sb.boundaryLSN {
          } else {
            // TODO wrapping these back up in CacheIfcs seems clumsy. (and demands the stupid decreases clause)
            var cache0r := CacheIfc.Variables(MapRemove1(cache0.dv, sb.freshestCU.value));
            var cache1r := CacheIfc.Variables(MapRemove1(cache1.dv, sb.freshestCU.value));
            var priorCU := firstRec.value.priorCU;
            var priorSB := firstRec.value.priorSB(sb);
            var aus := IReads(v, cache0, sb);
            var ausr := if priorCU.Some?
              then IReads(v, cache0r, priorSB)
              else [];

            forall i | 0<=i<|ausr| ensures ausr[i] in aus {
              assert aus[i+1] == ausr[i]; // witness to SequenceSubset(ausr, aus)
            }
            DiskViewsEquivalentAfterRemove(cache0, cache1, aus, sb.freshestCU.value, ausr);
            FrameOneChain(v, cache0r, cache1r, priorSB, ChainFrom(cache0r.dv, priorSB).chain);
          }
        }
      }
    }
  }

  lemma Framing(v: Variables, cache0: CacheIfc.Variables, cache1: CacheIfc.Variables, sb:CoreSuperblock)
    requires DiskViewsEquivalentForSet(cache0.dv, cache1.dv, IReads(v, cache0, sb))
    ensures IMinner(v, cache0, sb) == IMinner(v, cache1, sb)
  {
    FrameOneChain(v, cache0, cache1, sb, ChainFrom(cache0.dv, sb).chain);
  }
}
