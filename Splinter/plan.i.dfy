include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Maps.i.dfy"

module MessageMod {
  type Key(!new,==)
  type Value(!new)
  type Message(!new)

  function AllKeys() : iset<Key> {
    iset key:Key | true
  }

  function DefaultValue() : Value
    // TODO
}

module AllocationMod {
  type AU = nat
  datatype CU = CU(au: AU, offset: nat)
  type UninterpretedDiskPage

  function DiskSizeInAU() : (s:nat)
    ensures 1<=s

  function AUSizeInBlocks() : (s:nat)
    ensures 2<=s

  predicate ValidCU(cu: CU) {
    && 0 <= cu.au < DiskSizeInAU()
    && 0 <= cu.offset < AUSizeInBlocks()
  }

  type DiskView = map<CU, UninterpretedDiskPage>

  predicate FullView(dv: DiskView) {
    forall cu :: cu in dv.Keys <==> ValidCU(cu)
  }
}

module MsgSeqMod {
  import opened MessageMod

  type MsgSeq = seq<Message>

  function I(key:Key, msgseq: MsgSeq) : Value

  predicate Collapsed(m0: MsgSeq, m1:MsgSeq)
  {
    false
    // m0, m1 related by collapsing irrelevant messages
  }

  lemma ICollapse(m0: MsgSeq, m1:MsgSeq)
    requires Collapsed(m0, m1)
    ensures forall key :: I(key, m0) == I(key, m1)
  {
  }

  function Concat(m0: MsgSeq, m1:MsgSeq) : MsgSeq
  {
    m0 + m1
  }
}

module MsgMapMod {
  import opened MessageMod
  import opened MsgSeqMod
  import opened Sequences

  predicate FullImap<K(!new),V>(m: imap<K, V>) {  // TODO move to MapSpec
    forall k :: k in m
  }

  function method FullImapWitness<K(!new),V>(v: V) : (m: imap<K, V>)
    ensures FullImap(m)
    // Gaa "method" because Dafny considers 'witness' not a ghost context.
    // Can't actually give this a body.

  type MsgMap = m: imap<Key, MsgSeq> | FullImap(m) witness FullImapWitness([])

  function I(msgmap: MsgMap) : imap<Key, Value>
  {
    imap key | key in AllKeys() :: MsgSeqMod.I(key, msgmap[key])
  }

  function Concat(m0: MsgMap, m1: MsgMap) : MsgMap
  {
    imap key | key in AllKeys() :: MsgSeqMod.Concat(m0[key], m1[key])
  }

  function ConcatSeq(sm:seq<MsgMap>) : MsgMap
  {
    if |sm|==0
      then Empty()
      else Concat(ConcatSeq(DropLast(sm)), Last(sm))
  }

  function Empty() : MsgMap
  {
    imap key | key in AllKeys() :: []
  }
}

module JournalMod {
  import opened Options
  import opened Sequences
  import opened Maps
  import opened MsgSeqMod
  import opened MsgMapMod
  import opened AllocationMod

  datatype Superblock = Superblock(firstCU: Option<CU>, firstValidSeq : nat)

  // Monoid-friendly (quantified-list) definition
  datatype JournalRecord = JournalRecord(
    messageSeq: MsgSeq,
    seqStart: nat,  // inclusive
    nextCU: Option<CU>   // linked list pointer
  ) {

    function seqEnd() : nat { seqStart + |messageSeq| }

    // Synthesize a superblock that reflects the tail of the chain (cutting
    // off the first rec), propagating along firstValidSeq.
    function nextSB(sb: Superblock) : Superblock
    {
      Superblock(nextCU, sb.firstValidSeq)
    }
  }
  datatype JournalChain = JournalChain(sb: Superblock, recs:seq<JournalRecord>)
  {
    // Synthesize a superblock that reflects the tail of the chain (cutting
    // off the first rec), propagating along firstValidSeq.
    function nextSB() : Superblock
      requires 0<|recs|
    {
      recs[0].nextSB(sb)
    }
  }

  function parse(b: UninterpretedDiskPage) : Option<JournalRecord>
    // TODO marshalling

  predicate IsLastLink(i: nat, chain: JournalChain)
    requires 0<=i<|chain.recs|
  {
    // stop if nothing more available
    || chain.recs[i].nextCU.None?
    // stop if nothing more needed
    || chain.sb.firstValidSeq >= chain.recs[i].seqStart
  }

  predicate WFChainBasic(chain: JournalChain)
  {
    && (chain.sb.firstCU.None? <==> 0 == |chain.recs|)
    && (forall i | 0<=i<|chain.recs| :: i==|chain.recs|-1 <==> IsLastLink(i, chain))
    && (forall i | 0<=i<|chain.recs|-1 :: chain.recs[i].nextCU.Some?)
  }

  predicate {:opaque} WFChainInner(chain: JournalChain)
    requires WFChainBasic(chain)
  {
    && (forall i | 0<=i<|chain.recs|-1 ::
      chain.recs[i].seqStart == chain.recs[i+1].seqEnd())
  }

  predicate WFChain(chain: JournalChain)
  {
    && WFChainBasic(chain)
    && WFChainInner(chain)
  }

  function CUsForChain(chain: JournalChain) : (cus: seq<CU>)
    requires WFChain(chain)
    ensures |cus| == |chain.recs|
  {
    if chain.sb.firstCU.None?
    then []
    else [chain.sb.firstCU.value] + seq(|chain.recs|-1,
        i requires 0<=i<|chain.recs|-1 => chain.recs[i].nextCU.value)
  }

  predicate RecordOnDisk(dv: DiskView, cu: CU, journalRecord: JournalRecord)
  {
    && cu in dv
    && parse(dv[cu]) == Some(journalRecord)
  }

  predicate {:opaque} ChainMatchesDiskView(dv: DiskView, chain: JournalChain)
    requires WFChain(chain)
  {
    // chain corresponds to stuff in the DiskView starting at firstCU.
    && var cus := CUsForChain(chain);
    && (forall i | 0<=i<|chain.recs| :: RecordOnDisk(dv, cus[i], chain.recs[i]))
  }

  // Describe a valid chain with quantification.
  predicate ValidJournalChain(dv: DiskView, chain: JournalChain)
  {
    && WFChain(chain)
    && ChainMatchesDiskView(dv, chain)
  }

  lemma ValidEmptyChain(dv: DiskView, sb: Superblock)
    requires sb.firstCU.None?
    ensures ValidJournalChain(dv, JournalChain(sb, []))
  {
    reveal_WFChainInner();
    reveal_ChainMatchesDiskView();
  }

  function ExtendChain(sb: Superblock, rec: JournalRecord, innerchain: JournalChain)
    : (chain: JournalChain)
    requires sb.firstCU.Some?
    requires rec.nextCU.Some? ==> sb.firstValidSeq < rec.seqStart; // proves !IsLastLink(0, chain)
    requires innerchain.sb == rec.nextSB(sb);
    requires 0<|innerchain.recs| ==> rec.seqStart == innerchain.recs[0].seqEnd();
    requires WFChain(innerchain)
    ensures WFChain(chain)
  {
    var chain := JournalChain(sb, [rec] + innerchain.recs);
    assert WFChainBasic(chain) by {
      forall i | 0<=i<|chain.recs| ensures i==|chain.recs|-1 <==> IsLastLink(i, chain)
      {
        if 0<i {
          assert IsLastLink(i-1, innerchain) == IsLastLink(i, chain);
        }
      }
    }
    assert WFChainInner(chain) by { reveal_WFChainInner(); }
    chain
  }

  // Define reading a chain recursively. Returns None if any of the
  // CUs point to missing blocks from the dv, or if the block can't
  // be parsed.
  // Return the set of readCUs visited. We may read six CUs before returning
  // a None chain. We have to know that to show how related dvs produce identical
  // results (even when they're broken).
  datatype ChainResult = ChainResult(chain: Option<JournalChain>, readCUs:seq<CU>)

  function ChainFrom(dv: DiskView, sb: Superblock) : (r:ChainResult)
    ensures r.chain.Some? ==>
      && ValidJournalChain(dv, r.chain.value)
      && r.chain.value.sb == sb
    decreases |dv.Keys|
  {
    if sb.firstCU.None? then
      // Superblock told the whole story; nothing to read.
      ValidEmptyChain(dv, sb);
      ChainResult(Some(JournalChain(sb, [])), [])
    else if sb.firstCU.value !in dv then
      // !RecordOnDisk: tried to read firstCU and failed
      ChainResult(None, [sb.firstCU.value])
    else
      var firstRec := parse(dv[sb.firstCU.value]);
      if firstRec.None? then
        // !RecordOnDisk: read firstCU, but it was borked
        ChainResult(None, [sb.firstCU.value])
      else if firstRec.value.seqEnd() <= sb.firstValidSeq then
        // This isn't an invariant disk state: if we're in the initial call,
        // the superblock shouldn't point to a useless JournalRecord; if we're
        // in a recursive call with correctly-chained records, we should have
        // already ignored this case.
        ChainResult(None, [sb.firstCU.value])
      else if firstRec.value.seqStart == sb.firstValidSeq then
        // Glad we read this record, but we don't need to read anything beyond.
        var r := ChainResult(Some(JournalChain(sb, [firstRec.value])), [sb.firstCU.value]);
        assert ValidJournalChain(dv, r.chain.value) by {
          reveal_WFChainInner();
          reveal_ChainMatchesDiskView();
        }
        r
      else
        var inner := ChainFrom(MapRemove1(dv, sb.firstCU.value), firstRec.value.nextSB(sb));
        if inner.chain.None? // tail didn't decode or
          // tail decoded but head doesn't stitch to it (a cross-crash invariant)
          || (0<|inner.chain.value.recs|
              && firstRec.value.seqStart != inner.chain.value.recs[0].seqEnd())
        then
          // failure in recursive call.
          // We read our cu plus however far the recursive call reached.
          ChainResult(None, [sb.firstCU.value] + inner.readCUs)
        else
          assert firstRec.value.nextCU.Some? ==> sb.firstValidSeq < firstRec.value.seqStart;
          var chain := ExtendChain(sb, firstRec.value, inner.chain.value);
          //var chain := JournalChain(sb, [firstRec.value] + inner.chain.value.recs);
          assert ValidJournalChain(dv, chain) by {
            reveal_ChainMatchesDiskView();
            var cus := CUsForChain(chain);
            assert forall i | 0<=i<|chain.recs| :: RecordOnDisk(dv, cus[i], chain.recs[i]); // trigger
          }
          ChainResult(Some(chain), [sb.firstCU.value] + inner.readCUs)
  }

  // TODO redo: return a seq of Message, with a prefix of None.
  function MessageMaps(journalChain: JournalChain) : seq<MsgSeq> {
    seq(|journalChain.recs|,
      i requires 0<=i<|journalChain.recs|
        => var mm := journalChain.recs[i].messageSeq; mm)
  }

  function IM(dv: DiskView, sb: Superblock) : seq<MsgSeq>
  {
    var chain := ChainFrom(dv, sb).chain;
    if chain.Some?
    then
      MessageMaps(chain.value)
    else
      []
  }

  function ReadAt(cus: seq<CU>, i: nat) : AU
    requires i<|cus|
  {
    cus[i].au
  }

  function IReads(dv: DiskView, sb: Superblock) : seq<AU>
  {
    var cus := ChainFrom(dv, sb).readCUs;
    // wanted to write:
    // seq(|cus|, i requires 0<=i<|cus| => cus[i].au)
    // but Dafny bug, so:
    seq(|cus|, i requires 0<=i<|cus| => ReadAt(cus, i))
  }

  predicate EqualAt(dv0: DiskView, dv1: DiskView, cu: CU)
  {
    || (cu !in dv0 && cu !in dv1)
    || (cu in dv0 && cu in dv1 && dv0[cu]==dv1[cu])
  }

  predicate DiskViewsEquivalentForSet(dv0: DiskView, dv1: DiskView, aus: seq<AU>)
  {
    forall cu:CU :: cu.au in aus ==> EqualAt(dv0, dv1, cu)
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

  lemma FrameOneChain(dv0: DiskView, dv1: DiskView, sb: Superblock, chain: Option<JournalChain>)
    requires chain == ChainFrom(dv0, sb).chain
    requires DiskViewsEquivalentForSet(dv0, dv1, IReads(dv0, sb))
    ensures chain == ChainFrom(dv1, sb).chain
  {
    if sb.firstCU.Some? {
      assert IReads(dv0, sb)[0] == sb.firstCU.value.au; // trigger
      if sb.firstCU.value in dv0 {
        var firstRec := parse(dv0[sb.firstCU.value]);
        if firstRec.Some? { // Recurse to follow chain
          if firstRec.value.seqEnd() <= sb.firstValidSeq {
          } else if firstRec.value.seqStart == sb.firstValidSeq {
          } else {
            var dv0r := MapRemove1(dv0, sb.firstCU.value);
            var nextCU := firstRec.value.nextCU;
            var nextSB := firstRec.value.nextSB(sb);
            var aus := IReads(dv0, sb);
            var ausr := if nextCU.Some?
              then IReads(dv0r, nextSB)
              else [];

            forall i | 0<=i<|ausr| ensures ausr[i] in aus {
              assert aus[i+1] == ausr[i]; // witness to SequenceSubset(ausr, aus)
            }
            DiskViewsEquivalentAfterRemove(dv0, dv1, aus, sb.firstCU.value, ausr);
            FrameOneChain(dv0r, MapRemove1(dv1, sb.firstCU.value),
              nextSB, ChainFrom(dv0r, nextSB).chain);
          }
        }
      }
    }
  }

  lemma Framing(sb:Superblock, dv0: DiskView, dv1: DiskView)
    requires DiskViewsEquivalentForSet(dv0, dv1, IReads(dv0, sb))
    ensures IM(dv0, sb) == IM(dv1, sb)
  {
    FrameOneChain(dv0, dv1, sb, ChainFrom(dv0, sb).chain);
  }
}

module MarshalledSnapshot {
  // A snapshot of a data structure, spread across a linked list of CUs on the disk.
  // This module almost certainly shares a bunch of DNA with Journal; TODO refactor.
  import opened AllocationMod
  import opened NativeTypes

  datatype SnapshotSuperblock = SnapshotSuperblock(firstCU: CU)

  datatype Block = Block()
  type Snapshot = seq<Block>

  predicate ValidSnapshot(dv: DiskView, snapshot: Snapshot) {
    false // TODO
  }

  function IBytes(dv: DiskView, sb: SnapshotSuperblock) : seq<byte> {
    if (exists snapshot :: ValidSnapshot(dv, snapshot))
    then
      // TODO decode all the blocks
      []
    else
      []
  }
}

module AllocationTableMod refines MarshalledSnapshot {
  import opened Options

  datatype Superblock = Superblock(snapshot: SnapshotSuperblock)

  type AllocationTable = set<AU>

  function parse(b: seq<byte>) : Option<AllocationTable>
    // TODO

  function I(dv: DiskView, sb: Superblock) : Option<AllocationTable> {
    parse(IBytes(dv, sb.snapshot))
  }
}

module IndirectionTableMod refines MarshalledSnapshot {
  import opened Options

  datatype Superblock = Superblock(snapshot: SnapshotSuperblock)

  type IndirectionTable = map<nat, AU>

  function parse(b: seq<byte>) : Option<IndirectionTable>

  function I(dv: DiskView, sb: Superblock) : Option<IndirectionTable> {
    parse(IBytes(dv, sb.snapshot))
  }
}

module BetreeMod {
  import opened Options
  import opened MessageMod
  import opened AllocationMod
  import opened MsgSeqMod
  import opened MsgMapMod
  import opened IndirectionTableMod

  datatype Superblock = Superblock(itbl: IndirectionTableMod.Superblock, rootIdx: IndirectionTableMod.IndirectionTable)

  datatype LookupRecord = LookupRecord(
    cu: CU
  )
  type Lookup = seq<LookupRecord>

  function LookupToMsgSeq(lookup: Lookup) : MsgSeq
    // TODO body

  predicate ValidLookup(dv: DiskView, itbl: IndirectionTable, key: Key, lookup: Lookup)
    // TODO

  function IMKey(dv: DiskView, sb: Superblock, key: Key) : MsgSeq
  {
    var itbl := IndirectionTableMod.I(dv, sb.itbl);
    if
      && itbl.Some?
      && exists lookup :: ValidLookup(dv, itbl.value, key, lookup)
    then
      var lookup :| ValidLookup(dv, itbl.value, key, lookup);
      LookupToMsgSeq(lookup)
    else
      []
  }

  function IM(dv: DiskView, sb: Superblock) : MsgMap
  {
    imap key | key in AllKeys() :: IMKey(dv, sb, key)
  }

  function IReadsKey(dv: DiskView, itbl: Option<IndirectionTable>, key: Key) : set<AU> {
    
    if
      && itbl.Some?
      && exists lookup :: ValidLookup(dv, itbl.value, key, lookup)
    then
      var lookup :| ValidLookup(dv, itbl.value, key, lookup);
      set i | 0<=i<|lookup| :: var lr:LookupRecord := lookup[i]; lr.cu.au
    else
      {}
  }

  function IReads(dv: DiskView, sb: Superblock) : set<AU> {
    var itbl := IndirectionTableMod.I(dv, sb.itbl);
    set au:AU |
      && au < AUSizeInBlocks()
      && exists key :: au in IReadsKey(dv, itbl, key)
  }

  lemma Framing(sb:Superblock, dv0: DiskView, dv1: DiskView)
    requires forall cu:CU :: cu.au in IReads(dv0, sb) ==>
      && cu in dv0
      && cu in dv1
      && dv0[cu]==dv1[cu]
    ensures IM(dv0, sb) == IM(dv1, sb)
  {
    // TODO I'm surprised this proof passes easily.
    forall key | key in AllKeys()
      ensures IMKey(dv0, sb, key) == IMKey(dv1, sb, key)
    {
      var itbl0 := IndirectionTableMod.I(dv0, sb.itbl);
      var itbl1 := IndirectionTableMod.I(dv1, sb.itbl);
      if itbl0.Some? && itbl1.Some?
      {
        var le0 := exists lookup0 :: ValidLookup(dv0, itbl0.value, key, lookup0);
        var le1 := exists lookup1 :: ValidLookup(dv1, itbl1.value, key, lookup1);
        if le0 {
          var lookup0 :| ValidLookup(dv0, itbl0.value, key, lookup0);
          assert ValidLookup(dv1, itbl1.value, key, lookup0);
        }
        if le1 {
          var lookup1 :| ValidLookup(dv1, itbl1.value, key, lookup1);
          assert ValidLookup(dv0, itbl1.value, key, lookup1);
        }
        assert le0 == le1;
      }
    }
  }
}

// It's funky that the allocation table is going to reserve its own
// blocks, but it's actually okay: we reserve them in the in-memory
// representation, then emit them once we've frozen a given view.

module System {
  import opened Options
  import opened MessageMod
  import opened AllocationMod
  import opened MsgSeqMod
  import opened MsgMapMod
  import AllocationTableMod
  import JournalMod
  import BetreeMod

  datatype Superblock = Superblock(
    serial: nat,
    journal: JournalMod.Superblock,
    allocation: AllocationTableMod.Superblock,
    betree: BetreeMod.Superblock)

  function parseSuperblock(b: UninterpretedDiskPage) : Option<Superblock>

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
    else
      None  // silly expression: DV has holes in it
  }

  function ISuperblockReads(dv: DiskView) : set<AU>
  {
    {0}
  }
 
  // IM == Interpret as MsgSeq
  // Oh man we're gonna have a family of IReads predicates that capture the
  // heapiness of DiskView, aren't we?
  function IM(dv: DiskView) : MsgMap
  {
    var sb := ISuperblock(dv);
    if sb.Some?
    then
      //JournalMod.IM(dv, sb.value.journal) + BetreeMod.IM(dv, sb.value.betree)
      // TODO stubbed out because IM API is changing to MsgSeqs
      BetreeMod.IM(dv, sb.value.betree)
    else
      MsgMapMod.Empty()
  }

  function IMReads(dv: DiskView) : set<AU> {
      {}
      /*
    var sb := ISuperblock(dv);
    if sb.Some?
    then
      JournalMod.IReads(dv, sb.value.journal) + BetreeMod.IReads(dv, sb.value.betree)
    else
      set{}
      */
  }

  function I(dv: DiskView) : imap<Key, Value> {
    MsgMapMod.I(IM(dv))
  }

  function IReads(dv: DiskView) : set<AU> {
    IMReads(dv)
  }

  lemma Framing(dv0: DiskView, dv1: DiskView)
  /*
    requires forall cu:CU :: cu.au in IReads(dv0) ==>
      && cu in dv0
      && cu in dv1
      && dv0[cu]==dv1[cu]
      */
    ensures I(dv0) == I(dv1)
  {
    //assert forall k :: k !in I(dv0);
    assert forall k :: I(dv0)[k] == I(dv1)[k];
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
