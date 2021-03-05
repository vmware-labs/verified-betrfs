include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Option.s.dfy"

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
  import opened MsgMapMod
  import opened AllocationMod

  datatype Superblock = Superblock(firstCU: CU, firstValidSeq : nat)

  // Monoid-friendly (quantified-list) definition
  datatype JournalRecord = JournalRecord(
    messageMap: MsgMap,
    seqStart: nat,  // inclusive
    seqEnd: nat,  // exclusive
    nextCU: CU   // linked list pointer
  )
  type JournalChain = seq<JournalRecord>

  predicate ValidJournalChain(journalChain: JournalChain) {
    false
  }

  function MessageMaps(journalChain: JournalChain) : seq<MsgMap> {
    seq(|journalChain|,
      i requires 0<=i<|journalChain|
        => var mm := journalChain[i].messageMap; mm)
  }

  function IM(dv: DiskView, sb: Superblock) : MsgMap
  {
    if (exists journalChain :: ValidJournalChain(journalChain))
    then
      var journalChain :| ValidJournalChain(journalChain);
      MsgMapMod.ConcatSeq(MessageMaps(journalChain))
    else
      MsgMapMod.Empty()
  }

// Recursive definition, rejected
//  function IM(dv: DiskView, sb: Superblock) : Message.MsgMap
//  {
//    IMAU(dv, sb.firstCU)
//  }
//
//  function IMAU(dv: DiskView, cu:CU) : Message.MsgMap
//    var journalRecord = JournalRecord.I(dv, cu);
//    suffix := if (firstValidSeq >= journalRecord.lowestSeq)
//      then MsgMap.Empty()
//      else IMAU(dv, journalRecord.nextCu);
//    MsgMap.Concat(journalRecord.msgmap, suffix)
//  }
}

module MarshalledSnapshot {
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
  import opened MessageMod
  import opened AllocationMod
  import opened MsgSeqMod
  import opened MsgMapMod
  import opened IndirectionTableMod

  datatype Superblock = Superblock(itbl: IndirectionTableMod.Superblock, rootIdx: IndirectionTableMod.IndirectionTable)

  datatype LookupRecord = LookupRecord()
  type Lookup = seq<LookupRecord>

  function LookupToMsgSeq(lookup: Lookup) : MsgSeq
    // TODO body

  predicate ValidLookup(dv: DiskView, itbl: IndirectionTable, key: Key, lookup: Lookup)
  {
    false // TODO
  }

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
 
  // IM == Interpret as MsgSeq
  // Oh man we're gonna have a family of IReads predicates that capture the
  // heapiness of DiskView, aren't we?
  function IM(dv: DiskView) : MsgMap
  {
    var sb := ISuperblock(dv);
    if sb.Some?
    then
      JournalMod.IM(dv, sb.value.journal) + BetreeMod.IM(dv, sb.value.betree)
    else
      MsgMapMod.Empty()
  }

  function I(dv: DiskView) : imap<Key, Value> {
    MsgMapMod.I(IM(dv))
  }
}
