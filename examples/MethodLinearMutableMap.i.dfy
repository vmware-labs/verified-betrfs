// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Lang/LinearSequence.s.dfy"
include "../lib/Lang/LinearSequence.i.dfy"

include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/Sequences.i.dfy"
include "../lib/Base/Sets.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../lib/Base/SetBijectivity.i.dfy"
include "../lib/Lang/System/Arithmetic.s.dfy"
//
// Immutable (functional) model to support MutableMapImpl.  API provides an
// iterator interface with a deterministic order for parsing/marshaling.
// (That's why the API is/ more than just a Dafny map.)
//
// TODO(jonh): Here and elsewhere, Model files seem to be both
// API (because callers use some of the definitions as 'public' ways
// to reason about the behavior of the modeled Impl) and internal
// proof (the logic half of the behavior of the Impl). It would be
// nice to cleanly separate these concerns.
//

module LinearMutableMap {
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened Sets
  import opened Maps
  import opened SetBijectivity
  import opened NativeArithmetic

  import opened LinearSequence_i
  import opened LinearSequence_s

  function method {:opaque} lshift(a: uint64, b: uint32) : uint64
  requires 0 <= b < 64
  {
    ((a as bv64) << b) as uint64
  }

  function method {:opaque} rshift(a: uint64, b: uint32) : uint64
  requires 0 <= b < 64
  {
    ((a as bv64) >> b) as uint64
  }

  function method {:opaque} bitnot(a: uint64) : uint64
  {
    ((a as bv64) ^ 0xffff_ffff_ffff_ffff) as uint64
  }

  function method {:opaque} bitxor(a: uint64, b: uint64) : uint64
  {
    ((a as bv64) ^ (b as bv64)) as uint64
  }

  function method {:opaque} hash64(k: uint64): uint64
  {
    var k0 := u64add(bitnot(k), lshift(k, 21));
    var k1 := bitxor(k0, rshift(k0, 24));
    var k2 := u64add(u64add(k1, lshift(k1, 3)), lshift(k1, 8));
    var k3 := bitxor(k2, rshift(k2, 14));
    var k4 := u64add(u64add(k3, lshift(k3, 2)), lshift(k3, 4));
    var k5 := bitxor(k4, rshift(k4, 28));
    var k6 := u64add(k5, lshift(k5, 31));

    k6
  }

  datatype Slot = Slot(ghost slot: nat)

  datatype Item<V> = Empty | Entry(key: uint64, value: V) | Tombstone(key: uint64)

  predicate ValidSlot(elementsLength: nat, slot: Slot)
  {
    slot.slot < elementsLength
  }

  linear datatype FixedSizeLinearHashMap<V> = FixedSizeLinearHashMap(
    linear storage: seq<Item<V>>,
    count: uint64,
    ghost contents: map<uint64, Option<V>>)

  predicate ValidElements<V>(elements: seq<Item<V>>)
  {
    && 0 < |elements| < 0x1_0000_0000_0000_0000
  }

  function SlotForKey(elementsLength: nat, key: uint64): (result: Slot)
  requires 0 < elementsLength
  ensures ValidSlot(elementsLength, result)
  {
    var h := hash64(key);
    Slot((h as nat) % elementsLength)
  }

  function method Uint64SlotForKey<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64): (result: uint64)
  requires 0 < |self.storage| < 0x1_0000_0000_0000_0000
  ensures ValidSlot(|self.storage|, Slot(result as nat))
  ensures Slot(result as nat) == SlotForKey(|self.storage|, key)
  {
    var h := hash64(key);
    var storageLength := seq_length(self.storage);
    h % (storageLength as uint64)
  }

  function SlotSuccessor(elementsLength: nat, slot: Slot): (nextSlot: Slot)
  requires ValidSlot(elementsLength, slot)
  ensures ValidSlot(elementsLength, nextSlot)
  {
    Slot(if slot.slot == elementsLength - 1 then
      0
    else
      slot.slot + 1)
  }

  function KthSlotSuccessor(elementsLength: nat, slot: Slot, k: nat): (nextSlot: Slot)
    requires k >= 0
    requires ValidSlot(elementsLength, slot)
    ensures ValidSlot(elementsLength, nextSlot)
  {
    if k == 0 then
      slot
    else
      SlotSuccessor(elementsLength, KthSlotSuccessor(elementsLength, slot, k - 1))
  }

  // KthSlotSuccessorWrapsAround
  //
  //   0 - - - - - - - - - - -   length = 12
  //                 @           slot = 7
  //                 | > > *     k = 3; (slot + k) mod length is slot 10 == 7 + 3
  //
  //   0 - - - - - - - - - - -   length = 12
  //                 @           slot = 7
  //                 | > > > >   k = 8
  //   > > > *                   (slot + k) mod length is slot 3 == 8 - (12 - 7) == 8 - 5 == 3
  //
  lemma KthSlotSuccessorWrapsAround(elementsLength: nat, slot: Slot, k: nat)
    requires 0 <= k < elementsLength
    requires ValidSlot(elementsLength, slot)
    ensures if k < (elementsLength-slot.slot) then
          KthSlotSuccessor(elementsLength, slot, k).slot == slot.slot + k
        else
          KthSlotSuccessor(elementsLength, slot, k).slot == k - (elementsLength - slot.slot)
    decreases k
  {
    /* (doc)
      var elementsInRightSlice := elementsLength - slot.slot;
      if k < elementsInRightSlice {
      } else {
        var firstSlot := KthSlotSuccessor(elementsLength, slot, elementsInRightSlice);
        var idx: nat := k - elementsInRightSlice;
        KthSlotSuccessorWrapsAround(elementsLength, firstSlot, idx);
      }
    */
  }

  predicate SlotIsEmpty<V>(elements: seq<Item<V>>, slot: Slot) // hide trigger
  requires ValidSlot(|elements|, slot)
  {
    elements[slot.slot].Empty?
  }

  predicate SlotIsEntry<V>(elements: seq<Item<V>>, slot: Slot) // hide trigger
  requires ValidSlot(|elements|, slot)
  {
    elements[slot.slot].Entry?
  }

  predicate SlotIsTombstone<V>(elements: seq<Item<V>>, slot: Slot) // hide trigger
  requires ValidSlot(|elements|, slot)
  {
    elements[slot.slot].Tombstone?
  }

  predicate FilledWithOtherKey<V>(elements: seq<Item<V>>, slot: Slot, excludingKey: uint64)
    requires ValidElements(elements)
    requires ValidSlot(|elements|, slot)
  {
    || (SlotIsTombstone(elements, slot) && elements[slot.slot].key != excludingKey)
    || (SlotIsEntry(elements, slot) && elements[slot.slot].key != excludingKey)
  }

  predicate FilledWithOtherKeys<V>(elements: seq<Item<V>>, start: Slot, count: nat, excludingKey: uint64)
    requires ValidElements(elements)
    requires ValidSlot(|elements|, start)
  {
    && (forall offset: nat :: offset < count ==>
      FilledWithOtherKey(elements, KthSlotSuccessor(|elements|, start, offset), excludingKey))
  }

  predicate FilledWithKey<V>(elements: seq<Item<V>>, slot: Slot, key: uint64)
    requires ValidElements(elements)
    requires ValidSlot(|elements|, slot)
  {
    (SlotIsEntry(elements, slot) || SlotIsTombstone(elements, slot)) && elements[slot.slot].key == key
  }

  predicate FilledWithEntryKey<V>(elements: seq<Item<V>>, slot: Slot, key: uint64)
    requires ValidElements(elements)
    requires ValidSlot(|elements|, slot)
  {
    && SlotIsEntry(elements, slot)
    && elements[slot.slot].key == key
  }

  predicate SlotExplainsKey<V>(elements: seq<Item<V>>, skips: nat, key: uint64)
  requires ValidElements(elements)
  {
    var foundSlot := KthSlotSuccessor(|elements|, SlotForKey(|elements|, key), skips);
    && ValidSlot(|elements|, foundSlot)
    && FilledWithOtherKeys(elements, SlotForKey(|elements|, key), skips, key)
    && FilledWithKey(elements, foundSlot, key)
  }

  // hide forall trigger
  predicate TwoNonEmptyValidSlotsWithSameKey<V>(elements: seq<Item<V>>, slot1: Slot, slot2: Slot)
  requires ValidElements(elements)
  {
    && ValidSlot(|elements|, slot1)
    && ValidSlot(|elements|, slot2)
    && (SlotIsEntry(elements, slot1) || SlotIsTombstone(elements, slot1))
    && (SlotIsEntry(elements, slot2) || SlotIsTombstone(elements, slot2))
    && elements[slot1.slot].key == elements[slot2.slot].key
  }

  // hide forall trigger
  predicate SameSlot(elementsLength: nat, slot1: Slot, slot2: Slot)
  requires ValidSlot(elementsLength, slot1)
  requires ValidSlot(elementsLength, slot2)
  {
    slot1 == slot2
  }

  predicate CantEquivocateStorageKey<V>(elements: seq<Item<V>>)
    requires ValidElements(elements)
  {
    forall slot1, slot2 :: TwoNonEmptyValidSlotsWithSameKey(elements, slot1, slot2)
        ==> SameSlot(|elements|, slot1, slot2)
  }

  predicate KeyInSlotIsInContents<V>(elements: seq<Item<V>>, contents: map<uint64, Option<V>>, slot: Slot)
  requires ValidSlot(|elements|, slot)
  requires SlotIsEntry(elements, slot) || SlotIsTombstone(elements, slot)
  {
    && var key := elements[slot.slot].key;
    && key in contents
  }

  predicate SeqMatchesContentKeys<V>(elements: seq<Item<V>>, contents: map<uint64, Option<V>>)
  requires ValidElements(elements)
  {
    && (forall key :: key in contents ==> exists skips :: SlotExplainsKey(elements, skips, key))
    && (forall slot :: ValidSlot(|elements|, slot) && (SlotIsEntry(elements, slot) || SlotIsTombstone(elements, slot))
        ==> KeyInSlotIsInContents(elements, contents, slot))
    && CantEquivocateStorageKey(elements)
  }

  predicate EntryInSlotMatchesContents<V>(elements: seq<Item<V>>, slot: Slot, contents: map<uint64, Option<V>>) // hide triggers
  requires ValidSlot(|elements|, slot)
  requires SlotIsEntry(elements, slot)
  {
    && var item := elements[slot.slot];
    && item.key in contents
    && contents[item.key] == Some(item.value)
  }

  predicate TombstoneInSlotMatchesContents<V>(elements: seq<Item<V>>, slot: Slot, contents: map<uint64, Option<V>>) // hide triggers
  requires ValidSlot(|elements|, slot)
  requires SlotIsTombstone(elements, slot)
  {
    && var item := elements[slot.slot];
    && item.key in contents
    && contents[item.key].None?
  }

  predicate EntriesMatchContentValue<V>(elements: seq<Item<V>>, contents: map<uint64, Option<V>>) // hide triggers
  requires ValidElements(elements)
  {
    forall slot :: ValidSlot(|elements|, slot) && SlotIsEntry(elements, slot)
        ==> EntryInSlotMatchesContents(elements, slot, contents)
  }

  predicate TombstonesMatchContentValue<V>(elements: seq<Item<V>>, contents: map<uint64, Option<V>>) // hide triggers
  requires ValidElements(elements)
  {
    forall slot :: ValidSlot(|elements|, slot) && SlotIsTombstone(elements, slot)
        ==> TombstoneInSlotMatchesContents(elements, slot, contents)
  }

  predicate FixedSizeInv<V>(self: FixedSizeLinearHashMap<V>)
  {
    && 128 <= |self.storage| < 0x1_0000_0000_0000_0000
    && (self.count as nat) < 0x1_0000_0000_0000_0000
    && self.count as nat < |self.storage|

    && |self.contents| == (self.count as nat)
    && SeqMatchesContentKeys(self.storage, self.contents)
    && EntriesMatchContentValue(self.storage, self.contents)
    && TombstonesMatchContentValue(self.storage, self.contents)
  }

  function IndexSetThrough<V>(elements: seq<Item<V>>, through: nat): set<int>
    requires through <= |elements|
  {
    set i | 0 <= i < through && (elements[i].Entry? || elements[i].Tombstone?)
  }

  function IndexSet<V>(elements: seq<Item<V>>): set<int>
  {
    IndexSetThrough(elements, |elements|)
  }

  function Count1<V>(item: Item<V>): nat
  {
    if item.Entry? || item.Tombstone? then 1 else 0
  }

  function CountFilled<V>(view: seq<Item<V>>): (result: nat)
  {
    if |view| == 0 then
      0
    else
      CountFilled(view[1..]) + Count1(view[0])
  }

  lemma CountFilledMatchesIndexSet<V>(elements: seq<Item<V>>)
  ensures CountFilled(elements) == |IndexSet(elements)|
  {
    var i: nat := 0;
    while i < |elements|
      invariant i <= |elements|
      invariant |IndexSetThrough(elements, i)| == CountFilled(elements[..i])
    {
      var j := i + 1;
      CountFilledAdditive(elements[..i], [elements[i]]);
      assert elements[..i] + [elements[i]] == elements[..j]; // observe
      if elements[i].Entry? || elements[i].Tombstone? {
        assert IndexSetThrough(elements, j) == IndexSetThrough(elements, i) + {i}; // observe
      } else {
        assert IndexSetThrough(elements, j) == IndexSetThrough(elements, i); // observe
      }
      i := j;
    }
    assert elements[..i] == elements; // observe
  }

  lemma IndexSetMatchesContents<V>(elements: seq<Item<V>>, contents: map<uint64, Option<V>>)
  requires ValidElements(elements)
  requires SeqMatchesContentKeys(elements, contents)
  ensures |IndexSet(elements)| == |contents.Keys|
  {
    var relation := iset i | i in IndexSet(elements) :: (i, elements[i].key);
    var setA := IndexSet(elements);
    var setB := contents.Keys;
    assert forall a | a in setA
      :: SlotIsEntry(elements, Slot(a)) || SlotIsTombstone(elements, Slot(a)); // observe
    assert forall a1, a2, b | a1 in setA && a2 in setA && b in setB && (a1, b) in relation && (a2, b) in relation
      :: SameSlot(|elements|, Slot(a1), Slot(a2)); // observe
    BijectivityImpliesEqualCardinality(IndexSet(elements), contents.Keys, relation);
  }

  lemma CountFilledAdditive<V>(a: seq<Item<V>>, b: seq<Item<V>>)
  ensures CountFilled(a + b) == CountFilled(a) + CountFilled(b)
  {
    if |a| == 0 {
      assert a + b == b; // observe
    } else {
      assert (a + b)[1..] == a[1..] + b; // observe
    }
  }

  function method ConstructorFromSize<V>(size: uint64): (linear self: FixedSizeLinearHashMap<V>)
  requires 128 <= size
  ensures FixedSizeInv(self)
  ensures forall slot :: ValidSlot(|self.storage|, slot) ==> SlotIsEmpty(self.storage, slot)
  ensures self.contents == map[]
  ensures size as nat == |self.storage|
  {
    linear var storage := seq_alloc_init(size, Empty);
    FixedSizeLinearHashMap(
     /* storage := */ storage,
     /* count := */ 0,
     /* contents := */ map[])
  }

  // TODO is this necessary in functional land?
  function method ConstructorFromStorage<V>(linear storage: seq<Item<V>>, count: uint64) 
  : (linear self: FixedSizeLinearHashMap<V>)
  requires 128 <= |storage|
  ensures self.storage == storage
  ensures forall slot :: ValidSlot(|self.storage|, slot) ==>
    self.storage[slot.slot] == storage[slot.slot]
  ensures self.count == count
  ensures self.contents == map[]
  {
    FixedSizeLinearHashMap(
     /* storage := */ storage,
     /* count := */ count,
     /* contents := */ map[])
  }

  function View<V>(elements: seq<Item<V>>, start: nat): (result: seq<Item<V>>)
  requires start < |elements|
  ensures |result| == |elements|
  {
    elements[start..] + elements[..start]
  }

  lemma ViewsHaveConsistentCounts<V>(a: seq<Item<V>>, b: seq<Item<V>>, delta: nat)
  requires delta < |a|
  requires b == View(a, delta)
  ensures CountFilled(a) == CountFilled(b)
  {
    var n := |a|;
    assert a == a[..delta] + a[delta..]; // observe
    CountFilledAdditive(a[..delta], a[delta..]);
    CountFilledAdditive(b[..n-delta], b[n-delta..]);
    assert b == b[..n-delta] + b[n-delta..]; // observe
  }

  function Uint64SlotSuccessor(elementsLength: nat, slot: uint64): (nextSlot: uint64)
  requires elementsLength < 0x1_0000_0000_0000_0000
  requires ValidSlot(elementsLength, Slot(slot as nat))
  ensures ValidSlot(elementsLength, Slot(nextSlot as nat))
  ensures Slot(nextSlot as nat) == SlotSuccessor(elementsLength, Slot(slot as nat))
  {
    Uint64SlotSuccessorUint64(elementsLength as uint64, slot)
  }

  // TODO rename
  function method Uint64SlotSuccessorUint64(elementsLength: uint64, slot: uint64): (nextSlot: uint64)
  requires ValidSlot(elementsLength as nat, Slot(slot as nat))
  ensures ValidSlot(elementsLength as nat, Slot(nextSlot as nat))
  ensures Slot(nextSlot as nat) == SlotSuccessor(elementsLength as nat, Slot(slot as nat))
  {
    if slot == (elementsLength as uint64) - 1 then
      0
    else
      slot + 1
  }

  lemma allNonEmptyImpliesCountEqStorageSize<V>(self: FixedSizeLinearHashMap<V>)
  requires FixedSizeInv(self)
  ensures (forall j | 0 <= j < |self.storage| :: !self.storage[j].Empty?)
      ==> self.count as int == |self.storage|
  {
    var elements := self.storage;
    if forall j | 0 <= j < |elements| :: !elements[j].Empty? {
      var elementIndices := set i | 0 <= i < |elements|;
      assert IndexSetThrough(elements, |elements|) == elementIndices; // trigger
      CardinalityOfSetsOfSequenceIndices(elements, elementIndices);
      IndexSetMatchesContents(elements, self.contents);
    }
  }

  function {:opaque} getEmptyWitness<V>(self: FixedSizeLinearHashMap<V>, i: uint64) : (res : uint64)
  requires FixedSizeInv(self)
  requires 0 <= i as int <= |self.storage|
  requires forall j | 0 <= j < i :: !self.storage[j].Empty?
  requires self.count as int < |self.storage|
  decreases |self.storage| - i as int
  ensures 0 <= res as int < |self.storage|
  ensures self.storage[res].Empty?
  {
    allNonEmptyImpliesCountEqStorageSize(self);

    if self.storage[i].Empty? then
      i
    else
      getEmptyWitness(self, i+1)
  }

  function method ProbeIterate<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64, slotIdx: uint64)
      : (foundSlotIdx: uint64)
  requires FixedSizeInv(self)
  requires 0 <= slotIdx as int < |self.storage|

  // We use the emptyWitness to prove termination.
  // We will necessarily terminate when we reach this index,
  // if not earlier.
  decreases var wit := getEmptyWitness(self, 0);
    if slotIdx > wit
      then wit as int - slotIdx as int + |self.storage|
      else wit as int - slotIdx as int

  ensures 0 <= foundSlotIdx as int < |self.storage|
  {
    var item := seq_get(self.storage, slotIdx);
    if item.Empty? || item.key == key then
      slotIdx
    else (
      ProbeIterate(self, key, Uint64SlotSuccessorUint64(seq_length(self.storage), slotIdx))
    )
  }

  function method {:opaque} Probe<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64): (foundSlotIdx: uint64)
  requires FixedSizeInv(self)
  requires self.count as int < |self.storage|
  ensures 0 <= foundSlotIdx as int < |self.storage|
  {
    ProbeIterate(self, key, Uint64SlotForKey(self, key))
  }

  datatype ProbeResult<V> = ProbeResult(
      slotIdx: uint64,
      ghost startSlotIdx: uint64,
      ghost ghostSkips: uint64)

  lemma LemmaProbeResult<V>(self: FixedSizeLinearHashMap<V>, key: uint64)
  returns (result : ProbeResult<V>)
  requires FixedSizeInv(self)
  ensures result.slotIdx == Probe(self, key)
  ensures ValidSlot(|self.storage|, Slot(result.slotIdx as nat))
  ensures ValidSlot(|self.storage|, Slot(result.startSlotIdx as nat))
  ensures Slot(result.startSlotIdx as nat) == SlotForKey(|self.storage|, key)
  ensures 0 <= result.ghostSkips
  ensures result.slotIdx as nat == KthSlotSuccessor(|self.storage|, Slot(result.startSlotIdx as nat), result.ghostSkips as nat).slot
  ensures key in self.contents ==> SlotExplainsKey(self.storage, result.ghostSkips as nat, key)
  ensures key !in self.contents ==> FilledWithOtherKeys(self.storage, Slot(result.startSlotIdx as nat), result.ghostSkips as nat, key) && (self.storage[result.slotIdx].Empty? || (self.storage[result.slotIdx].Tombstone? && self.storage[result.slotIdx].key == key))
  ensures self.storage[result.slotIdx].Entry? ==> key in self.contents && key == self.storage[result.slotIdx].key
  ensures self.storage[result.slotIdx].Empty? ==> key !in self.contents
  {
    reveal_Probe();

    var slotIdx := Uint64SlotForKey(self, key);
    var startSlotIdx := slotIdx;
    ghost var startSlot := Slot(startSlotIdx as nat);

    ghost var viewFromStartSlot := View(self.storage, startSlotIdx as nat);
    ViewsHaveConsistentCounts(self.storage, viewFromStartSlot, startSlotIdx as nat);
    CountFilledMatchesIndexSet(self.storage);
    IndexSetMatchesContents(self.storage, self.contents);

    forall dist: nat | dist < |self.storage|
    ensures self.storage[KthSlotSuccessor(|self.storage|, startSlot, dist).slot] == viewFromStartSlot[dist]
    {
      KthSlotSuccessorWrapsAround(|self.storage|, startSlot, dist); // observe
    }

    var skips := 0;
    while true
      invariant skips < (|self.storage| as uint64)
      invariant slotIdx < (|self.storage| as uint64)
      invariant |self.storage| == |viewFromStartSlot|
      invariant self.storage[startSlotIdx..] + self.storage[..startSlotIdx] == viewFromStartSlot
      invariant slotIdx as nat == KthSlotSuccessor(|self.storage|, startSlot, skips as nat).slot
      invariant skips < (|self.storage| as uint64) ==> self.storage[slotIdx] == viewFromStartSlot[skips]
      invariant ValidSlot(|self.storage|, KthSlotSuccessor(|self.storage|, startSlot, skips as nat))
      invariant FilledWithOtherKeys(self.storage, startSlot, skips as nat, key)
      invariant CountFilled(viewFromStartSlot[..skips]) == skips as nat

      invariant Probe(self, key) == ProbeIterate(self, key, slotIdx)

      decreases var wit := getEmptyWitness(self, 0);
        if slotIdx > wit
          then wit as int - slotIdx as int + |self.storage|
          else wit as int - slotIdx as int
    {
      if self.storage[slotIdx].Empty? || (self.storage[slotIdx].Tombstone? && self.storage[slotIdx].key == key) {
        result := ProbeResult(slotIdx, startSlotIdx, skips);
        return;
      } else if self.storage[slotIdx].key == key {
        assert EntryInSlotMatchesContents(self.storage, Slot(slotIdx as nat), self.contents); // observe
        result := ProbeResult(slotIdx, startSlotIdx, skips);
        return;
      }

      ghost var skipsBefore := skips;

      // -- increment --
      slotIdx := Uint64SlotSuccessor(|self.storage|, slotIdx);
      skips := skips + 1;
      // ---------------

      assert viewFromStartSlot[..skips] == viewFromStartSlot[..skipsBefore] + [viewFromStartSlot[skipsBefore]]; // observe
      CountFilledAdditive(viewFromStartSlot[..skipsBefore], [viewFromStartSlot[skipsBefore]]);

      assert Probe(self, key) == ProbeIterate(self, key, slotIdx);

      if skips == |self.storage| as uint64 {
        forall ensures false
        {
          calc {
            |self.storage|;
            skips as nat;
            CountFilled(viewFromStartSlot[..skips]);
              { assert viewFromStartSlot[..skips] == viewFromStartSlot; } // observe
            CountFilled(viewFromStartSlot);
            |self.contents|;
            self.count as nat;
            < |self.storage|;
          }
        }
      }
    }
  }

  method FixedSizeInsert<V>(linear self: FixedSizeLinearHashMap, key: uint64, value: V)
  returns (linear self': FixedSizeLinearHashMap, replaced: Option<V>)

    requires FixedSizeInv(self)
    requires self.count as nat < |self.storage| - 1
    ensures (
      && FixedSizeInv(self')
      && self'.contents == self.contents[key := Some(value)]
      && (key in self.contents ==> replaced == self.contents[key])
      && (replaced.Some? ==> key in self.contents)
      && (key !in self.contents ==> replaced.None?)
      && |self'.storage| == |self.storage|)
  {
    var slotIdx := Probe(self, key);
    var probeRes := LemmaProbeResult(self, key);

    assert slotIdx == probeRes.slotIdx;
    ghost var probeStartSlotIdx := probeRes.startSlotIdx;
    ghost var probeSkips := probeRes.ghostSkips;

    linear var FixedSizeLinearHashMap(selfStorage, selfCount, selfContents) := self;
    ghost var contents := selfContents[key := Some(value)];

    var replacedItem := seq_get(selfStorage, slotIdx);
    linear var updatedStorage := seq_set(selfStorage, slotIdx, Entry(key, value));

    replaced := None;
    if replacedItem.Empty? {
      self' := FixedSizeLinearHashMap(updatedStorage, selfCount + 1, contents);
    } else if replacedItem.Tombstone? {
      self' := FixedSizeLinearHashMap(updatedStorage, selfCount, contents);
    } else {
      self' := FixedSizeLinearHashMap(updatedStorage, selfCount, contents);
      replaced := Some(replacedItem.value);
    }

    forall explainedKey | explainedKey in self'.contents
    ensures exists skips :: SlotExplainsKey(self'.storage, skips, explainedKey)
    {
      if key == explainedKey {
        assert SlotExplainsKey(self'.storage, probeSkips as nat, key); // observe
      } else {
        var oldSkips :| SlotExplainsKey(self.storage, oldSkips, explainedKey);
        assert SlotExplainsKey(self'.storage, oldSkips, explainedKey); // observe
      }
    }

    forall slot | ValidSlot(|self'.storage|, slot) && self'.storage[slot.slot].Entry?
    ensures && var item := self'.storage[slot.slot];
            && self'.contents[item.key] == Some(item.value)
    {
      var item := self'.storage[slot.slot];
      if slot != Slot(slotIdx as nat) {
        if item.key == key {
          assert TwoNonEmptyValidSlotsWithSameKey(self'.storage, slot, Slot(slotIdx as nat)); // observe
          assert SameSlot(|self'.storage|, slot, Slot(slotIdx as nat)); // observe
          assert false;
        }
      }
    }
    forall slot | ValidSlot(|self'.storage|, slot) && self'.storage[slot.slot].Tombstone?
    ensures && var item := self'.storage[slot.slot];
            && self'.contents[item.key].None?
    {
      var item := self'.storage[slot.slot];
      if slot != Slot(slotIdx as nat) {
        if item.key == key {
          assert TwoNonEmptyValidSlotsWithSameKey(self'.storage, slot, Slot(slotIdx as nat)); // observe
          assert SameSlot(|self'.storage|, slot, Slot(slotIdx as nat)); // observe
          assert false;
        }
      }
    }
  }

  function method FixedSizeUpdateBySlot<V>(linear self: FixedSizeLinearHashMap<V>, slotIdx: uint64, value: V) : linear FixedSizeLinearHashMap<V>
  requires 0 <= slotIdx as int < |self.storage|
  requires self.storage[slotIdx].Entry?
  {
    linear var FixedSizeLinearHashMap(selfStorage, selfCount, selfContents) := self;
    ghost var updatedContents := selfContents[selfStorage[slotIdx].key := Some(value)];
    var entry := seq_get(selfStorage, slotIdx);
    linear var updatedStorage := seq_set(selfStorage, slotIdx, entry.(value := value));
    FixedSizeLinearHashMap(updatedStorage, selfCount, updatedContents)
  }

  lemma FixedSizeUpdateBySlotResult<V>(self: FixedSizeLinearHashMap<V>, slotIdx: uint64, value: V)
  requires FixedSizeInv(self)
  requires 0 <= slotIdx as int < |self.storage|
  requires self.storage[slotIdx].Entry?
  ensures var self' := FixedSizeUpdateBySlot(self, slotIdx, value);
      && FixedSizeInv(self')
  {
    var self' := FixedSizeUpdateBySlot(self, slotIdx, value);
    var key := self.storage[slotIdx].key;
    assert EntryInSlotMatchesContents(self.storage, Slot(slotIdx as int), self.contents);
    assert key in self.contents;
    calc {
      |self.contents|;
      |self.contents.Keys|;
      |self'.contents.Keys|;
      |self'.contents.Keys|;
    }

    forall explainedKey | explainedKey in self'.contents
    ensures exists skips :: SlotExplainsKey(self'.storage, skips, explainedKey)
    {
      var oldSkips :| SlotExplainsKey(self.storage, oldSkips, explainedKey);
      assert SlotExplainsKey(self'.storage, oldSkips, explainedKey); // observe
      
    }

    forall slot | ValidSlot(|self'.storage|, slot)
        && SlotIsEntry(self'.storage, slot)
    ensures EntryInSlotMatchesContents(self'.storage, slot, self'.contents)
    {
      assert EntryInSlotMatchesContents(self.storage, slot, self.contents);
      if slot.slot == slotIdx as int {
        calc {
          self'.contents[self'.storage[slot.slot].key];
          Some(self'.storage[slot.slot].value);
        }
      } else {
        calc {
          self'.contents[self'.storage[slot.slot].key];
          {
            assert self.storage[slot.slot].key
                == self'.storage[slot.slot].key;
            if self.storage[slot.slot].key == key {
              assert TwoNonEmptyValidSlotsWithSameKey(self.storage, slot, Slot(slotIdx as int));
            }
          }
          self.contents[self.storage[slot.slot].key];
          Some(self.storage[slot.slot].value);
          Some(self'.storage[slot.slot].value);
        }
      }
    }
  }

  function method {:opaque} FixedSizeGet<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64)
    : (found : Option<V>)
  requires FixedSizeInv(self)
  {
    var slotIdx := Probe(self, key);

    if seq_get(self.storage, slotIdx).Entry? then
      Some(seq_get(self.storage, slotIdx).value)
    else
      None
  }

  lemma LemmaFixedSizeGetResult<V>(self: FixedSizeLinearHashMap<V>, key: uint64)
  requires FixedSizeInv(self)
  ensures var found := FixedSizeGet(self, key);
    && if key in self.contents && self.contents[key].Some? then found == Some(self.contents[key].value) else found.None?
  {
    reveal_FixedSizeGet();
    var _ := LemmaProbeResult(self, key);
  }

  linear datatype FixedSizeRemoveResult<V> = FixedSizeRemoveResult(linear self': FixedSizeLinearHashMap<V>, removed: Option<V>)
  function method {:opaque} FixedSizeRemove<V>(linear self: FixedSizeLinearHashMap<V>, key: uint64)
    : linear FixedSizeRemoveResult<V>
  requires FixedSizeInv(self)
  {
    var slotIdx := Probe(self, key);

    if seq_get(self.storage, slotIdx).Entry? then (
      linear var FixedSizeLinearHashMap(selfStorage, selfCount, selfContents) := self;
      var removed := Some(seq_get(selfStorage, slotIdx).value);
      linear var updatedStorage := seq_set(selfStorage, slotIdx, Tombstone(key));
      linear var self' := FixedSizeLinearHashMap(
          updatedStorage,
          selfCount,
          selfContents[key := None]);
      FixedSizeRemoveResult(self', removed)
    ) else (
      FixedSizeRemoveResult(self, None)
    )
  }

  lemma LemmaFixedSizeRemoveResult<V>(self: FixedSizeLinearHashMap<V>, key: uint64)
  requires FixedSizeInv(self)
  ensures var FixedSizeRemoveResult(self', removed) := FixedSizeRemove(self, key);
    && FixedSizeInv(self')
    && (self'.contents == if key in self.contents
      then self.contents[key := None]
      else self.contents)
    && (removed == if key in self.contents && self.contents[key].Some?
      then Some(self.contents[key].value)
      else None)
    && (removed.Some? <==> (key in self.contents && self.contents[key].Some?))
    && (self'.count == self.count)
  {
    reveal_FixedSizeRemove();
    var FixedSizeRemoveResult(self', removed) := FixedSizeRemove(self, key);

    var probeRes := LemmaProbeResult(self, key);
    var slotIdx := probeRes.slotIdx;
    var probeStartSlotIdx := probeRes.startSlotIdx;
    var probeSkips := probeRes.ghostSkips;

    if self.storage[slotIdx].Entry? {
      forall explainedKey | explainedKey in self'.contents
      ensures exists skips :: SlotExplainsKey(self'.storage, skips, explainedKey)
      {
        if key == explainedKey {
          assert SlotExplainsKey(self'.storage, probeSkips as nat, key);
        } else {
          var oldSkips :| SlotExplainsKey(self.storage, oldSkips, explainedKey);
          assert SlotExplainsKey(self'.storage, oldSkips, explainedKey);
        }
      }

      forall slot | ValidSlot(|self'.storage|, slot) && self'.storage[slot.slot].Entry?
      ensures && var item := self'.storage[slot.slot];
              && self'.contents[item.key] == Some(item.value)
      {
        var item := self'.storage[slot.slot];
        if slot != Slot(slotIdx as nat) {
          if item.key == key {
            assert CantEquivocateStorageKey(self'.storage);
            assert TwoNonEmptyValidSlotsWithSameKey(self'.storage, slot, Slot(slotIdx as nat));
            assert false;
          }
        }
      }
    } else {
    }
  }

  //////// Resizing Hash Map

  linear datatype LinearHashMap<V> = LinearHashMap(
    linear underlying: FixedSizeLinearHashMap<V>,
    count: uint64,
    ghost contents: map<uint64, V>)
  {
    predicate Inv() {Inv0(this)} // HACK Inv0: is there a better way to refer to the outer Inv(...) from inside Inv()?
  }

  function MapFromStorage<V>(elements: seq<Item<V>>): (result: map<uint64, V>)
  {
    if |elements| == 0 then
      map[]
    else
      var item := Last(elements);
      var dropLastMap := MapFromStorage(DropLast(elements));
      if item.Entry? then
        dropLastMap[item.key := item.value]
      else
        dropLastMap
  }

  // TODO(jonh): This should just be CantEquivocateStorageKey, because (a) it's
  // the same and (b) this expression is a trigger nest.  But doing so will
  // involve cleaning up the proofs that break when we re-hide the definition.
  predicate CantEquivocate<V>(elements: seq<Item<V>>)
  {
    forall slot1, slot2 :: ValidSlot(|elements|, slot1) && ValidSlot(|elements|, slot2) &&
        elements[slot1.slot].Entry? && elements[slot2.slot].Entry? &&
        elements[slot1.slot].key == elements[slot2.slot].key ==> slot1 == slot2
  }

  lemma CantEquivocateMapFromStorageKey<V>(underlying: FixedSizeLinearHashMap<V>)
    requires FixedSizeInv(underlying)
    ensures CantEquivocate(underlying.storage)
  {
    assert |underlying.storage| > 0;
    assert ValidSlot(|underlying.storage|, Slot(0));
    assert exists slot :: ValidSlot(|underlying.storage|, slot);
    forall slot1, slot2 | (
      && ValidSlot(|underlying.storage|, slot1) && ValidSlot(|underlying.storage|, slot2)
      && underlying.storage[slot1.slot].Entry? && underlying.storage[slot2.slot].Entry?
      && underlying.storage[slot1.slot].key == underlying.storage[slot2.slot].key)
    ensures slot1 == slot2
    {
      assert CantEquivocateStorageKey(underlying.storage);
      if underlying.storage[slot1.slot].Entry? && underlying.storage[slot2.slot].Entry? &&
        underlying.storage[slot1.slot].key == underlying.storage[slot2.slot].key {

        assert TwoNonEmptyValidSlotsWithSameKey(underlying.storage, slot1, slot2);
        if slot1 != slot2 {
          assert false;
        }
        assert slot1 == slot2;
      } else {
        assert slot1 == slot2;
      }
    }
  }

  lemma MapFromStorageProperties<V>(elements: seq<Item<V>>, result: map<uint64, V>)
    requires CantEquivocate(elements)
    requires MapFromStorage(elements) == result
    ensures forall slot :: ValidSlot(|elements|, slot) && elements[slot.slot].Entry? ==>
        && var item := elements[slot.slot];
        && item.key in result && result[item.key] == item.value
    ensures forall key :: key in result ==>
        exists slot :: ValidSlot(|elements|, slot) && elements[slot.slot] == Entry(key, result[key])
    ensures forall key :: key !in result ==>
        forall slot :: ValidSlot(|elements|, slot) && elements[slot.slot].Entry?
            ==> elements[slot.slot].key != key
  {
    if |elements| == 0 {
    } else if Last(elements).Entry? {
      var item := Last(elements);
      assert elements == DropLast(elements) + [Last(elements)];
      var dropLastMap := MapFromStorage(DropLast(elements));
      MapFromStorageProperties(DropLast(elements), dropLastMap);

      forall slot | ValidSlot(|elements|, slot) && elements[slot.slot].Entry?
      ensures && var item := elements[slot.slot];
              && item.key in result && result[item.key] == item.value
      {
        var slotItem := elements[slot.slot];
        if item.key == elements[slot.slot].key {
          if slot.slot == |elements| - 1 {
            assert slotItem.key in result && result[slotItem.key] == slotItem.value;
          } else {
            var slot := Slot(|elements| - 1);
            assert ValidSlot(|elements|, slot);
            assert false;
          }
        } else {
          assert slotItem.key in result && result[slotItem.key] == slotItem.value;
        }
      }
      forall key | key in result
      ensures exists slot :: ValidSlot(|elements|, slot) && elements[slot.slot] == Entry(key, result[key])
      {
        if key == item.key {
          var slot := Slot(|elements| - 1);
          assert ValidSlot(|elements|, slot);
          assert elements[slot.slot] == Entry(key, result[key]);
        } else {
          assert exists slot :: ValidSlot(|elements|, slot) && elements[slot.slot] == Entry(key, result[key]);
        }
      }
    } else {
    }
  }

  predicate UnderlyingContentsMatchesContents<V>(underlying: FixedSizeLinearHashMap<V>, contents: map<uint64, V>)
  {
    && (forall key :: key in contents ==> key in underlying.contents && underlying.contents[key] == Some(contents[key]))
    && (forall key :: key !in contents ==> key !in underlying.contents || underlying.contents[key].None?)
  }

  predicate UnderlyingInv<V>(self: LinearHashMap<V>, underlying: FixedSizeLinearHashMap<V>)
  {
    && |self.contents| == self.count as nat
    && UnderlyingContentsMatchesContents(underlying, self.contents)
    && FixedSizeInv(underlying)
    && MapFromStorage(underlying.storage) == self.contents
  }

  lemma UnderlyingInvImpliesMapFromStorageMatchesContents<V>(underlying: FixedSizeLinearHashMap<V>, contents: map<uint64, V>)
    requires UnderlyingContentsMatchesContents(underlying, contents)
    requires FixedSizeInv(underlying)
    ensures MapFromStorage(underlying.storage) == contents
  {
    var mapFromStorage := MapFromStorage(underlying.storage);
    CantEquivocateMapFromStorageKey(underlying);
    MapFromStorageProperties(underlying.storage, mapFromStorage);
    assert MapFromStorage(underlying.storage) == contents;
  }

  predicate Inv0<V>(self: LinearHashMap<V>) { Inv(self) }

  protected predicate Inv<V>(self: LinearHashMap<V>)
    ensures Inv(self) ==> |self.contents| == self.count as nat
  {
    && UnderlyingInv(self, self.underlying)
    && MapFromStorage(self.underlying.storage) == self.contents
    && |self.contents| == self.count as nat
    && (self.count as nat) <= 0x1_0000_0000_0000_0000 / 8
  }

  lemma CountBound<V>(self: LinearHashMap<V>)
  requires Inv(self)
  ensures self.count as int <= 0x1_0000_0000_0000_0000 / 8
  {
  }

  lemma RevealProtectedInv<V>(self: LinearHashMap<V>)
    requires Inv(self)
    ensures (
      && UnderlyingInv(self, self.underlying)
      && MapFromStorage(self.underlying.storage) == self.contents
      && |self.contents| == self.count as nat)
  {
  }

  function method {:opaque} Constructor<V>(size: uint64) : (linear self: LinearHashMap<V>)
  requires 128 <= size
  ensures Inv(self)
  ensures self.contents == map[]
  {
    linear var self := LinearHashMap(ConstructorFromSize(size), 0, map[]);

    assert forall slot :: ValidSlot(|self.underlying.storage|, slot) ==> !self.underlying.storage[slot.slot].Entry?;
    UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents);
    assert MapFromStorage(self.underlying.storage) == self.contents;

    self
  }

  method {:opaque} Destructor<V>(linear self: LinearHashMap<V>)
  {
    linear var LinearHashMap(underlying, _, _) := self;
    linear var FixedSizeLinearHashMap(storage, _, _) := underlying;
    var _ := seq_free(storage);
  }

  lemma LemmaEntryKeyInContents<V>(self: LinearHashMap<V>, i: uint64)
  requires Inv(self)
  requires 0 <= i as int < |self.underlying.storage|
  requires self.underlying.storage[i].Entry?
  ensures self.underlying.storage[i].key in self.contents
  {
    assert EntryInSlotMatchesContents(self.underlying.storage, Slot(i as nat), self.underlying.contents); // trigger
  }

  method Realloc<V>(linear self: LinearHashMap<V>)
  returns (linear self': LinearHashMap<V>)
    requires Inv(self)
    requires self.count as nat < 0x1_0000_0000_0000_0000 / 8
    ensures Inv(self')
    ensures self'.contents == self.contents
    ensures self'.underlying.count as nat < |self'.underlying.storage| - 2
  {
    var i: uint64 := 0;
    var newSize: uint64 := (128 + self.count) * 4;
    linear var newUnderlying := ConstructorFromSize(newSize);

    var transferredContents: map<uint64, V> := map[];

    while i < seq_length(self.underlying.storage)
      invariant i <= seq_length(self.underlying.storage)

      invariant FixedSizeInv(newUnderlying)
      invariant self.count as int < |newUnderlying.storage| - 1
      invariant newUnderlying.contents.Keys <= self.contents.Keys

      invariant transferredContents.Keys <= self.contents.Keys
      invariant UnderlyingContentsMatchesContents(newUnderlying, transferredContents)
      invariant MapFromStorage(self.underlying.storage[..i]) == transferredContents

      invariant FixedSizeInv(newUnderlying)
      invariant newUnderlying.count as nat <= i as nat
      invariant |newUnderlying.storage| == newSize as nat

      invariant |transferredContents| == newUnderlying.count as nat
      invariant transferredContents.Keys <= self.contents.Keys
      invariant forall key :: key in newUnderlying.contents ==> exists slot: Slot :: (
          && slot.slot < i as int
          && ValidSlot(|self.underlying.storage|, slot)
          && FilledWithEntryKey(self.underlying.storage, slot, key))

      decreases |self.underlying.storage| - i as int
    {
      var item := seq_get(self.underlying.storage, i);

      assert self.underlying.storage[..i+1] == self.underlying.storage[..i] + [self.underlying.storage[i]];

      if item.Entry? {
        SetInclusionImpliesSmallerCardinality(newUnderlying.contents.Keys, self.contents.Keys);
        LemmaEntryKeyInContents(self, i);

        assert item == self.underlying.storage[i];

        if item.key in newUnderlying.contents {
          var j:uint64 :| (
              && 0 <= j < i
              && ValidSlot(|self.underlying.storage|, Slot(j as int))
              && self.underlying.storage[Slot(j as int).slot].Entry?
              && self.underlying.storage[Slot(j as int).slot].key == item.key);
          assert ValidSlot(|self.underlying.storage|, Slot(i as nat));
          assert i != j;
          assert Slot(i as nat) != Slot(j as nat);
          assert self.underlying.storage[Slot(j as nat).slot].key == self.underlying.storage[Slot(i as nat).slot].key;
          CantEquivocateMapFromStorageKey(self.underlying);
          assert false;
        }
        assert item.key !in newUnderlying.contents;

        // assert transferredContents.Keys <= self.contents.Keys;
        SetInclusionImpliesSmallerCardinality(transferredContents.Keys, self.contents.Keys);

        // -- mutation --
        var replaced;
        newUnderlying, replaced := FixedSizeInsert(newUnderlying, item.key, item.value); // use mutable ref here
        transferredContents := transferredContents[item.key := item.value];
        // --------------

        forall key | key in newUnderlying.contents
        ensures exists slot: Slot :: (
            && slot.slot < i as nat + 1
            && ValidSlot(|self.underlying.storage|, slot)
            && self.underlying.storage[slot.slot].Entry?
            && self.underlying.storage[slot.slot].key == key)
        {
          if key == item.key {
            assert ValidSlot(|self.underlying.storage|, Slot(i as nat));
          } else {
          }
        }
      }

      i := i + 1;
    }
    assert FixedSizeInv(newUnderlying);

    assert self.underlying.storage[..i] == self.underlying.storage;
    assert MapFromStorage(self.underlying.storage) == transferredContents;

    UnderlyingInvImpliesMapFromStorageMatchesContents(newUnderlying, transferredContents);
    assert transferredContents == self.contents;

    linear var LinearHashMap(selfUnderlying, selfCount, selfContents) := self;
    linear var FixedSizeLinearHashMap(oldStorage, _, _) := selfUnderlying;
    var _ := seq_free(oldStorage);

    self' := LinearHashMap(newUnderlying, selfCount, selfContents);

    assert self'.contents == transferredContents;

    assert UnderlyingContentsMatchesContents(newUnderlying, self'.contents);
    assert forall key :: key in self.contents ==> key in newUnderlying.contents && newUnderlying.contents[key] == Some(self.contents[key]);
    assert forall key :: key !in self.contents ==> key !in newUnderlying.contents || newUnderlying.contents[key].None?;

  }

  method InsertAndGetOld<V>(linear self: LinearHashMap, key: uint64, value: V)
  returns (linear self': LinearHashMap, replaced: Option<V>)
    requires Inv(self)
    requires self.count as nat < 0x1_0000_0000_0000_0000 / 8
    ensures Inv(self')
    ensures self'.contents == self.contents[key := value]
    ensures self'.count as nat == self.count as nat + (if replaced.Some? then 0 else 1)
    ensures replaced.Some? ==> MapsTo(self.contents, key, replaced.value)
    ensures replaced.None? ==> key !in self.contents
  {
    linear var self1 := self;
    // -- mutation --
    if seq_length(self1.underlying.storage) as uint64 / 2 <= self1.underlying.count {
      self1 := Realloc(self1);
    }
    // --------------

    // -- mutation --
    linear var LinearHashMap(self1Underlying, self1Count, self1Contents) := self1;
    linear var underlying';
    underlying', replaced := FixedSizeInsert(self1Underlying, key, value);
    ghost var contents' := self1Contents[key := value];
    self' := LinearHashMap(underlying',
        if replaced.None? then self1Count + 1 else self1Count,
        contents');
    // --------------

    UnderlyingInvImpliesMapFromStorageMatchesContents(self'.underlying, self'.contents);
  }

  method Insert<V>(linear self: LinearHashMap, key: uint64, value: V)
  returns (linear self': LinearHashMap)
    requires Inv(self)
    requires self.count as nat < 0x1_0000_0000_0000_0000 / 8
    ensures
      && Inv(self')
      && self'.contents == self.contents[key := value]
      && (self'.count as nat == self.count as nat ||
         self'.count as nat == self.count as nat + 1)
  {
    var replaced;
    self', replaced := InsertAndGetOld(self, key, value);
  }

  linear datatype RemoveResult<V> = RemoveResult(linear self': LinearHashMap, removed: Option<V>)
  function method RemoveInternal<V>(linear self: LinearHashMap, key: uint64)
  : (linear res: RemoveResult<V>)
    requires Inv(self)
    ensures var RemoveResult(self', removed) := res;
      && FixedSizeRemoveResult(self'.underlying, removed) == FixedSizeRemove(self.underlying, key)
      && FixedSizeInv(self'.underlying)
      && (self'.underlying.contents == if key in self.underlying.contents
        then self.underlying.contents[key := None]
        else self.underlying.contents)
      && (removed == if key in self.underlying.contents && self.underlying.contents[key].Some?
        then Some(self.underlying.contents[key].value)
        else None)
      && (self'.underlying.count == self.underlying.count)
  {
    // -- mutation --
    linear var LinearHashMap(selfUnderlying, selfCount, selfContents) := self;
    linear var FixedSizeRemoveResult(underlying', removed) := FixedSizeRemove(selfUnderlying, key);
    // --------------

    LemmaFixedSizeRemoveResult(self.underlying, key);

    linear var self' := LinearHashMap(
      /* underlying := */ underlying',
      /* count := */ if removed.Some? then selfCount - 1 else selfCount,
      /* contents := */ map k | k in selfContents && k != key :: selfContents[k]);

    RemoveResult(self', removed)
  }

  lemma RemoveCountCorrect<V>(self: LinearHashMap, key: uint64, res: RemoveResult<V>)
  requires Inv(self)
  requires res == RemoveInternal(self, key)
  ensures var RemoveResult(self', removed) := res;
    self'.count as nat == |self'.contents|
  {
    var RemoveResult(self', removed) := res;
    if removed.Some? {
      assert key in self.contents;
      assert self'.contents.Keys <= self.contents.Keys;
      assert |self.contents| == self'.count as nat + 1;
      assert |self.contents.Keys| == self'.count as nat + 1;
      assert |self.contents.Keys - {key}| == |self.contents.Keys| - |{key}|;
      assert self.contents.Keys - {key} == self'.contents.Keys;
      assert |self'.contents| == |self.contents| - 1;
      assert |self'.contents| == self'.count as nat;
    } else {
      assert key !in self.contents;
      assert self'.contents == self.contents;
      assert |self'.contents| == self'.count as nat;
    }
  }

  function method RemoveAndGet<V>(linear self: LinearHashMap, key: uint64)
  : (linear res: RemoveResult<V>)
    requires Inv(self)
    ensures var RemoveResult(self', removed) := res;
      && Inv(self')
      && (self'.contents == if key in self.contents
        then map k | k in self.contents && k != key :: self.contents[k]
        else self.contents)
      && (removed == if key in self.contents
        then Some(self.contents[key])
        else None)
  {
    linear var RemoveResult(self', removed) := RemoveInternal(self, key);

    LemmaFixedSizeRemoveResult(self.underlying, key);
    RemoveCountCorrect(self, key, RemoveResult(self', removed));
    UnderlyingInvImpliesMapFromStorageMatchesContents(self'.underlying, self'.contents); 

    RemoveResult(self', removed)
  }

  function method Remove<V>(linear self: LinearHashMap, key: uint64)
  : (linear self': LinearHashMap)
    requires Inv(self)
    ensures
      && Inv(self')
      && (self'.contents == if key in self.contents
        then map k | k in self.contents && k != key :: self.contents[k]
        else self.contents)
  {
    linear var RemoveResult(self', _) := RemoveAndGet(self, key);
    self'
  }

  function method Get<V>(shared self: LinearHashMap, key: uint64)
  : (found: Option<V>)
    requires Inv(self)
    ensures if key in self.contents then found == Some(self.contents[key]) else found.None?
    ensures found.Some? <==> key in self.contents
  {
    var found := FixedSizeGet(self.underlying, key);
    LemmaFixedSizeGetResult(self.underlying, key);
    found
  }

  //////// Iterator

  // We have two types of iterators.
  //
  // Iterator is usually more convenient as it has the IteratorOutput
  // built-in.
  //
  // SimpleIterator doesn't (you have to call SimpleIteratorOutput)
  // but has the advantage that the WFSimpleIter condition doesn't
  // depend on the key/value being correct. Thus the well-formedness
  // of a SimpleIterator can be preserved across (some) modifications
  // of the hash map.
  //
  // TODO fix the duplicated code that results.

  datatype IteratorOutput<V> = Next(key: uint64, value: V) | Done

  datatype Iterator<V> = Iterator(
    i: uint64, // index in hash table item list
    ghost s: set<uint64>,   // set of values returned so far
    ghost decreaser: ORDINAL,
    next: IteratorOutput)

  datatype SimpleIterator = SimpleIterator(
    i: uint64, // index in hash table item list
    ghost s: set<uint64>,   // set of values returned so far
    ghost decreaser: ORDINAL)

  predicate NextExplainedByI<V>(self: LinearHashMap<V>, i : uint64, output:IteratorOutput)
  {
    && (output.Next? ==>
      && i as int < |self.underlying.storage|
      && self.underlying.storage[i].Entry?
      && self.underlying.storage[i].key == output.key
      && self.underlying.storage[i].value == output.value)
    && (output.Done? ==> i as int == |self.underlying.storage|)
  }

  predicate ValidI<V>(self: LinearHashMap<V>, it: Iterator<V>)
  {
    && 0 <= it.i as int <= |self.underlying.storage|
  }

  predicate EachReturnedKeyExplainedByPassedIndex<V>(self: LinearHashMap<V>, s: set<uint64>, i: uint64)
  requires 0 <= i as int <= |self.underlying.storage|
  {
    forall key | key in s ::
        exists j | 0 <= j < i as int ::
        && self.underlying.storage[j].Entry?
        && key == self.underlying.storage[j].key
  }

  protected predicate WFIter<V>(self: LinearHashMap<V>, it: Iterator<V>)
  ensures WFIter(self, it) ==> (it.next.Done? ==> it.s == self.contents.Keys)
  ensures WFIter(self, it) ==> (it.next.Next? ==>
      MapsTo(self.contents, it.next.key, it.next.value));
  ensures WFIter(self, it) ==> (it.next.Next? ==> it.next.key !in it.s)
  ensures WFIter(self, it) ==> it.s <= self.contents.Keys
  {
    && ValidI(self, it)
    && NextExplainedByI(self, it.i, it.next)
    // Done justified by exhausting i
    && (it.next.Done? ==> (it.s == self.contents.Keys))
    // Each passed index appears in s
    && (forall j | 0 <= j < it.i as int ::
        self.underlying.storage[j].Entry? ==> self.underlying.storage[j].key in it.s)
    && EachReturnedKeyExplainedByPassedIndex(self, it.s, it.i)
    && it.decreaser == (|self.underlying.storage| - it.i as int) as ORDINAL
    && (it.next.Next? ==> MapsTo(self.contents, it.next.key, it.next.value))
    && (it.next.Next? ==> it.next.key !in it.s)
    && it.s <= self.contents.Keys
  }

  protected predicate WFSimpleIter<V>(self: LinearHashMap<V>, it: SimpleIterator)
  ensures WFSimpleIter(self, it) ==> it.s <= self.contents.Keys
  {
    && 0 <= it.i as int <= |self.underlying.storage| < Uint64UpperBound()
    && (it.i as int == |self.underlying.storage| ==> (it.s == self.contents.Keys))
    && (it.i as int < |self.underlying.storage| ==> self.underlying.storage[it.i].Entry?)
    // Each passed index appears in s
    && (forall j | 0 <= j < it.i as int ::
        self.underlying.storage[j].Entry? ==> self.underlying.storage[j].key in it.s)
    && EachReturnedKeyExplainedByPassedIndex(self, it.s, it.i)
    && it.decreaser == (|self.underlying.storage| - it.i as int) as ORDINAL
    && (it.i as int < |self.underlying.storage| ==> (
      && MapsTo(self.contents, self.underlying.storage[it.i].key, self.underlying.storage[it.i].value)
      && self.underlying.storage[it.i].key !in it.s
    ))
    && it.s <= self.contents.Keys
  }

  function method indexOutput<V>(shared self: LinearHashMap<V>, i: uint64) : (next: IteratorOutput<V>)
  requires 0 <= i as int <= |self.underlying.storage| < Uint64UpperBound()
  requires i as int < |self.underlying.storage| ==> self.underlying.storage[i].Entry?
  {
    if i == seq_length(self.underlying.storage) then (
      Done
    ) else (
      Next(
        seq_get(self.underlying.storage, i).key,
        seq_get(self.underlying.storage, i).value)
    )
  }

  protected function method SimpleIterOutput<V>(shared self: LinearHashMap<V>, it: SimpleIterator) : (next: IteratorOutput<V>)
  requires WFSimpleIter(self, it)
  ensures (next.Done? ==> it.s == self.contents.Keys)
  ensures (next.Next? ==>
      MapsTo(self.contents, next.key, next.value));
  ensures (next.Next? ==> next.key !in it.s)
  {
    indexOutput(self, it.i)
  }

  lemma LemmaWFIterImpliesILt<V>(self: LinearHashMap<V>, it: Iterator<V>)
  requires WFIter(self, it)
  ensures it.next.Next? ==> it.i as int < |self.underlying.storage|
  {
  }

  lemma LemmaWFSimpleIterImpliesEntry<V>(self: LinearHashMap<V>, it: SimpleIterator)
  requires WFSimpleIter(self, it)
  ensures
    && 0 <= it.i as int <= |self.underlying.storage|
    && (SimpleIterOutput(self, it).Next? ==> it.i as int < |self.underlying.storage|)
    && (it.i as int < |self.underlying.storage| ==>
      && self.underlying.storage[it.i].Entry?
    )
  {
  }

  lemma LemmaIterNextNotInS<V>(self: LinearHashMap<V>, it: Iterator<V>)
  requires 0 <= it.i as int <= |self.underlying.storage|
  requires ValidElements(self.underlying.storage)
  requires CantEquivocateStorageKey(self.underlying.storage)
  requires NextExplainedByI(self, it.i, it.next)
  requires EachReturnedKeyExplainedByPassedIndex(self, it.s, it.i)
  ensures (it.next.Next? ==> it.next.key !in it.s)
  {
    if it.next.Next? {
      if it.next.key in it.s {
        var j :| 0 <= j < it.i as int
          && self.underlying.storage[j].Entry?
          && it.next.key == self.underlying.storage[j].key;
        assert TwoNonEmptyValidSlotsWithSameKey<V>(self.underlying.storage, Slot(it.i as int), Slot(j));  // trigger
        // assert false; // proof by contradiction
      }
    }
  }

  function method iterToNext<V>(shared self: LinearHashMap<V>, i: uint64) : (res: (uint64, IteratorOutput))
  requires Inv(self)
  requires 0 <= i as int <= |self.underlying.storage|
  ensures NextExplainedByI(self, res.0, res.1)
  ensures forall j | i <= j < res.0 :: !self.underlying.storage[j].Entry?
  ensures i <= res.0
  decreases |self.underlying.storage| - i as int
  {
    if i == seq_length(self.underlying.storage) then (
      (i, Done)
    ) else if seq_get(self.underlying.storage, i).Entry? then (
      (i, Next(seq_get(self.underlying.storage, i).key, seq_get(self.underlying.storage, i).value))
    ) else (
      iterToNext(self, i+1)
    )
  }

  function method simpleIterToNext<V>(shared self: LinearHashMap<V>, i: uint64) : (i': uint64)
  requires Inv(self)
  requires 0 <= i as int <= |self.underlying.storage|
  ensures 0 <= i' as int <= |self.underlying.storage|
  ensures forall j | i <= j < i' :: !self.underlying.storage[j].Entry?
  ensures i' as int < |self.underlying.storage| ==>
      self.underlying.storage[i'].Entry?
  ensures i <= i'
  decreases |self.underlying.storage| - i as int
  {
    if i == seq_length(self.underlying.storage) then (
      i
    ) else if seq_get(self.underlying.storage, i).Entry? then (
      i
    ) else (
      simpleIterToNext(self, i+1)
    )
  }

  lemma lemmaIterToNextValidKeyValuePair<V>(self: LinearHashMap<V>, i: uint64)
  requires Inv(self)
  requires 0 <= i as int <= |self.underlying.storage|
  ensures iterToNext(self, i).1.Next? ==>
      MapsTo(self.contents, 
          iterToNext(self, i).1.key,
          iterToNext(self, i).1.value)
  {
    var j := iterToNext(self, i).0;
    var next := iterToNext(self, i).1;
    if next.Next? {
      UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents);
      CantEquivocateMapFromStorageKey(self.underlying);
      MapFromStorageProperties(self.underlying.storage, self.contents);
      assert self.underlying.storage[Slot(j as int).slot].value == next.value; // trigger
    }
  }

  function method {:opaque} IterStart<V>(shared self: LinearHashMap<V>) : (it' : Iterator<V>)
  requires Inv(self)
  ensures WFIter(self, it')
  ensures it'.s == {}
  {
    lemmaIterToNextValidKeyValuePair(self, 0);

    var (i, next) := iterToNext(self, 0);
    var it' := Iterator(i, {}, (|self.underlying.storage| - i as int) as ORDINAL, next);

    LemmaIterNextNotInS(self, it');

    it'
  }

  function method {:opaque} SimpleIterStart<V>(shared self: LinearHashMap<V>) : (it' : SimpleIterator)
  requires Inv(self)
  ensures WFSimpleIter(self, it')
  ensures it'.s == {}
  {
    lemmaIterToNextValidKeyValuePair(self, 0);

    var i := simpleIterToNext(self, 0);
    var it' := SimpleIterator(i, {}, (|self.underlying.storage| - i as int) as ORDINAL);

    LemmaIterNextNotInS(self,
      Iterator(it'.i, it'.s, it'.decreaser, indexOutput(self, it'.i)));

    it'
  }

  function method {:opaque} IterInc<V>(shared self: LinearHashMap<V>, it: Iterator) : (it' : Iterator)
  requires Inv(self)
  requires WFIter(self, it)
  requires it.next.Next?
  ensures WFIter(self, it')
  ensures it'.s == it.s + {it.next.key}
  ensures it'.next.Done? ==> it'.s == self.contents.Keys
  ensures it'.decreaser < it.decreaser
  {
    lemmaIterToNextValidKeyValuePair(self, it.i + 1);

    var (i, next) := iterToNext(self, it.i + 1);
    var it' := Iterator(i, it.s + {it.next.key}, (|self.underlying.storage| - i as int) as ORDINAL, next);

    assert (forall key | key in it'.s ::
        exists j | 0 <= j < it'.i as int ::
        && self.underlying.storage[j].Entry?
        && key == self.underlying.storage[j].key);
    assert (it'.next.Done? ==> it'.s == self.contents.Keys);

    LemmaIterNextNotInS(self, it');

    it'
  }

  function method {:opaque} SimpleIterInc<V>(shared self: LinearHashMap<V>, it: SimpleIterator) : (it' : SimpleIterator)
  requires Inv(self)
  requires WFSimpleIter(self, it)
  requires SimpleIterOutput(self, it).Next?
  ensures WFSimpleIter(self, it')
  ensures it'.s == it.s + {SimpleIterOutput(self, it).key}
  ensures it'.decreaser < it.decreaser
  {
    lemmaIterToNextValidKeyValuePair(self, it.i + 1);

    var i := simpleIterToNext(self, it.i + 1);
    var it' := SimpleIterator(i, it.s + {SimpleIterOutput(self, it).key}, (|self.underlying.storage| - i as int) as ORDINAL);

    assert (forall key | key in it'.s ::
        exists j | 0 <= j < it'.i as int ::
        && self.underlying.storage[j].Entry?
        && key == self.underlying.storage[j].key);

    LemmaIterNextNotInS(self,
      Iterator(it'.i, it'.s, it'.decreaser, indexOutput(self, it'.i)));

    it'
  }

  lemma LemmaIterIndexLtCount<V>(self: LinearHashMap<V>, it: Iterator<V>)
  requires Inv(self)
  requires WFIter(self, it)
  ensures it.next.Next? ==> |it.s| < self.count as int
  {
    if it.next.Next? {
      ProperSubsetImpliesSmallerCardinality(it.s, self.contents.Keys);
    }
  }

  function method MaxKeyIterate<V>(shared self: LinearHashMap<V>, it: Iterator<V>, m: uint64) : (res : uint64)
  requires Inv(self)
  requires WFIter(self, it)
  requires forall key | key in it.s :: key <= m
  ensures forall key | key in self.contents :: key <= res
  decreases it.decreaser
  {
    if it.next.Done? then (
      m
    ) else (
      var key := it.next.key;
      MaxKeyIterate(self, IterInc(self, it), if m < key then key else m)
    )
  }

  function method {:opaque} MaxKey<V>(shared self: LinearHashMap<V>) : (res : uint64)
  requires Inv(self)
  ensures forall key | key in self.contents :: key <= res
  {
    MaxKeyIterate(self, IterStart(self), 0)    
  }

  function method {:opaque} UpdateByIter<V>(linear self: LinearHashMap<V>, it: SimpleIterator, value: V)
    : (linear self': LinearHashMap)
  requires Inv(self)
  requires WFSimpleIter(self, it)
  requires SimpleIterOutput(self, it).Next?
  ensures Inv(self')
  ensures self'.contents == self.contents[SimpleIterOutput(self, it).key := value]
  ensures self'.count == self.count
  {
    FixedSizeUpdateBySlotResult(self.underlying, it.i, value);

    linear var LinearHashMap(selfUnderlying, selfCount, selfContents) := self;
    linear var newUnderlying := FixedSizeUpdateBySlot(selfUnderlying, it.i, value);
    linear var self' := LinearHashMap(newUnderlying, selfCount,
        self.contents[SimpleIterOutput(self, it).key := value]);

    UnderlyingInvImpliesMapFromStorageMatchesContents(self'.underlying, self'.contents);

    self'
  }

  lemma UpdatePreservesSimpleIter<V>(
    self: LinearHashMap<V>, it: SimpleIterator, value: V,
    preserved: SimpleIterator)
  requires UpdateByIter.requires(self, it, value)
  requires WFSimpleIter(self, preserved)
  ensures WFSimpleIter(UpdateByIter(self, it, value), preserved)
  {
    reveal_UpdateByIter();
    var self' := UpdateByIter(self, it, value);

    forall key | key in preserved.s
    ensures exists j | 0 <= j < preserved.i as int ::
        && self'.underlying.storage[j].Entry?
        && key == self'.underlying.storage[j].key
    {
      assert key in self.contents;
      var j :| 0 <= j < preserved.i as int
        && self.underlying.storage[j].Entry?
        && key == self.underlying.storage[j].key;
      assert self'.underlying.storage[j].Entry?;
      assert key == self'.underlying.storage[j].key;
    }
  }

  function setUpTo<V>(self: LinearHashMap<V>, i: int) : set<uint64>
  requires 0 <= i <= |self.underlying.storage|
  {
    set j | 0 <= j < i && self.underlying.storage[j].Entry?
        :: self.underlying.storage[j].key
  }

  lemma setUpToLeContents<V>(self: LinearHashMap<V>, i: int)
  requires Inv(self)
  requires 0 <= i <= |self.underlying.storage|
  ensures setUpTo(self, i) <= self.contents.Keys
  {
    forall j | 0 <= j < i && self.underlying.storage[j].Entry?
    ensures self.underlying.storage[j].key in self.contents
    {
      var key := self.underlying.storage[j].key;
      var slot := Slot(j);
      assert ValidSlot(|self.underlying.storage|, slot);
      CantEquivocateMapFromStorageKey(self.underlying);
      MapFromStorageProperties(self.underlying.storage, self.contents);
    }
  }

  function method {:opaque} FindSimpleIter<V>(shared self: LinearHashMap<V>, key: uint64)
    : (it : SimpleIterator)
  requires Inv(self)
  ensures WFSimpleIter(self, it)
  ensures key in self.contents ==> SimpleIterOutput(self, it) == Next(key, self.contents[key])
  ensures key !in self.contents ==> SimpleIterOutput(self, it) == Done
  {
    var idx := Probe(self.underlying, key);

    var i := if seq_get(self.underlying.storage, idx).Entry? then idx
      else seq_length(self.underlying.storage) as uint64;
    var it := SimpleIterator(i, setUpTo(self, i as int), (|self.underlying.storage| - i as int) as ORDINAL);

    assert WFSimpleIter(self, it)
      && (key in self.contents ==>
        SimpleIterOutput(self, it) == Next(key, self.contents[key]))
      && (key !in self.contents ==>
        SimpleIterOutput(self, it) == Done)
    by {
      var result := LemmaProbeResult(self.underlying, key);
      if it.i as int < |self.underlying.storage| {
        if self.underlying.storage[it.i].key in it.s {
          var j :| 0 <= j < it.i && self.underlying.storage[j].Entry?
              && self.underlying.storage[j].key == key;
          assert TwoNonEmptyValidSlotsWithSameKey(
              self.underlying.storage, Slot(j as int), Slot(it.i as int));
        }
      }
      setUpToLeContents(self, i as int);
    }

    it
  }

  method Clone<V>(shared self: LinearHashMap<V>) returns(linear self': LinearHashMap<V>)
    ensures self' == self
  {
    shared var LinearHashMap(underlying, count, contents) := self;
    shared var FixedSizeLinearHashMap(storage, fCount, fContents) := underlying;
    shared_seq_length_bound(storage);
    linear var storage' := AllocAndCopy(storage, 0, seq_length(storage));
    self' := LinearHashMap(FixedSizeLinearHashMap(storage', fCount, fContents), count, contents);
  }
}
