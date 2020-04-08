include "LinearSequence.s.dfy"
include "LinearSequence.i.dfy"

include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Sets.i.dfy"
include "../lib/Base/Maps.s.dfy"
include "../lib/Base/SetBijectivity.i.dfy"
include "../lib/Base/Arithmetic.s.dfy"
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

// module MutableMapModel {
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened Sets
  import opened Maps
  import opened SetBijectivity
  import opened NativeArithmetic
  import opened LinearSequence_s
  import opened LinearSequence_i

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

  function method StorageLength<V>(shared self: FixedSizeLinearHashMap<V>): nat
  {
    seq_length(self.storage)
  }

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
  requires 0 < StorageLength(self) < 0x1_0000_0000_0000_0000
  ensures ValidSlot(StorageLength(self), Slot(result as nat))
  ensures Slot(result as nat) == SlotForKey(StorageLength(self), key)
  {
    var h := hash64(key);
    h % (StorageLength(self) as uint64)
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
    && 128 <= StorageLength(self) < 0x1_0000_0000_0000_0000
    && (self.count as nat) < 0x1_0000_0000_0000_0000
    && self.count as nat < StorageLength(self)

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

  method ConstructorFromSize<V>(size: uint64) returns (linear self: FixedSizeLinearHashMap<V>)
  requires 128 <= size
  ensures FixedSizeInv(self)
  ensures forall slot :: ValidSlot(StorageLength(self), slot) ==> SlotIsEmpty(self.storage, slot)
  ensures self.contents == map[]
  ensures size as nat == StorageLength(self)
  {
    linear var storage := seq_alloc_init(size as nat, Empty);

    self := FixedSizeLinearHashMap(
     /* storage := */ storage,
     /* count := */ 0,
     /* contents := */ map[]);
  }

//   // TODO is this necessary in functional land?
//   // function ConstructorFromStorage<V>(storage: seq<Item<V>>, count: uint64) 
//   // : (self: FixedSizeLinearHashMap<V>)
//   // requires 128 <= |storage|
//   // ensures self.storage == storage
//   // ensures forall slot :: ValidSlot(StorageLength(self), slot) ==>
//   //   self.storage[slot.slot] == storage[slot.slot]
//   // ensures self.count == count
//   // ensures self.contents == map[]
//   // {
//   //   FixedSizeLinearHashMap(
//   //    /* storage := */ storage,
//   //    /* count := */ count,
//   //    /* contents := */ map[])
//   // }

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

  function method Uint64SlotSuccessor(elementsLength: nat, slot: uint64): (nextSlot: uint64)
  requires elementsLength < 0x1_0000_0000_0000_0000
  requires ValidSlot(elementsLength, Slot(slot as nat))
  ensures ValidSlot(elementsLength, Slot(nextSlot as nat))
  ensures Slot(nextSlot as nat) == SlotSuccessor(elementsLength, Slot(slot as nat))
  {
    if slot == (elementsLength as uint64) - 1 then
      0
    else
      slot + 1
  }

  lemma allNonEmptyImpliesCountEqStorageSize<V>(self: FixedSizeLinearHashMap<V>)
  requires FixedSizeInv(self)
  ensures (forall j | 0 <= j < StorageLength(self) :: !self.storage[j].Empty?)
      ==> self.count as int == StorageLength(self)
  {
    var elements := self.storage;
    if forall j | 0 <= j < StorageLength(self) :: !elements[j].Empty? {
      var elementIndices := set i | 0 <= i < StorageLength(self);
      assert IndexSetThrough(elements, StorageLength(self)) == elementIndices; // trigger
      CardinalityOfSetsOfSequenceIndices(elements, elementIndices);
      IndexSetMatchesContents(elements, self.contents);
    }
  }

  function {:opaque} getEmptyWitness<V>(self: FixedSizeLinearHashMap<V>, i: uint64) : (res : uint64)
  requires FixedSizeInv(self)
  requires 0 <= i as int <= StorageLength(self)
  requires forall j | 0 <= j < i :: !self.storage[j].Empty?
  requires self.count as int < StorageLength(self)
  decreases StorageLength(self) - i as int
  ensures 0 <= res as int < StorageLength(self)
  ensures self.storage[res].Empty?
  {
    allNonEmptyImpliesCountEqStorageSize(self);

    if self.storage[i].Empty? then
      i
    else
      getEmptyWitness(self, i+1)
  }

//  function ProbeIterate<V>(self: FixedSizeLinearHashMap<V>, key: uint64, slotIdx: uint64)
//      : (foundSlotIdx: uint64)
//  requires FixedSizeInv(self)
//  requires 0 <= slotIdx as int < StorageLength(self)
//
//  // We use the emptyWitness to prove termination.
//  // We will necessarily terminate when we reach this index,
//  // if not earlier.
//  decreases var wit := getEmptyWitness(self, 0);
//    if slotIdx > wit
//      then wit as int - slotIdx as int + StorageLength(self)
//      else wit as int - slotIdx as int
//
//  {
//    if self.storage[slotIdx].Empty? || self.storage[slotIdx].key == key then
//      slotIdx
//    else
//      ProbeIterate(self, key, Uint64SlotSuccessor(StorageLength(self), slotIdx))
//  }

//  function {:opaque} Probe<V>(self: FixedSizeLinearHashMap<V>, key: uint64): (foundSlotIdx: uint64)
//  requires FixedSizeInv(self)
//  requires self.count as int < StorageLength(self)
//  ensures 0 <= foundSlotIdx as int < StorageLength(self)
//  {
//    ProbeIterate(self, key, Uint64SlotForKey(self, key))
//  }

  function method IsTombstoneForKey<V>(item: Item<V>, key: uint64) : bool {
    item.Tombstone? && item.key == key
  }

  // function method IsValueForKey<V>(shared item: Item<V>) : bool {
  // }

  datatype ProbeResult<V> = ProbeResult(
      slotIdx: uint64,
      ghost startSlotIdx: uint64,
      ghost ghostSkips: uint64)

  method Probe<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64)
  returns (result : ProbeResult<V>)
  requires FixedSizeInv(self)
  ensures ValidSlot(StorageLength(self), Slot(result.slotIdx as nat))
  ensures ValidSlot(StorageLength(self), Slot(result.startSlotIdx as nat))
  ensures Slot(result.startSlotIdx as nat) == SlotForKey(StorageLength(self), key)
  ensures 0 <= result.ghostSkips
  ensures result.slotIdx as nat == KthSlotSuccessor(StorageLength(self), Slot(result.startSlotIdx as nat), result.ghostSkips as nat).slot
  ensures key in self.contents ==> SlotExplainsKey(self.storage, result.ghostSkips as nat, key)
  ensures key !in self.contents ==> FilledWithOtherKeys(self.storage, Slot(result.startSlotIdx as nat), result.ghostSkips as nat, key) && (self.storage[result.slotIdx].Empty? || (self.storage[result.slotIdx].Tombstone? && self.storage[result.slotIdx].key == key))
  ensures self.storage[result.slotIdx].Entry? ==> key in self.contents && key == self.storage[result.slotIdx].key
  ensures self.storage[result.slotIdx].Empty? ==> key !in self.contents
  {
    var slotIdx := Uint64SlotForKey(self, key);
    var startSlotIdx := slotIdx;
    ghost var startSlot := Slot(startSlotIdx as nat);

    ghost var viewFromStartSlot := View(self.storage, startSlotIdx as nat);
    ViewsHaveConsistentCounts(self.storage, viewFromStartSlot, startSlotIdx as nat);
    CountFilledMatchesIndexSet(self.storage);
    IndexSetMatchesContents(self.storage, self.contents);

    forall dist: nat | dist < StorageLength(self)
    ensures self.storage[KthSlotSuccessor(StorageLength(self), startSlot, dist).slot] == viewFromStartSlot[dist]
    {
      KthSlotSuccessorWrapsAround(StorageLength(self), startSlot, dist); // observe
    }

    var skips := 0;
    while true
      invariant skips < (StorageLength(self) as uint64)
      invariant slotIdx < (StorageLength(self) as uint64)
      invariant StorageLength(self) == |viewFromStartSlot|
      invariant self.storage[startSlotIdx..] + self.storage[..startSlotIdx] == viewFromStartSlot
      invariant slotIdx as nat == KthSlotSuccessor(StorageLength(self), startSlot, skips as nat).slot
      invariant skips < (StorageLength(self) as uint64) ==> self.storage[slotIdx] == viewFromStartSlot[skips]
      invariant ValidSlot(StorageLength(self), KthSlotSuccessor(StorageLength(self), startSlot, skips as nat))
      invariant FilledWithOtherKeys(self.storage, startSlot, skips as nat, key)
      invariant CountFilled(viewFromStartSlot[..skips]) == skips as nat

      // invariant Probe(self, key) == ProbeIterate(self, key, slotIdx)

      decreases var wit := getEmptyWitness(self, 0);
        if slotIdx > wit
          then wit as int - slotIdx as int + StorageLength(self)
          else wit as int - slotIdx as int
    {
      var item := seq_get(self.storage, slotIdx as nat);
      if item.Empty? || IsTombstoneForKey(item, key) {
        result := ProbeResult(slotIdx, startSlotIdx, skips);
        return;
      } else if item.key == key {
        assert EntryInSlotMatchesContents(self.storage, Slot(slotIdx as nat), self.contents); // observe
        result := ProbeResult(slotIdx, startSlotIdx, skips);
        return;
      } else {
        ghost var skipsBefore := skips;

        // -- increment --
        slotIdx := Uint64SlotSuccessor(StorageLength(self), slotIdx);
        skips := skips + 1;
        // ---------------

        assert viewFromStartSlot[..skips] == viewFromStartSlot[..skipsBefore] + [viewFromStartSlot[skipsBefore]]; // observe
        CountFilledAdditive(viewFromStartSlot[..skipsBefore], [viewFromStartSlot[skipsBefore]]);

        if skips == StorageLength(self) as uint64 {
          forall ensures false
          {
            calc {
              StorageLength(self);
              skips as nat;
              CountFilled(viewFromStartSlot[..skips]);
                { assert viewFromStartSlot[..skips] == viewFromStartSlot; } // observe
              CountFilled(viewFromStartSlot);
              |self.contents|;
              self.count as nat;
              < StorageLength(self);
            }
          }
        }
      }
    }
  }

  method FixedSizeInsert<V>(linear self: FixedSizeLinearHashMap, key: uint64, value: V)
      returns (linear self': FixedSizeLinearHashMap, replaced: Option<V>)
    requires FixedSizeInv(self)
    requires self.count as nat < StorageLength(self) - 1
    ensures FixedSizeInv(self')
    ensures self'.contents == self.contents[key := Some(value)]
    ensures (key in self.contents ==> replaced == self.contents[key])
    ensures (replaced.Some? ==> key in self.contents)
    ensures (key !in self.contents ==> replaced.None?)
    ensures |self'.storage| == StorageLength(self)
  {
    self' := self;
    // var ProbeResult(slotIdx, ghost startSlotIdx, ghost ghostSkips) := Probe(self, key);
    var probeResult := Probe(self', key);
    var slotIdx := probeResult.slotIdx;
    ghost var probeSkips := probeResult.ghostSkips;

    linear var FixedSizeLinearHashMap(selfStorage, selfCount, selfContents) := self';
    var itemReplaced: Item<V> := seq_get(selfStorage, slotIdx as int);
    selfStorage := seq_set(selfStorage, slotIdx as int, Entry(key, value));
    selfContents := selfContents[key := Some(value)];

    replaced := None;
    if itemReplaced.Empty? {
      self' := FixedSizeLinearHashMap(selfStorage, selfCount + 1, selfContents);
    } else if itemReplaced.Tombstone? {
      self' := FixedSizeLinearHashMap(selfStorage, selfCount, selfContents);
    } else { // Entry
      self' := FixedSizeLinearHashMap(selfStorage, selfCount, selfContents);
      replaced := Some(itemReplaced.value);
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

    // TODO (chris): commenting out the body of this forall causes >30s verification time
    //               with nothing being instantiated more than 500 times (as shown by the profiler)
    //               it's not heap reasoning but it's still extremely unpleasant
    forall slot | ValidSlot(|self'.storage|, slot) && self'.storage[slot.slot].Tombstone?
    ensures && var item := self'.storage[slot.slot];
            && self'.contents[item.key].None?
    {
      ghost var item := self'.storage[slot.slot];
      if slot != Slot(slotIdx as nat) {
        if item.key == key {
          assert TwoNonEmptyValidSlotsWithSameKey(self'.storage, slot, Slot(slotIdx as nat)); // observe
          assert SameSlot(|self'.storage|, slot, Slot(slotIdx as nat)); // observe
          assert false;
        }
      }
    }
  }

  method FixedSizeGet<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64) returns (found : Option<V>)
  requires FixedSizeInv(self)
  ensures if key in self.contents && self.contents[key].Some? then found == Some(self.contents[key].value) else found.None?
  {
    var probeResult := Probe(self, key);
    var slotIdx := probeResult.slotIdx;

    // TODO (chris) we had to break this out to a separate assignment, instead of inline expr
    //     if seq_get(self.storage, slotIdx as nat).Entry? {
    //     Error: expected ordinary expression, found shared expression
    var item := seq_get(self.storage, slotIdx as nat);
    if item.Entry? {
      found := Some(item.value);
    } else {
      found := None;
    }
  }

  method FixedSizeRemove<V>(linear self: FixedSizeLinearHashMap<V>, key: uint64) returns (linear self': FixedSizeLinearHashMap<V>, removed: Option<V>)
  requires FixedSizeInv(self)
  ensures FixedSizeInv(self')
  ensures (self'.contents == if key in self.contents
    then self.contents[key := None]
    else self.contents)
  ensures (removed == if key in self.contents && self.contents[key].Some?
    then Some(self.contents[key].value)
    else None)
  ensures (removed.Some? <==> (key in self.contents && self.contents[key].Some?))
  ensures (self'.count == self.count)
  {
    self' := self;

    var probeResult := Probe(self', key);
    var slotIdx := probeResult.slotIdx;
    ghost var probeStartSlotIdx := probeResult.startSlotIdx;
    ghost var probeSkips := probeResult.ghostSkips;

    var item := seq_get(self'.storage, slotIdx as nat);
    if item.Entry? {
      removed := Some(item.value);
      linear var FixedSizeLinearHashMap(selfStorage, selfCount, selfContents) := self';
      linear var newStorage := seq_set(selfStorage, slotIdx as nat, Tombstone(key));
      self' := FixedSizeLinearHashMap(
          newStorage,
          selfCount,
          selfContents[key := None]);

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
      removed := None;
    }
  }
// } // module
