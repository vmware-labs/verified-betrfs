// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../Lang/NativeTypes.s.dfy"
include "../Lang/System/Arithmetic.s.dfy"
include "../Base/SetBijectivity.i.dfy"
include "../Base/sequences.i.dfy"
include "../Base/Option.s.dfy"

module LinearMutableMapBase {
  import opened NativeTypes
  import opened SetBijectivity
  import opened NativeArithmetic
  import opened Options
  import opened Sequences

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

  predicate {:opaque} SomeSkipCountExplainsKey<V>(elements: seq<Item<V>>, key: uint64)
  requires ValidElements(elements)
  {
    exists skips :: SlotExplainsKey(elements, skips, key)
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

  predicate EntryExistsInElements<V>(elements: seq<Item<V>>, i: uint64, key: uint64)
  requires i as int <= |elements|
  requires ValidElements(elements)
  {
    && (exists slot: Slot :: ( && slot.slot < i as int
        && ValidSlot(|elements|, slot)
        && FilledWithEntryKey(elements, slot, key)))
  }

  lemma ElementsEntryInMap<V>(elements: seq<Item<V>>, item: Item<V>)
  requires item.Entry?
  requires item in elements
  ensures item.key in MapFromStorage(elements)
  {
  }
}