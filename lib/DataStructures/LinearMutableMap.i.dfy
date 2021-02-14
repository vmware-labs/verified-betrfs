include "../Lang/Inout.i.dfy"
include "../Lang/LinearSequence.s.dfy"
include "../Lang/LinearSequence.i.dfy"

include "../Lang/NativeTypes.s.dfy"
include "../Base/Option.s.dfy"
include "../Base/sequences.i.dfy"
include "../Base/Sets.i.dfy"
include "../Base/Maps.i.dfy"
include "LinearMutableMapBase.i.dfy"

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
  import opened Inout
  import opened Sets
  import opened Maps

  import opened LinearSequence_i
  import opened LinearSequence_s
  import opened LinearMutableMapBase

// begin generated export
  export Spec
    provides *
    reveals setUpTo, MapFromStorage, UnderlyingContentsMatchesContents, LinearHashMap, FixedSizeLinearHashMap, Iterator, NextExplainedByI, indexOutput, IteratorOutput, LinearHashMap.Inv, Inv0, EachReturnedKeyExplainedByPassedIndex, CantEquivocate, ValidIterIndex, ConstructorFromSize, ConstructorFromStorage, UnderlyingInv, KeyExplainedByPassedIndex, ValidI, Uint64SlotForKey, SimpleIterator
  export extends Spec
// end generated export

  linear datatype FixedSizeLinearHashMap<V> = FixedSizeLinearHashMap(
    linear storage: seq<Item<V>>,
    count: uint64,
    ghost contents: map<uint64, Option<V>>)

  protected predicate FixedSizeInv<V>(self: FixedSizeLinearHashMap<V>)
  {
    && 128 <= |self.storage| < 0x1_0000_0000_0000_0000
    && (self.count as nat) < 0x1_0000_0000_0000_0000
    && self.count as nat < |self.storage|

    && |self.contents| == (self.count as nat)
    && SeqMatchesContentKeys(self.storage, self.contents)
    && EntriesMatchContentValue(self.storage, self.contents)
    && TombstonesMatchContentValue(self.storage, self.contents)
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

  method Probe<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64)
  returns (slotIdx: uint64, ghost startSlotIdx: uint64, ghost skips: uint64)
  requires FixedSizeInv(self)
  requires self.count as int < |self.storage|
  ensures 0 <= slotIdx as int < |self.storage|
  ensures ValidSlot(|self.storage|, Slot(slotIdx as nat))
  ensures ValidSlot(|self.storage|, Slot(startSlotIdx as nat))
  ensures Slot(startSlotIdx as nat) == SlotForKey(|self.storage|, key)
  ensures 0 <= skips
  ensures slotIdx as nat == KthSlotSuccessor(|self.storage|, Slot(startSlotIdx as nat), skips as nat).slot
  ensures key in self.contents ==> SlotExplainsKey(self.storage, skips as nat, key)
  ensures key !in self.contents ==> FilledWithOtherKeys(self.storage, Slot(startSlotIdx as nat), skips as nat, key) && (self.storage[slotIdx].Empty? || (self.storage[slotIdx].Tombstone? && self.storage[slotIdx].key == key))
  ensures self.storage[slotIdx].Entry? ==> key in self.contents && key == self.storage[slotIdx].key
  ensures self.storage[slotIdx].Empty? ==> key !in self.contents
  {
    slotIdx := Uint64SlotForKey(self, key);
    startSlotIdx := slotIdx;
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

    skips := 0;

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
    decreases var wit := getEmptyWitness(self, 0);
      if slotIdx > wit
        then wit as int - slotIdx as int + |self.storage|
        else wit as int - slotIdx as int
    {
      ghost var skipsBefore := skips;

      if seq_get(self.storage, slotIdx).Empty? || (seq_get(self.storage, slotIdx).Tombstone? && seq_get(self.storage, slotIdx).key == key) {
        assert key in self.contents ==> SlotExplainsKey(self.storage, skips as nat, key) by {
          reveal_SomeSkipCountExplainsKey();
        }
        return;
      } else if seq_get(self.storage, slotIdx).key == key {
        assert EntryInSlotMatchesContents(self.storage, Slot(slotIdx as nat), self.contents); // observe
        return;
      }

      // -- increment --
      slotIdx := Uint64SlotSuccessorUint64(seq_length(self.storage), slotIdx);
      skips := skips + 1;
      // ---------------

      assert viewFromStartSlot[..skips] == viewFromStartSlot[..skipsBefore] + [viewFromStartSlot[skipsBefore]]; // observe
      CountFilledAdditive(viewFromStartSlot[..skipsBefore], [viewFromStartSlot[skipsBefore]]);
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

  method FixedSizeInsert<V>(linear inout self: FixedSizeLinearHashMap, key: uint64, value: V)
  returns (replaced: Option<V>)
    requires FixedSizeInv(old_self)
    requires old_self.count as nat < |old_self.storage| - 1
    ensures (
      && FixedSizeInv(self)
      && self.contents == old_self.contents[key := Some(value)]
      && (key in old_self.contents ==> replaced == old_self.contents[key])
      && (replaced.Some? ==> key in old_self.contents)
      && (key !in old_self.contents ==> replaced.None?)
      && |self.storage| == |old_self.storage|)
  {
    var slotIdx;
    ghost var probeStartSlotIdx, probeSkips;
    slotIdx, probeStartSlotIdx, probeSkips := Probe(self, key);

    inout ghost self.contents := self.contents[key := Some(value)];

    var replacedItem := seq_get(self.storage, slotIdx);
    mut_seq_set(inout self.storage, slotIdx, Entry(key, value));

    if replacedItem.Empty? {
      inout self.count := self.count + 1;
    }

    if replacedItem.Entry? {
      replaced := Some(replacedItem.value);
    } else {
      replaced := None;
    }

    forall explainedKey | explainedKey in self.contents
    ensures exists skips :: SlotExplainsKey(self.storage, skips, explainedKey)
    {
      if key == explainedKey {
        assert SlotExplainsKey(self.storage, probeSkips as nat, key); // observe
      } else {
        reveal_SomeSkipCountExplainsKey();
        var oldSkips :| SlotExplainsKey(old_self.storage, oldSkips, explainedKey);
        assert SlotExplainsKey(self.storage, oldSkips, explainedKey); // observe
      }
    }

    forall slot | ValidSlot(|self.storage|, slot) && self.storage[slot.slot].Entry?
    ensures && var item := self.storage[slot.slot];
            && self.contents[item.key] == Some(item.value)
    {
      var item := self.storage[slot.slot];
      if slot != Slot(slotIdx as nat) {
        if item.key == key {
          assert TwoNonEmptyValidSlotsWithSameKey(self.storage, slot, Slot(slotIdx as nat)); // observe
          assert SameSlot(|self.storage|, slot, Slot(slotIdx as nat)); // observe
          assert false;
        }
      }
    }
    forall slot | ValidSlot(|self.storage|, slot) && self.storage[slot.slot].Tombstone?
    ensures && var item := self.storage[slot.slot];
            && self.contents[item.key].None?
    {
      var item := self.storage[slot.slot];
      if slot != Slot(slotIdx as nat) {
        if item.key == key {
          assert TwoNonEmptyValidSlotsWithSameKey(self.storage, slot, Slot(slotIdx as nat)); // observe
          assert SameSlot(|self.storage|, slot, Slot(slotIdx as nat)); // observe
          assert false;
        }
      }
    }
    assert SeqMatchesContentKeys(self.storage, self.contents) by {
      reveal_SomeSkipCountExplainsKey();
    }
  }

  method FixedSizeUpdateBySlot<V>(linear inout self: FixedSizeLinearHashMap<V>, slotIdx: uint64, value: V)
  requires FixedSizeInv(old_self)
  requires 0 <= slotIdx as int < |old_self.storage|
  requires old_self.storage[slotIdx].Entry?
  ensures FixedSizeInv(self)
  ensures |self.storage| == |old_self.storage|
  ensures self.storage == old_self.storage[slotIdx as nat := Entry(old_self.storage[slotIdx].key, value)]
  ensures self.contents == old_self.contents[old_self.storage[slotIdx].key := Some(value)]
  {
    var entry := seq_get(self.storage, slotIdx);
    mut_seq_set(inout self.storage, slotIdx, entry.(value := value));
    inout ghost self.contents := self.contents[self.storage[slotIdx].key := Some(value)];

    ghost var old_self := old_self; // TODO(andrea)
    ghost var key := old_self.storage[slotIdx].key;
    assert EntryInSlotMatchesContents(old_self.storage, Slot(slotIdx as int), old_self.contents);
    assert key in old_self.contents;
    calc {
      |old_self.contents|;
      |old_self.contents.Keys|;
      |self.contents.Keys|;
      |self.contents.Keys|;
    }

    forall explainedKey | explainedKey in self.contents
    ensures exists skips :: SlotExplainsKey(self.storage, skips, explainedKey)
    {
      reveal_SomeSkipCountExplainsKey();
      var oldSkips :| SlotExplainsKey(old_self.storage, oldSkips, explainedKey);
      assert SlotExplainsKey(self.storage, oldSkips, explainedKey); // observe
    }

    forall slot | ValidSlot(|self.storage|, slot)
        && SlotIsEntry(self.storage, slot)
    ensures EntryInSlotMatchesContents(self.storage, slot, self.contents)
    {
      assert EntryInSlotMatchesContents(old_self.storage, slot, old_self.contents);
      if slot.slot == slotIdx as int {
        assert self.contents[self.storage[slot.slot].key] == Some(self.storage[slot.slot].value);
      } else {
        calc {
          self.contents[self.storage[slot.slot].key];
          {
            assert old_self.storage[slot.slot].key
                == self.storage[slot.slot].key;
            if old_self.storage[slot.slot].key == key {
              assert TwoNonEmptyValidSlotsWithSameKey(old_self.storage, slot, Slot(slotIdx as int));
            }
          }
          old_self.contents[old_self.storage[slot.slot].key];
          Some(old_self.storage[slot.slot].value);
          Some(self.storage[slot.slot].value);
        }
      }
    }

    reveal_SomeSkipCountExplainsKey();
  }

  method FixedSizeGet<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64)
  returns (found : Option<V>)
  requires FixedSizeInv(self)
  ensures if key in self.contents && self.contents[key].Some?
    then found == Some(self.contents[key].value)
    else found.None?
  {
    var slotIdx, _, _ := Probe(self, key);

    if seq_get(self.storage, slotIdx).Entry? {
      found := Some(seq_get(self.storage, slotIdx).value);
    } else {
      found := None;
    }
  }

  method FixedSizeRemove<V>(linear inout self: FixedSizeLinearHashMap<V>, key: uint64)
  returns (removed: Option<V>)
  requires FixedSizeInv(old_self)
  ensures FixedSizeInv(self)
  ensures (self.contents == if key in old_self.contents
    then old_self.contents[key := None]
    else old_self.contents)
  ensures (removed == if key in old_self.contents && old_self.contents[key].Some?
    then Some(old_self.contents[key].value)
    else None)
  ensures (removed.Some? <==> (key in old_self.contents && old_self.contents[key].Some?))
  ensures (self.count == old_self.count)
  {
    ghost var probeStartSlotIdx, probeSkips;
    var slotIdx;
    slotIdx, probeStartSlotIdx, probeSkips := Probe(self, key);

    if seq_get(self.storage, slotIdx).Entry? {
      removed := Some(seq_get(self.storage, slotIdx).value);
      mut_seq_set(inout self.storage, slotIdx, Tombstone(key));
      inout ghost self.contents := self.contents[key := None];
    } else {
      removed := None;
    }

    ghost var old_self := old_self; // TODO(andrea) is there something we can do about this?
    if old_self.storage[slotIdx].Entry? {
      forall explainedKey | explainedKey in self.contents
      ensures exists skips :: SlotExplainsKey(self.storage, skips, explainedKey)
      {
        if key == explainedKey {
          assert SlotExplainsKey(self.storage, probeSkips as nat, key);
        } else {
          reveal_SomeSkipCountExplainsKey();
          var oldSkips :| SlotExplainsKey(old_self.storage, oldSkips, explainedKey);
          assert SlotExplainsKey(self.storage, oldSkips, explainedKey);
        }
      }

      forall slot | ValidSlot(|self.storage|, slot) && self.storage[slot.slot].Entry?
      ensures && var item := self.storage[slot.slot];
              && self.contents[item.key] == Some(item.value)
      {
        var item := self.storage[slot.slot];
        if slot != Slot(slotIdx as nat) {
          if item.key == key {
            assert CantEquivocateStorageKey(self.storage);
            assert TwoNonEmptyValidSlotsWithSameKey(self.storage, slot, Slot(slotIdx as nat));
            assert false;
          }
        }
      }
      assert SeqMatchesContentKeys(self.storage, self.contents) by {
        reveal_SomeSkipCountExplainsKey();
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
    assert MapFromStorage(underlying.storage) == contents by {
      reveal_SomeSkipCountExplainsKey();
    }
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

  method Realloc<V>(linear inout self: LinearHashMap<V>)
    requires Inv(old_self)
    requires old_self.count as nat < 0x1_0000_0000_0000_0000 / 8
    ensures Inv(self)
    ensures self.contents == old_self.contents
    ensures self.underlying.count as nat < |self.underlying.storage| - 2
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
        var replaced := FixedSizeInsert(inout newUnderlying, item.key, item.value); // use mutable ref here
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

    // linear var LinearHashMap(selfUnderlying, selfCount, selfContents) := self;
    // self' := LinearHashMap(newUnderlying, selfCount, selfContents);
    linear var oldUnderlying := Replace(inout self.underlying, newUnderlying);
    linear var FixedSizeLinearHashMap(oldStorage, _, _) := oldUnderlying;
    var _ := seq_free(oldStorage);

    assert self.contents == transferredContents;

    assert UnderlyingContentsMatchesContents(newUnderlying, self.contents);
    assert forall key :: key in old_self.contents ==> key in newUnderlying.contents && newUnderlying.contents[key] == Some(old_self.contents[key]);
    assert forall key :: key !in old_self.contents ==> key !in newUnderlying.contents || newUnderlying.contents[key].None?;

  }

  method InsertAndGetOld<V>(linear inout self: LinearHashMap, key: uint64, value: V)
  returns (replaced: Option<V>)
    requires Inv(old_self)
    requires old_self.count as nat < 0x1_0000_0000_0000_0000 / 8
    ensures Inv(self)
    ensures self.contents == old_self.contents[key := value]
    ensures self.count as nat == old_self.count as nat + (if replaced.Some? then 0 else 1)
    ensures replaced.Some? ==> MapsTo(old_self.contents, key, replaced.value)
    ensures replaced.None? ==> key !in old_self.contents
  {
    // -- mutation --
    if seq_length(self.underlying.storage) as uint64 / 2 <= self.underlying.count {
      Realloc(inout self);
    }
    // --------------

    // -- mutation --
    // linear var LinearHashMap(self1Underlying, self1Count, self1Contents) := self1;
    replaced := FixedSizeInsert(inout self.underlying, key, value);
    inout ghost self.contents := self.contents[key := value];
    if replaced.None? {
      inout self.count := self.count + 1;
    }
    // --------------

    UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents);
  }

  method Insert<V>(linear inout self: LinearHashMap, key: uint64, value: V)
    requires Inv(old_self)
    requires old_self.count as nat < 0x1_0000_0000_0000_0000 / 8
    ensures Inv(self)
    ensures self.contents == old_self.contents[key := value]
    ensures (self.count as nat == old_self.count as nat ||
       self.count as nat == old_self.count as nat + 1)
  {
    var replaced := InsertAndGetOld(inout self, key, value);
  }

  method RemoveAndGet<V>(linear inout self: LinearHashMap, key: uint64)
  returns (removed: Option<V>)
    requires Inv(old_self)
    ensures Inv(self)
    ensures (self.contents == if key in old_self.contents
      then map k | k in old_self.contents && k != key :: old_self.contents[k]
      else old_self.contents)
    ensures (removed == if key in old_self.contents
      then Some(old_self.contents[key])
      else None)
    ensures (self.count == if key in old_self.contents then old_self.count - 1 else old_self.count)
  {
    removed := FixedSizeRemove(inout self.underlying, key);
    if removed.Some? {
      inout self.count := self.count - 1;
    }
    inout ghost self.contents := map k | k in self.contents && k != key :: self.contents[k];

    if removed.Some? {
      assert |old_self.contents.Keys - {key}| == |old_self.contents.Keys| - |{key}|; // observe
      assert old_self.contents.Keys - {key} == self.contents.Keys; // observe
    } else {
      assert self.contents == old_self.contents; // observe
    }
    // assert |self.contents| == self.count as nat; // goal

    // TODO RemoveCountCorrect(self, key, RemoveResult(self', removed));
    assert self.count as nat == |self.contents|;
    assert UnderlyingContentsMatchesContents(self.underlying, self.contents);
    UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents); 
  }

  method Remove<V>(linear inout self: LinearHashMap, key: uint64)
    requires Inv(old_self)
    ensures
      && Inv(self)
      && (self.contents == if key in old_self.contents
        then map k | k in old_self.contents && k != key :: old_self.contents[k]
        else old_self.contents)
  {
    var _ := RemoveAndGet(inout self, key);
  }

  method Get<V>(shared self: LinearHashMap, key: uint64)
  returns (found: Option<V>)
    requires Inv(self)
    ensures if key in self.contents then found == Some(self.contents[key]) else found.None?
    ensures found.Some? <==> key in self.contents
  {
    found := FixedSizeGet(self.underlying, key);
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

  predicate ValidIterIndex<V>(self: LinearHashMap<V>, i: nat)
  {
    i <= |self.underlying.storage|
  }

  predicate ValidI<V>(self: LinearHashMap<V>, it: Iterator<V>)
  {
    && ValidIterIndex(self, it.i as nat)
  }

  predicate KeyExplainedByPassedIndex<V>(self: LinearHashMap<V>, i: nat, key: uint64)
  requires ValidElements(self.underlying.storage)
  requires ValidIterIndex(self, i)
  {
    exists j | 0 <= j < i :: FilledWithEntryKey(self.underlying.storage, Slot(j), key)
  }

  predicate EachReturnedKeyExplainedByPassedIndex<V>(self: LinearHashMap<V>, s: set<uint64>, i: nat)
  requires ValidElements(self.underlying.storage)
  requires ValidIterIndex(self, i)
  {
    forall key | key in s :: KeyExplainedByPassedIndex(self, i, key) 
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
    && ValidElements(self.underlying.storage)
    // Each passed index appears in s
    && (forall j | 0 <= j < it.i as int ::
        self.underlying.storage[j].Entry? ==> self.underlying.storage[j].key in it.s)
    && EachReturnedKeyExplainedByPassedIndex(self, it.s, it.i as nat)
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
    && ValidElements(self.underlying.storage)
    // Each passed index appears in s
    && (forall j | 0 <= j < it.i as int ::
        self.underlying.storage[j].Entry? ==> self.underlying.storage[j].key in it.s)
    && EachReturnedKeyExplainedByPassedIndex(self, it.s, it.i as nat)
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
  requires EachReturnedKeyExplainedByPassedIndex(self, it.s, it.i as nat)
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

  method iterToNext<V>(shared self: LinearHashMap<V>, i: uint64) returns (i': uint64, output: IteratorOutput)
  requires Inv(self)
  requires 0 <= i as int <= |self.underlying.storage|
  ensures NextExplainedByI(self, i', output)
  ensures forall j | i <= j < i' :: !self.underlying.storage[j].Entry?
  ensures i <= i'
  ensures output.Next? ==> MapsTo(self.contents, output.key, output.value)
  decreases |self.underlying.storage| - i as int
  {
    i' := i;

    while true
    invariant 0 <= i' as int <= |self.underlying.storage|
    invariant forall j | i <= j < i' :: !self.underlying.storage[j].Entry?
    invariant i <= i'
    decreases |self.underlying.storage| - i' as int
    {
      if i' == seq_length(self.underlying.storage) {
        output := Done;
        return;
      } else if seq_get(self.underlying.storage, i').Entry? {
        output := Next(seq_get(self.underlying.storage, i').key, seq_get(self.underlying.storage, i').value);
        UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents);
        CantEquivocateMapFromStorageKey(self.underlying);
        MapFromStorageProperties(self.underlying.storage, self.contents);
        assert Slot(i' as int).slot == i' as nat; // trigger
        return;
      }
      i' := i' + 1;
    }
  }

  method simpleIterToNext<V>(shared self: LinearHashMap<V>, i: uint64) returns (i': uint64)
  requires Inv(self)
  requires 0 <= i as int <= |self.underlying.storage|
  ensures 0 <= i' as int <= |self.underlying.storage|
  ensures forall j | i <= j < i' :: !self.underlying.storage[j].Entry?
  ensures i' as int < |self.underlying.storage| ==> self.underlying.storage[i'].Entry?
  ensures i' as int < |self.underlying.storage| ==> (
    var output := self.underlying.storage[i'];
    MapsTo(self.contents, output.key, output.value)
  )
  ensures i <= i'
  {
    i' := i;

    while true
    invariant 0 <= i' as int <= |self.underlying.storage|
    invariant forall j | i <= j < i' :: !self.underlying.storage[j].Entry?
    decreases |self.underlying.storage| - i' as int
    {
      if i' == seq_length(self.underlying.storage) {
        return;
      } else if seq_get(self.underlying.storage, i').Entry? {
        ghost var output := self.underlying.storage[i'];
        UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents);
        CantEquivocateMapFromStorageKey(self.underlying);
        MapFromStorageProperties(self.underlying.storage, self.contents);
        assert Slot(i' as int).slot == i' as nat; // trigger
        return;
      }
      i' := i' + 1;
    }
  }


  method IterStart<V>(shared self: LinearHashMap<V>) returns (it' : Iterator<V>)
  requires Inv(self)
  ensures WFIter(self, it')
  ensures it'.s == {}
  {
    var i, next := iterToNext(self, 0);
    it' := Iterator(i, {}, (|self.underlying.storage| - i as int) as ORDINAL, next);

    LemmaIterNextNotInS(self, it');

    reveal_SomeSkipCountExplainsKey();
  }

  method SimpleIterStart<V>(shared self: LinearHashMap<V>) returns (it' : SimpleIterator)
  requires Inv(self)
  ensures WFSimpleIter(self, it')
  ensures it'.s == {}
  {
    var i := simpleIterToNext(self, 0);
    it' := SimpleIterator(i, {}, (|self.underlying.storage| - i as int) as ORDINAL);

    LemmaIterNextNotInS(self,
      Iterator(it'.i, it'.s, it'.decreaser, indexOutput(self, it'.i)));

    reveal_SomeSkipCountExplainsKey();
  }

  method IterInc<V>(shared self: LinearHashMap<V>, it: Iterator) returns (it' : Iterator)
  requires Inv(self)
  requires WFIter(self, it)
  requires it.next.Next?
  ensures WFIter(self, it')
  ensures it'.s == it.s + {it.next.key}
  ensures it'.next.Done? ==> it'.s == self.contents.Keys
  ensures it'.decreaser < it.decreaser
  {
    var i, next := iterToNext(self, it.i + 1);
    it' := Iterator(i, it.s + {it.next.key}, (|self.underlying.storage| - i as int) as ORDINAL, next);

    assert FilledWithEntryKey(self.underlying.storage, Slot(it.i as nat), it.next.key);
    // assert EachReturnedKeyExplainedByPassedIndex(self, it'.s, it'.i as nat); // goal

    LemmaIterNextNotInS(self, it');

    assert (it'.next.Done? ==> it'.s == self.contents.Keys) by {
      reveal_SomeSkipCountExplainsKey();
    }
  }

  method SimpleIterInc<V>(shared self: LinearHashMap<V>, it: SimpleIterator) returns (it' : SimpleIterator)
  requires Inv(self)
  requires WFSimpleIter(self, it)
  requires SimpleIterOutput(self, it).Next?
  ensures WFSimpleIter(self, it')
  ensures it'.s == it.s + {SimpleIterOutput(self, it).key}
  ensures it'.decreaser < it.decreaser
  {
    var i := simpleIterToNext(self, it.i + 1);
    it' := SimpleIterator(i, it.s + {SimpleIterOutput(self, it).key}, (|self.underlying.storage| - i as int) as ORDINAL);

    assert FilledWithEntryKey(self.underlying.storage, Slot(it.i as nat), SimpleIterOutput(self, it).key);
    // assert EachReturnedKeyExplainedByPassedIndex(self, it'.s, it'.i as nat); // goal

    LemmaIterNextNotInS(self,
      Iterator(it'.i, it'.s, it'.decreaser, indexOutput(self, it'.i)));

    assert (it'.i as int == |self.underlying.storage| ==> (it'.s == self.contents.Keys)) by {
      reveal_SomeSkipCountExplainsKey();
    }
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

  method MaxKey<V>(shared self: LinearHashMap<V>) returns (maxK : uint64)
  requires Inv(self)
  ensures forall key | key in self.contents :: key <= maxK
  {
    var it := IterStart(self);

    while it.next.Next?
    invariant WFIter(self, it)
    invariant forall key | key in it.s :: key <= maxK
    decreases it.decreaser
    {
      var key := it.next.key;
      maxK := if maxK < key then key else maxK;
      it := IterInc(self, it);
    }
  }

  method UpdateByIter<V>(linear inout self: LinearHashMap<V>, it: SimpleIterator, value: V)
  requires Inv(old_self)
  requires WFSimpleIter(old_self, it)
  requires SimpleIterOutput(old_self, it).Next?
  ensures Inv(self)
  ensures self.contents == old_self.contents[SimpleIterOutput(old_self, it).key := value]
  ensures self.count == old_self.count
  ensures WFSimpleIter(self, it)
  ensures forall preserved :: WFSimpleIter(old_self, preserved) ==> (
    && WFSimpleIter(self, preserved)
    && ((it.i == preserved.i) ==>
        (SimpleIterOutput(self, preserved).key == SimpleIterOutput(old_self, preserved).key))
  )
  {
    ghost var key := SimpleIterOutput(self, it).key;
    FixedSizeUpdateBySlot(inout self.underlying, it.i, value);
    inout ghost self.contents := self.contents[key := value];
    UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents);
  
    forall preserved | WFSimpleIter(old_self, preserved) ensures WFSimpleIter(self, preserved) {
      forall key | key in preserved.s
      ensures exists j | 0 <= j < preserved.i as int ::
      && self.underlying.storage[j].Entry?
      && key == self.underlying.storage[j].key
      {
        assert key in old_self.contents;
        var j :| 0 <= j < preserved.i as int
        && old_self.underlying.storage[j].Entry?
        && key == old_self.underlying.storage[j].key;
        assert self.underlying.storage[j].Entry?;
        assert key == self.underlying.storage[j].key;
      }
    }
  }

  function setUpTo<V>(self: LinearHashMap<V>, i: int) : set<uint64>
  requires 0 <= i <= |self.underlying.storage|
  {
    set j | 0 <= j < i && self.underlying.storage[j].Entry?
        :: self.underlying.storage[j].key
  }

  lemma setUpToEachKeyExplainedByPassedIndex<V>(self: LinearHashMap<V>, i: nat)
  requires ValidElements(self.underlying.storage)
  requires ValidIterIndex(self, i)
  ensures EachReturnedKeyExplainedByPassedIndex(self, setUpTo(self, i), i)
  {
    forall key | key in setUpTo(self, i)
    ensures KeyExplainedByPassedIndex(self, i, key)
    {
      var j :| 0 <= j < i && self.underlying.storage[j].Entry? && key == self.underlying.storage[j].key;
      assert FilledWithEntryKey(self.underlying.storage, Slot(j), key);
    }
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

  method FindSimpleIter<V>(shared self: LinearHashMap<V>, key: uint64)
  returns (it : SimpleIterator)
  requires Inv(self)
  ensures WFSimpleIter(self, it)
  ensures key in self.contents ==> SimpleIterOutput(self, it) == Next(key, self.contents[key])
  ensures key !in self.contents ==> SimpleIterOutput(self, it) == Done
  {
    var idx, _, _ := Probe(self.underlying, key);

    var i := if seq_get(self.underlying.storage, idx).Entry? then idx
      else seq_length(self.underlying.storage) as uint64;
    it := SimpleIterator(i, setUpTo(self, i as int), (|self.underlying.storage| - i as int) as ORDINAL);

    assert WFSimpleIter(self, it)
      && (key in self.contents ==>
        SimpleIterOutput(self, it) == Next(key, self.contents[key]))
      && (key !in self.contents ==>
        SimpleIterOutput(self, it) == Done)
    by {
      if it.i as int < |self.underlying.storage| {
        if self.underlying.storage[it.i].key in it.s {
          var j :| 0 <= j < it.i && self.underlying.storage[j].Entry?
              && self.underlying.storage[j].key == key;
          assert TwoNonEmptyValidSlotsWithSameKey(
              self.underlying.storage, Slot(j as int), Slot(it.i as int));
        }
      }
      setUpToLeContents(self, i as int);
      setUpToEachKeyExplainedByPassedIndex(self, i as nat);
    }
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
