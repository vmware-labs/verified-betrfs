include "../Lang/LinearSequence.s.dfy"
include "../Lang/LinearSequence.i.dfy"
include "../Base/LinearOption.i.dfy"
include "../Lang/Inout.i.dfy"

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

module LinearContentMutableMap {
  import opened NativeTypes
  import opened Options
  import opened LinearOption
  import opened Sequences
  import opened Sets
  import opened Maps

  import opened LinearSequence_i
  import opened LinearSequence_s
  import opened Inout
  import opened Base = LinearMutableMapBase

// begin generated export
  export Spec
    provides *
    reveals LinearHashMap, FixedSizeLinearHashMap, IsConstructor, UnderlyingInv, lItem, IsRealloc, Uint64SlotForKey, UnderlyingContentsMatchesContents, LinearHashMap.Inv, IsConstructorFromSize, Inv0
  export extends Spec
// end generated export

  linear datatype lItem<V> = Empty | Entry(key: uint64, linear value: V) | Tombstone(key: uint64)
  {
    linear method FreeNonEntry()
    requires !this.Entry? 
    {
      linear match this {
        case Empty() => 
        case Tombstone(key) =>
      }
    }

    /* protected */
    function toItem(): Item<V>
    {
      match this {
        case Empty() => Base.Empty()
        case Entry(key, value) => Base.Entry(key, value)
        case Tombstone(key) => Base.Tombstone(key)
      }
    }
  }

  /* protected */
  function toItems<V>(litems: lseq<lItem<V>>): (items: seq<Item<V>>)
  ensures |items| == |litems|
  {
    var elements := lseqs(litems);
    seq (|elements|, i requires 0 <= i < |elements| => elements[i].toItem())
  }

  linear datatype FixedSizeLinearHashMap<V> = FixedSizeLinearHashMap(
    linear storage: lseq<lItem<V>>,
    count: uint64,
    ghost contents: map<uint64, Option<V>>)

  function method Uint64SlotForKey<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64): (result: uint64)
  requires 0 < |self.storage| < 0x1_0000_0000_0000_0000
  ensures ValidSlot(|self.storage|, Slot(result as nat))
  ensures Slot(result as nat) == SlotForKey(|self.storage|, key)
  {
    var h := hash64(key);
    var storageLength := lseq_length_as_uint64(self.storage);
    h % (storageLength as uint64)
  }

  /* protected */
  predicate FixedSizeInv<V>(self: FixedSizeLinearHashMap<V>)
  {
    && 128 <= |self.storage| < 0x1_0000_0000_0000_0000
    && (self.count as nat) < 0x1_0000_0000_0000_0000
    && self.count as nat < |self.storage|

    && |self.contents| == (self.count as nat)
    && lseq_has_all(self.storage)
    && SeqMatchesContentKeys(toItems(self.storage), self.contents)
    && EntriesMatchContentValue(toItems(self.storage), self.contents)
    && TombstonesMatchContentValue(toItems(self.storage), self.contents)
  }

  predicate IsConstructorFromSize<V>(size: nat, self: FixedSizeLinearHashMap<V>)  
  {
    && |self.storage| == size
    && self.count == 0
    && self.contents == map[]
    && (forall slot :: ValidSlot(|self.storage|, slot) ==> SlotIsEmpty(toItems(self.storage), slot))
    && FixedSizeInv(self)
  }

  method ConstructorFromSize<V>(size: uint64) returns (linear self: FixedSizeLinearHashMap<V>)
  requires 128 <= size
  ensures IsConstructorFromSize(size as nat, self)
  {
    linear var storage := lseq_alloc(size);

    var i := 0 as uint64;
    while i < size
      invariant i <= size
      invariant size as nat == |storage|
      invariant forall j | 0 <= j < i as nat :: lseq_has(storage)[j]
      invariant forall j | i as nat <= j < size as nat :: !lseq_has(storage)[j]
      invariant forall slot :: ValidSlot(|storage|, slot) && 0 <= slot.slot < i as nat 
          ==> SlotIsEmpty(toItems(storage), slot)
    {
      linear var item := lItem.Empty();
      lseq_give_inout(inout storage, i, item);
      i := i + 1;
    }

    self := FixedSizeLinearHashMap(
     /* storage := */ storage,
     /* count := */ 0,
     /* contents := */ map[]);
  }

  lemma allNonEmptyImpliesCountEqStorageSize<V>(self: FixedSizeLinearHashMap<V>)
  requires FixedSizeInv(self)
  ensures (forall j | 0 <= j < |self.storage| :: !self.storage[j].Empty?)
      ==> self.count as int == |self.storage|
  {
    var elements := self.storage;
    if forall j | 0 <= j < |elements| :: !elements[j].Empty? {
      var elementIndices := set i | 0 <= i < |elements|;
      assert IndexSetThrough(toItems(elements), |elements|) == elementIndices; // trigger
      CardinalityOfSetsOfSequenceIndices(toItems(elements), elementIndices);
      IndexSetMatchesContents(toItems(elements), self.contents);
    }
  }

  function {:opaque} getEmptyWitness<V>(self: FixedSizeLinearHashMap<V>, i: uint64) : (res : uint64)
  requires FixedSizeInv(self)
  requires 0 <= i as int <= |self.storage|
  requires forall j | 0 <= j < i as int :: !self.storage[j].Empty?
  requires self.count as int < |self.storage|
  decreases |self.storage| - i as int
  ensures 0 <= res as int < |self.storage|
  ensures self.storage[res as int].Empty?
  {
    allNonEmptyImpliesCountEqStorageSize(self);

    if self.storage[i as int].Empty? then
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
  ensures key in self.contents ==> SlotExplainsKey(toItems(self.storage), skips as nat, key)
  ensures key !in self.contents ==> FilledWithOtherKeys(toItems(self.storage), Slot(startSlotIdx as nat), skips as nat, key) && (self.storage[slotIdx as nat].Empty? || (self.storage[slotIdx as nat].Tombstone? && self.storage[slotIdx as nat].key == key))
  ensures self.storage[slotIdx as nat].Entry? ==> key in self.contents && key == self.storage[slotIdx as nat].key
  ensures self.storage[slotIdx as nat].Empty? ==> key !in self.contents
  {
    slotIdx := Uint64SlotForKey(self, key);
    startSlotIdx := slotIdx;
    ghost var startSlot := Slot(startSlotIdx as nat);

    ghost var viewFromStartSlot := View(toItems(self.storage), startSlotIdx as nat);
    ViewsHaveConsistentCounts(toItems(self.storage), viewFromStartSlot, startSlotIdx as nat);
    CountFilledMatchesIndexSet(toItems(self.storage));
    IndexSetMatchesContents(toItems(self.storage), self.contents);

    forall dist: nat | dist < |self.storage|
    ensures self.storage[KthSlotSuccessor(|self.storage|, startSlot, dist).slot].toItem() == viewFromStartSlot[dist]
    {
      KthSlotSuccessorWrapsAround(|self.storage|, startSlot, dist); // observe
    }

    skips := 0;

    while true
    invariant skips < (|self.storage| as uint64)
    invariant slotIdx < (|self.storage| as uint64)
    invariant |self.storage| == |viewFromStartSlot|
    invariant toItems(self.storage)[startSlotIdx..] + toItems(self.storage)[..startSlotIdx] == viewFromStartSlot
    invariant slotIdx as nat == KthSlotSuccessor(|self.storage|, startSlot, skips as nat).slot
    invariant skips < (|self.storage| as uint64) ==> self.storage[slotIdx as nat].toItem() == viewFromStartSlot[skips]
    invariant ValidSlot(|self.storage|, KthSlotSuccessor(|self.storage|, startSlot, skips as nat))
    invariant FilledWithOtherKeys(toItems(self.storage), startSlot, skips as nat, key)
    invariant CountFilled(viewFromStartSlot[..skips]) == skips as nat
    decreases var wit := getEmptyWitness(self, 0);
      if slotIdx > wit
        then wit as int - slotIdx as int + |self.storage|
        else wit as int - slotIdx as int
    {
      ghost var skipsBefore := skips;
      shared var entry := lseq_peek(self.storage, slotIdx);
      if entry.Empty? || (entry.Tombstone? && entry.key == key) {
        assert key in self.contents ==> SlotExplainsKey(toItems(self.storage), skips as nat, key) by {
          reveal_SomeSkipCountExplainsKey();
        }
        return;
      } else if entry.key == key {
        assert EntryInSlotMatchesContents(toItems(self.storage), Slot(slotIdx as nat), self.contents); // observe
        return;
      }

      // -- increment --
      slotIdx := Uint64SlotSuccessorUint64(lseq_length_as_uint64(self.storage), slotIdx);
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

  method FixedSizeInsert<V>(linear inout self: FixedSizeLinearHashMap, key: uint64, linear value: V)
  returns (linear replaced: lOption<V>)
  requires FixedSizeInv(old_self)
  requires old_self.count as nat < |old_self.storage| - 1
  ensures FixedSizeInv(self)
  ensures self.contents == old_self.contents[key := Some(value)]
  ensures key !in old_self.contents ==> replaced.lNone?
  ensures key in old_self.contents ==> replaced.Option() == old_self.contents[key]
  ensures replaced.lSome? ==> key in old_self.contents
  ensures |self.storage| == |old_self.storage|
  {
    linear var entry := lItem.Entry(key, value);
    replaced := FixedSizeInsertEntry(inout self, entry);
  }

  method FixedSizeInsertEntry<V>(linear inout self: FixedSizeLinearHashMap, linear entry: lItem<V>)
  returns (linear replaced: lOption<V>)
  requires entry.Entry?
  requires FixedSizeInv(old_self)
  requires old_self.count as nat < |old_self.storage| - 1
  ensures FixedSizeInv(self)
  ensures self.contents == old_self.contents[entry.key := Some(entry.value)]
  ensures entry.key !in old_self.contents ==> replaced.lNone?
  ensures entry.key in old_self.contents ==> replaced.Option() == old_self.contents[entry.key]
  ensures replaced.lSome? ==> entry.key in old_self.contents
  ensures |self.storage| == |old_self.storage|
  {
    var slotIdx;
    ghost var probeStartSlotIdx, probeSkips;
    slotIdx, probeStartSlotIdx, probeSkips := Probe(self, entry.key);

    ghost var contents := old_self.contents[entry.key := Some(entry.value)];
    inout ghost self.contents := contents;
    
    linear var olditem := lseq_take_inout(inout self.storage, slotIdx);
    lseq_give_inout(inout self.storage, slotIdx, entry);

    if olditem.Empty? {
      olditem.FreeNonEntry();
      inout self.count := self.count + 1;
      replaced := lNone;
   } else if olditem.Tombstone? {
      olditem.FreeNonEntry();
      replaced := lNone;
    } else {
      linear var Entry(_, value) := olditem;
      replaced := lSome(value);
    }

    forall explainedKey | explainedKey in self.contents
    ensures exists skips :: SlotExplainsKey(toItems(self.storage), skips, explainedKey)
    {
      if entry.key == explainedKey {
        assert SlotExplainsKey(toItems(self.storage), probeSkips as nat, entry.key); // observe
      } else {
        var oldSkips :| SlotExplainsKey(toItems(old_self.storage), oldSkips, explainedKey);
        assert SlotExplainsKey(toItems(self.storage), oldSkips, explainedKey); // observe
      }
    }
  
    forall slot | ValidSlot(|self.storage|, slot) && toItems(self.storage)[slot.slot].Entry?
    ensures && var item := toItems(self.storage)[slot.slot];
            && self.contents[item.key] == Some(item.value)
    {
      var item := toItems(self.storage)[slot.slot];
      if slot != Slot(slotIdx as nat) {
        if item.key == entry.key {
          assert TwoNonEmptyValidSlotsWithSameKey(toItems(self.storage), slot, Slot(slotIdx as nat)); // observe
          assert SameSlot(|self.storage|, slot, Slot(slotIdx as nat)); // observe
          assert false;
        }
      }
    }

    forall slot | ValidSlot(|self.storage|, slot) && toItems(self.storage)[slot.slot].Tombstone?
    ensures && var item := self.storage[slot.slot];
            && self.contents[item.key].None?
    {
      var item := self.storage[slot.slot];
      if slot != Slot(slotIdx as nat) {
        if item.key == entry.key {
          assert TwoNonEmptyValidSlotsWithSameKey(toItems(self.storage), slot, Slot(slotIdx as nat)); // observe
          assert SameSlot(|self.storage|, slot, Slot(slotIdx as nat)); // observe
          assert false;
        }
      }
    }
  }

  method FixedSizeUpdateBySlot<V>(linear inout self: FixedSizeLinearHashMap<V>, slotIdx: uint64, linear value: V)
  returns (linear replaced: V)
  requires FixedSizeInv(old_self)
  requires 0 <= slotIdx as int < |old_self.storage|
  requires old_self.storage[slotIdx as nat].Entry?
  ensures FixedSizeInv(self)
  {
    linear var entry: lItem<V> := lseq_take_inout(inout self.storage, slotIdx);
    linear var Entry(key, oldvalue) := entry;
    lseq_give_inout(inout self.storage, slotIdx, lItem.Entry(key, value));
    replaced := oldvalue;

    inout ghost self.contents := self.contents[key := Some(value)];
    assert EntryInSlotMatchesContents(toItems(old_self.storage), Slot(slotIdx as int), old_self.contents);

    forall explainedKey | explainedKey in self.contents
    ensures exists skips :: SlotExplainsKey(toItems(self.storage), skips, explainedKey)
    {
      var oldSkips :| SlotExplainsKey(toItems(old_self.storage), oldSkips, explainedKey);
      assert SlotExplainsKey(toItems(self.storage), oldSkips, explainedKey); // observe
    }
  
    forall slot | ValidSlot(|self.storage|, slot)
        && SlotIsEntry(toItems(self.storage), slot)
    ensures EntryInSlotMatchesContents(toItems(self.storage), slot, self.contents)
    {
      assert EntryInSlotMatchesContents(toItems(old_self.storage), slot, old_self.contents);
      if old_self.storage[slot.slot].key == key {
        assert TwoNonEmptyValidSlotsWithSameKey(toItems(old_self.storage), slot, Slot(slotIdx as int));
      }
    }

    forall slot | ValidSlot(|self.storage|, slot)
        && toItems(self.storage)[slot.slot].Tombstone?
    ensures TombstoneInSlotMatchesContents(toItems(self.storage), slot, self.contents)
    {
      if slot.slot != slotIdx as nat && old_self.storage[slot.slot].key == key {
        assert TwoNonEmptyValidSlotsWithSameKey(toItems(self.storage), slot, Slot(slotIdx as nat)); // observe
        assert SameSlot(|self.storage|, slot, Slot(slotIdx as nat)); // observe
        assert false;
      }
    }
  }

  method IsEntry<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64) returns (b: bool)
  requires FixedSizeInv(self)
  ensures b == (key in self.contents && self.contents[key].Some?)
  {
    var slotIdx, _, _ := Probe(self, key);
    b := lseq_peek(self.storage, slotIdx).Entry?;
    assert b == (key in self.contents && self.contents[key].Some?);
  }

  method FixedSizeGet<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64)
  returns (shared found: V)
  requires FixedSizeInv(self)
  requires key in self.contents && self.contents[key].Some?
  ensures found == self.contents[key].value
  {
    var slotIdx, _, _ := Probe(self, key);
    found := lseq_peek(self.storage, slotIdx).value;
    // TODO(Jialin): update to return shared lOption<V>
  }

  method FixedSizeRemove<V>(linear inout self: FixedSizeLinearHashMap<V>, key: uint64)
  returns (linear removed: lOption<V>)
  requires FixedSizeInv(old_self)
  ensures FixedSizeInv(self)
  ensures (self.contents == if key in old_self.contents
    then old_self.contents[key := None]
    else old_self.contents)
  ensures (removed == if key in old_self.contents && old_self.contents[key].Some?
    then lSome(old_self.contents[key].value)
    else lNone)
  ensures (removed.lSome? <==> (key in old_self.contents && old_self.contents[key].Some?))
  ensures (self.count == old_self.count)
  {
    var slotIdx;
    ghost var probeStartSlotIdx, probeSkips;
    slotIdx, probeStartSlotIdx, probeSkips := Probe(self, key);

    if lseq_peek(self.storage, slotIdx).Entry? {
      linear var item: lItem<V> := lseq_take_inout(inout self.storage, slotIdx);
      lseq_give_inout(inout self.storage, slotIdx, lItem.Tombstone(key));
      linear var Entry(_, value) := item;
      removed := lSome(value);

      inout ghost self.contents := self.contents[key := None];
      assert EntryInSlotMatchesContents(toItems(old_self.storage), Slot(slotIdx as int), old_self.contents);

      forall explainedKey | explainedKey in self.contents
      ensures exists skips :: SlotExplainsKey(toItems(self.storage), skips, explainedKey)
      {
        if key == explainedKey {
          assert SlotExplainsKey(toItems(self.storage), probeSkips as nat, key);
        } else {
          var oldSkips :| SlotExplainsKey(toItems(old_self.storage), oldSkips, explainedKey);
          assert SlotExplainsKey(toItems(self.storage), oldSkips, explainedKey);
        }
      }

      forall slot | ValidSlot(|self.storage|, slot) && toItems(self.storage)[slot.slot].Entry?
      ensures && var item := self.storage[slot.slot];
              && self.contents[item.key] == Some(item.value)
      {
        var item := self.storage[slot.slot];
        if slot != Slot(slotIdx as nat) && item.key == key {
          assert CantEquivocateStorageKey(toItems(self.storage));
          assert TwoNonEmptyValidSlotsWithSameKey(toItems(self.storage), slot, Slot(slotIdx as nat));
          assert false;
        }
      }
    } else {
      removed := lNone;
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

  lemma CantEquivocateMapFromStorageKey<V>(underlying: FixedSizeLinearHashMap<V>)
  requires FixedSizeInv(underlying)
  ensures CantEquivocate(toItems(underlying.storage))
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
      assert CantEquivocateStorageKey(toItems(underlying.storage));
      if underlying.storage[slot1.slot].Entry? && underlying.storage[slot2.slot].Entry? &&
        underlying.storage[slot1.slot].key == underlying.storage[slot2.slot].key {

        assert TwoNonEmptyValidSlotsWithSameKey(toItems(underlying.storage), slot1, slot2);
        if slot1 != slot2 {
          assert false;
        }
        assert slot1 == slot2;
      } else {
        assert slot1 == slot2;
      }
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
    && MapFromStorage(toItems(underlying.storage)) == self.contents
  }

  lemma UnderlyingInvImpliesMapFromStorageMatchesContents<V>(underlying: FixedSizeLinearHashMap<V>, contents: map<uint64, V>)
  requires UnderlyingContentsMatchesContents(underlying, contents)
  requires FixedSizeInv(underlying)
  ensures MapFromStorage(toItems(underlying.storage)) == contents
  {
    var mapFromStorage := MapFromStorage(toItems(underlying.storage));
    CantEquivocateMapFromStorageKey(underlying);
    MapFromStorageProperties(toItems(underlying.storage), mapFromStorage);
    assert MapFromStorage(toItems(underlying.storage)) == contents;
  }

  /* protected */
  predicate Inv<V>(self: LinearHashMap<V>)
  ensures Inv(self) ==> |self.contents| == self.count as nat
  ensures Inv(self) ==> UnderlyingInv(self, self.underlying)
  {
    && UnderlyingInv(self, self.underlying)
    && MapFromStorage(toItems(self.underlying.storage)) == self.contents
    && |self.contents| == self.count as nat
    && (self.count as nat) <= 0x1_0000_0000_0000_0000 / 8
  }

  predicate Inv0<V>(self: LinearHashMap<V>) { Inv(self) }

  lemma CountBound<V>(self: LinearHashMap<V>)
  requires Inv(self)
  ensures self.count as int <= 0x1_0000_0000_0000_0000 / 8
  {
  }

  lemma RevealProtectedInv<V>(self: LinearHashMap<V>)
    requires Inv(self)
    ensures (
      && UnderlyingInv(self, self.underlying)
      && MapFromStorage(toItems(self.underlying.storage)) == self.contents
      && |self.contents| == self.count as nat)
  {
  }

  predicate IsConstructor<V>(self: LinearHashMap<V>, size: uint64)
  requires 128 <= size
  {
    && Inv(self)
    && self.contents == map[]
  }

  method Constructor<V>(size: uint64) returns (linear self: LinearHashMap<V>)
  requires 128 <= size
  ensures IsConstructor(self, size)
  {
    linear var fixed := ConstructorFromSize(size);
    self := LinearHashMap(fixed, 0, map[]);

    assert forall slot :: ValidSlot(|self.underlying.storage|, slot) ==> !self.underlying.storage[slot.slot].Entry?;
    UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents);
    assert MapFromStorage(toItems(self.underlying.storage)) == self.contents;
  }

  lemma LemmaEntryKeyInContents<V>(self: LinearHashMap<V>, i: uint64)
  requires Inv(self)
  requires 0 <= i as int < |self.underlying.storage|
  requires self.underlying.storage[i as nat].Entry?
  ensures self.underlying.storage[i as nat].key in self.contents
  {
    assert EntryInSlotMatchesContents(toItems(self.underlying.storage), Slot(i as nat), self.underlying.contents); // trigger
  }

  predicate IsRealloc<V>(self: LinearHashMap<V>, self': LinearHashMap<V>)
  requires Inv(self)
  requires self.count as nat < 0x1_0000_0000_0000_0000 / 8
  {
    && self'.contents == self.contents
    && self'.underlying.count as nat < |self'.underlying.storage| - 2
    && Inv(self')
  }

  method Realloc<V>(linear inout self: LinearHashMap<V>)
  requires Inv(old_self)
  requires old_self.count as nat < 0x1_0000_0000_0000_0000 / 8
  ensures IsRealloc(old_self, self)
  {
    var newSize: uint64 := (128 + self.count) * 4;
    linear var newUnderlying := ConstructorFromSize(newSize);

    ghost var transferredContents := map[];
    ghost var transfers := toItems(self.underlying.storage);
    CantEquivocateMapFromStorageKey(self.underlying);

    var i := 0 as uint64;
    var size := lseq_length_as_uint64(self.underlying.storage);

    while i < size
      invariant i <= size
      invariant size as nat == |self.underlying.storage|
      invariant self.count as nat == |self.contents|
      invariant |newUnderlying.storage| == newSize as nat

      invariant transferredContents.Keys <= self.contents.Keys
      invariant newUnderlying.count as nat == |transferredContents|
      invariant newUnderlying.count as nat < |newUnderlying.storage| - 2
      invariant (forall key :: key in newUnderlying.contents ==> 
        EntryExistsInElements(transfers, i, key))

      invariant FixedSizeInv(newUnderlying)
      invariant UnderlyingContentsMatchesContents(newUnderlying, transferredContents)
      invariant toItems(self.underlying.storage)[i..] == transfers[i..]
      invariant MapFromStorage(transfers[..i]) == transferredContents
      invariant MapFromStorage(transfers) == self.contents

      invariant (forall j | i as nat <= j < size as nat :: lseq_has(self.underlying.storage)[j])
      invariant (forall j | 0 <= j < i as nat :: !lseq_has(self.underlying.storage)[j])
    {
      assert i < size;
      assert Last(transfers[..i+1]) == transfers[i];
      assert transfers[..i] == DropLast(transfers[..i+1]);

      linear var item := lseq_take_inout(inout self.underlying.storage, i);
      if item.Entry? {
        ElementsEntryInMap(transfers, item.toItem());
        if item.key in newUnderlying.contents {
          var j:uint64 :| (
              && 0 <= j < i
              && ValidSlot(|transfers|, Slot(j as int))
              && transfers[Slot(j as int).slot].Entry?
              && transfers[Slot(j as int).slot].key == item.key);
          assert ValidSlot(|transfers|, Slot(i as nat));
          assert false;
        }
        assert item.key !in newUnderlying.contents;

        assert transferredContents.Keys <= self.contents.Keys;
        SetInclusionImpliesSmallerCardinality(transferredContents.Keys, self.contents.Keys);
        assert |transferredContents.Keys| <= |self.contents.Keys|;
        assert |transferredContents| <= |self.contents|;
        assert newUnderlying.count as nat < |newUnderlying.storage| - 1;

        // ------ Mutation ------
        transferredContents := transferredContents[item.key := item.value];
        linear var replaced := FixedSizeInsertEntry(inout newUnderlying, item);
        // ----------------------
        linear match replaced { case lNone() => }
        assert ValidSlot(|transfers|, Slot(i as nat));
        assert FixedSizeInv(newUnderlying);
      } else {
        item.FreeNonEntry();
      }
      assert newUnderlying.count as nat < |newUnderlying.storage| - 2;
      i := i + 1;
    }

    assert transfers[..i] == transfers;
    assert UnderlyingContentsMatchesContents(newUnderlying, transferredContents);
    assert UnderlyingContentsMatchesContents(newUnderlying, self.contents);
    UnderlyingInvImpliesMapFromStorageMatchesContents(newUnderlying, self.contents);

    linear var oldUnderlying := Replace(inout self.underlying, newUnderlying);
    linear var FixedSizeLinearHashMap(oldstorage, _, _) := oldUnderlying;
    lseq_free(oldstorage);
  }

  method Insert<V>(linear inout self: LinearHashMap, key: uint64, linear value: V) 
  returns (linear replaced: lOption<V>)
  requires Inv(old_self)
  requires old_self.count as nat < 0x1_0000_0000_0000_0000 / 8
  ensures
    && Inv(self)
    && self.contents == old_self.contents[key := value]
    && self.count as nat == old_self.count as nat + (if replaced.lSome? then 0 else 1)
    && (replaced.lSome? ==> MapsTo(old_self.contents, key, replaced.value))
    && (replaced.lNone? ==> key !in old_self.contents)
  {
    var len := lseq_length_as_uint64(self.underlying.storage);
    if len / 2 <= self.underlying.count {
      Realloc(inout self);
    }
    // --------------

    // -- mutation --
    replaced := FixedSizeInsert(inout self.underlying, key, value);
    inout ghost self.contents := self.contents[key := value];
    if replaced.lNone? {
      inout self.count := self.count + 1;
    }
    // --------------

    UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents);
  }

  method Remove<V>(linear inout self: LinearHashMap, key: uint64) 
  returns (linear removed: lOption<V>)
  requires Inv(old_self)
  ensures Inv(self)
  ensures removed.lSome? ==>
      key in old_self.contents && old_self.contents[key] == removed.value
  ensures removed.lNone? ==> key !in old_self.contents
  ensures (self.contents == if key in old_self.contents
      then map k | k in old_self.contents && k != key :: old_self.contents[k]
      else old_self.contents)
  {
    // -- mutation --
    removed := FixedSizeRemove(inout self.underlying, key);
    inout ghost self.contents := map k | k in self.contents && k != key :: self.contents[k];
    if removed.lSome? {
      inout self.count := self.count - 1;
    }
    // -------------- 

    UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents); 
    assert self.count as nat == |self.contents| by {
      if removed.lSome? {
        assert key in old_self.contents;
        assert self.contents.Keys <= old_self.contents.Keys;
        assert |old_self.contents| == self.count as nat + 1;
        assert |old_self.contents.Keys| == self.count as nat + 1;
        assert |old_self.contents.Keys - {key}| == |old_self.contents.Keys| - |{key}|;
        assert old_self.contents.Keys - {key} == self.contents.Keys;
        assert |self.contents| == |old_self.contents| - 1;
        assert |self.contents| == self.count as nat;
      } else {
        assert key !in old_self.contents;
        assert self.contents == old_self.contents;
        assert |self.contents| == self.count as nat;
      }
    }
  }

  method Get<V>(shared self: LinearHashMap, key: uint64) returns (shared result: V)
  requires Inv(self)
  requires key in self.underlying.contents && self.underlying.contents[key].Some?
  ensures key in self.contents && result == self.contents[key]
  {
    result := FixedSizeGet(self.underlying, key);
  }
}
