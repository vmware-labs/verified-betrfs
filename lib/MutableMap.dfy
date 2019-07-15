include "NativeTypes.dfy"
include "Option.dfy"
include "sequences.dfy"

module MutableMap {
  import opened NativeTypes
  import opened Options
  import opened Sequences

  datatype Slot = Slot(slot: uint64)

  datatype Item<V(==)> = Empty | Filled(key: uint64, value: V)

  class FixedSizeHashMap<V(==)> {
    var Storage: array<Item<V>>;
    var Count: uint64;

    ghost var Contents: map<uint64, V>;

    predicate LengthInv()
      reads this, this.Storage
    {
      && 0 < Storage.Length < 0x10000000000000000
    }

    predicate ValidElements(elements: seq<Item<V>>)
    {
      && 0 < |elements| < 0x10000000000000000
    }

    function method {:opaque} SlotForKey(elementsLength: uint64, key: uint64): (result: Slot)
      requires 0 < elementsLength
      ensures ValidSlot(elementsLength, result)
    {
      Slot(key % elementsLength)
    }

    predicate ValidSlot(elementsLength: uint64, slot: Slot)
    {
      0 <= slot.slot < elementsLength
    }

    predicate FilledWithOtherKey(elements: seq<Item<V>>, slot: Slot, excludingKey: uint64)
      requires ValidElements(elements)
      requires ValidSlot(|elements| as uint64, slot)
    {
      elements[slot.slot].Filled? && elements[slot.slot].key != excludingKey
    }

    predicate FilledWithKey(elements: seq<Item<V>>, slot: Slot, key: uint64)
      requires ValidElements(elements)
      requires ValidSlot(|elements| as uint64, slot)
    {
      elements[slot.slot].Filled? && elements[slot.slot].key == key
    }

    predicate SlotBetween(elementsLength: uint64, startInclusive: Slot, slot: Slot, endExclusive: Slot)
      requires ValidSlot(elementsLength, startInclusive)
      requires ValidSlot(elementsLength, slot)
      requires ValidSlot(elementsLength, endExclusive)
    {
      if startInclusive.slot <= endExclusive.slot then
        startInclusive.slot <= slot.slot < endExclusive.slot
      else
        slot.slot < endExclusive.slot || startInclusive.slot <= slot.slot
    }

    predicate FilledWithOtherKeys(elements: seq<Item<V>>, startInclusive: Slot, endExclusive: Slot, excludingKey: uint64)
      requires ValidElements(elements)
      requires ValidSlot(|elements| as uint64, startInclusive)
      requires ValidSlot(|elements| as uint64, endExclusive)
    {
      && (forall slot :: ValidSlot(|elements| as uint64, slot) && SlotBetween(|elements| as uint64, startInclusive, slot, endExclusive) ==>
        FilledWithOtherKey(elements, slot, excludingKey))
    }

    predicate FilledSlots(elements: seq<Item<V>>, startInclusive: Slot, endExclusive: Slot)
      requires ValidElements(elements)
      requires ValidSlot(|elements| as uint64, startInclusive)
      requires ValidSlot(|elements| as uint64, endExclusive)
    {
      && (forall slot :: ValidSlot(|elements| as uint64, slot) && SlotBetween(|elements| as uint64, startInclusive, slot, endExclusive) ==> elements[slot.slot].Filled?)
    }

    predicate SlotExplainsKey(elements: seq<Item<V>>, slot: Slot, key: uint64)
      requires ValidElements(elements)
    {
      && ValidSlot(|elements| as uint64, slot)
      && FilledWithOtherKeys(elements, SlotForKey(|elements| as uint64, key), slot, key)
      && FilledWithKey(elements, slot, key)
    }

    predicate SeqMatchesContents(elements: seq<Item<V>>, contents: map<uint64, V>)
      requires ValidElements(elements)
    {
      && (forall key :: key in contents ==> exists slot :: SlotExplainsKey(elements, slot, key))
      && (forall slot :: ValidSlot(|elements| as uint64, slot) && elements[slot.slot].Filled? ==>
        elements[slot.slot].key in contents)
    }
    
    predicate Inv()
      reads this, this.Storage
    {
      && 0 < Storage.Length < 0x10000000000000000
      && 0 <= (Count as int) < 0x10000000000000000
      && Count as int <= Storage.Length 

      && |Contents| == (Count as int)
      && SeqMatchesContents(Storage[..], Contents)
    }
    
    constructor (size: uint64)
      requires 0 < size
      ensures Inv()
      ensures Contents == map[]
    {
      Count := 0;
      Storage := new [size] (_ => Empty);
      Contents := map[];
    }

    function method NextSlot(slot: Slot): (nextSlot: Slot)
      requires Inv()
      requires ValidSlot(Storage.Length as uint64, slot)
      ensures ValidSlot(Storage.Length as uint64, nextSlot)
      reads this, this.Storage
    {
      Slot(if slot.slot == (Storage.Length as uint64) - 1 then
        0
      else
        slot.slot + 1)
    }

    function NextSlotK(slot: Slot, k: int): (nextSlot: Slot)
      requires k >= 0
      requires Inv()
      requires ValidSlot(Storage.Length as uint64, slot)
      ensures ValidSlot(Storage.Length as uint64, nextSlot)
      reads this, this.Storage
    {
      if k == 0 then
        slot
      else
        NextSlot(NextSlotK(slot, k - 1))
    }
    
    lemma LastSlotMustBeEmptyWhenNotFull(slot: Slot) returns (emptySlot: Slot)
      requires Inv()
      requires ValidSlot(Storage.Length as uint64, slot)
      requires FilledSlots(Storage[..], slot, NextSlotK(slot, Storage.Length - 1))
      ensures emptySlot == NextSlotK(slot, Storage.Length - 1)
      ensures ValidSlot(Storage.Length as uint64, emptySlot)
      ensures (Count as int) < Storage.Length ==> Storage[emptySlot.slot].Empty?
    {
      emptySlot := NextSlotK(slot, Storage.Length - 1);
      if (Count as int) < Storage.Length {
        assert |Contents| < Storage.Length;
        assert SeqMatchesContents(Storage[..], Contents);
        if Storage[emptySlot.slot].Filled? {
          assert false;
        }
        assert Storage[emptySlot.slot].Empty?;
      } else {
      }
    }

    method Probe(key: uint64) returns (slot: Slot)
      requires Inv()
      requires Count as int < Storage.Length
      ensures ValidSlot(Storage.Length as uint64, slot)
      ensures key in Contents ==> FilledWithKey(Storage[..], slot, key)
      ensures key !in Contents ==> Storage[slot.slot].Empty?
      ensures FilledWithOtherKeys(Storage[..], SlotForKey(Storage.Length as uint64, key), slot, key)
    {
      slot := SlotForKey(Storage.Length as uint64, key);
      var startSlot := slot;
      var i := 0;
      while i < (Storage.Length as uint64) - 1
        invariant ValidSlot(Storage.Length as uint64, slot)
        invariant FilledWithOtherKeys(Storage[..], startSlot, slot, key)
        invariant FilledSlots(Storage[..], startSlot, slot)
        invariant Storage.Length == old(Storage.Length)
        invariant i <= (Storage.Length as uint64) - 1
        invariant NextSlotK(startSlot, i as int) == slot;
      {
        if Storage[slot.slot].Empty? {
          if key in Contents { // contradiction
            ghost var keySlot :| SlotExplainsKey(Storage[..], keySlot, key);
            if SlotBetween(Storage.Length as uint64, startSlot, slot, keySlot) {
              assert FilledWithOtherKey(Storage[..], slot, key);
              assert false;
            } else {
              assert FilledWithOtherKey(Storage[..], keySlot, key);
              assert false;
            }
          }
          return slot;
        } else if Storage[slot.slot].key == key {
          return slot;
        }
        slot := NextSlot(slot);
        i := i + 1;
      }
      assert i == (Storage.Length as uint64) - 1;
      assert Count as int < Storage.Length;
      assert NextSlotK(startSlot, i as int) == slot;
      ghost var lastSlot := LastSlotMustBeEmptyWhenNotFull(startSlot);
      assert lastSlot == slot;
      assert Storage[slot.slot].Empty?;
      if key in Contents { // contradiction
        ghost var keySlot :| SlotExplainsKey(Storage[..], keySlot, key);
        if SlotBetween(Storage.Length as uint64, startSlot, slot, keySlot) {
          assert FilledWithOtherKey(Storage[..], slot, key);
          assert false;
        } else {
          assert FilledWithOtherKey(Storage[..], keySlot, key);
          assert false;
        }
      }
      assert key !in Contents;
    }
  }
}
