include "NativeTypes.dfy"
include "Option.dfy"
include "sequences.dfy"
include "SetBijectivity.dfy"

module MutableMap {
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened SetBijectivity

  datatype Slot = Slot(slot: nat)

  datatype Item<V(==)> = Empty | Filled(key: uint64, value: V)

  class FixedSizeHashMap<V(==)> {
    var Storage: array<Item<V>>;
    var Count: uint64;

    ghost var Contents: map<uint64, V>;

    predicate ValidElements(elements: seq<Item<V>>)
    {
      && 0 < |elements| < 0x10000000000000000
    }

    function SlotForKey(elementsLength: nat, key: uint64): (result: Slot)
      requires 0 < elementsLength
      ensures ValidSlot(elementsLength, result)
    {
      Slot((key as nat) % elementsLength)
    }

    function method Uint64SlotForKey(key: uint64): (result: uint64)
      requires 0 < Storage.Length < 0x10000000000000000
      ensures ValidSlot(Storage.Length, Slot(result as nat))
      ensures Slot(result as nat) == SlotForKey(Storage.Length, key)
      reads this, this.Storage
    {
      key % (Storage.Length as uint64)
    }

    predicate ValidSlot(elementsLength: nat, slot: Slot)
    {
      slot.slot < elementsLength
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

    predicate FilledWithOtherKey(elements: seq<Item<V>>, slot: Slot, excludingKey: uint64)
      requires ValidElements(elements)
      requires ValidSlot(|elements|, slot)
    {
      elements[slot.slot].Filled? && elements[slot.slot].key != excludingKey
    }

    predicate FilledWithOtherKeys(elements: seq<Item<V>>, start: Slot, count: nat, excludingKey: uint64)
      requires ValidElements(elements)
      requires ValidSlot(|elements|, start)
    {
      && (forall offset: nat :: offset < count ==>
        FilledWithOtherKey(elements, KthSlotSuccessor(|elements|, start, offset), excludingKey))
    }

    predicate FilledWithKey(elements: seq<Item<V>>, slot: Slot, key: uint64)
      requires ValidElements(elements)
      requires ValidSlot(|elements|, slot)
    {
      elements[slot.slot].Filled? && elements[slot.slot].key == key
    }

    predicate SlotExplainsKey(elements: seq<Item<V>>, skips: nat, key: uint64)
      requires ValidElements(elements)
    {
      var foundSlot := KthSlotSuccessor(|elements|, SlotForKey(|elements|, key), skips);
      && ValidSlot(|elements|, foundSlot)
      && FilledWithOtherKeys(elements, SlotForKey(|elements|, key), skips, key)
      && FilledWithKey(elements, foundSlot, key)
    }

    predicate SeqMatchesContents(elements: seq<Item<V>>, contents: map<uint64, V>)
      requires ValidElements(elements)
    {
      && (forall key :: key in contents ==> exists skips :: SlotExplainsKey(elements, skips, key))
      && (forall slot :: ValidSlot(|elements|, slot) && elements[slot.slot].Filled? ==>
        && var key := elements[slot.slot].key;
        && key in contents)
      && (forall slot1, slot2 :: (
        && ValidSlot(|elements|, slot1)
        && ValidSlot(|elements|, slot2)
        && elements[slot1.slot].Filled?
        && elements[slot2.slot].Filled?
        && elements[slot1.slot].key == elements[slot2.slot].key
      ) ==> slot1 == slot2)
    }

    predicate Inv()
      reads this, this.Storage
      {
      && 0 < Storage.Length < 0x10000000000000000
      && (Count as nat) < 0x10000000000000000
      && Count as nat <= Storage.Length 

      && |Contents| == (Count as nat)
      && SeqMatchesContents(Storage[..], Contents)
    }

    function IndexSetThrough(elements: seq<Item<V>>, through: nat): set<int>
      requires through <= |elements|
    {
      set i | 0 <= i < through && elements[i].Filled?
    }

    function IndexSet(elements: seq<Item<V>>): set<int>
    {
      IndexSetThrough(elements, |elements|)
    }

    function Count1(item: Item<V>): nat
    {
      if item.Filled? then 1 else 0
    }

    function CountFilled(view: seq<Item<V>>): (result: nat)
    {
      if |view| == 0 then
        0
      else
        CountFilled(view[1..]) + Count1(view[0])
    }

    lemma CountFilledMatchesIndexSet(elements: seq<Item<V>>)
      ensures CountFilled(elements) == |IndexSet(elements)|
    {
      var i: nat := 0;
      while i < |elements|
        invariant i <= |elements|
        invariant |IndexSetThrough(elements, i)| == CountFilled(elements[..i])
      {
        var j := i + 1;
        CountFilledAdditive(elements[..i], [elements[i]]);
        assert elements[..i] + [elements[i]] == elements[..j];
        if elements[i].Filled? {
          assert IndexSetThrough(elements, j) == IndexSetThrough(elements, i) + {i};
        } else {
          assert IndexSetThrough(elements, j) == IndexSetThrough(elements, i);
        }
        i := j;
      }
      assert elements[..i] == elements;
    }

    lemma IndexSetMatchesContents(elements: seq<Item<V>>, contents: map<uint64, V>)
      requires ValidElements(elements)
      requires SeqMatchesContents(elements, contents)
      ensures |IndexSet(elements)| == |contents.Keys|
    {
      var relation := set i | i in IndexSet(elements) :: (i, elements[i].key);
      var setA := IndexSet(elements);
      var setB := contents.Keys;
      forall a | a in setA
      ensures exists b :: b in setB && (a, b) in relation
      {
        var slot := Slot(a);
        assert ValidSlot(|elements|, slot);
      }
      forall a1, a2, b | a1 in setA && a2 in setA && b in setB && (a1, b) in relation && (a2, b) in relation
      ensures a1 == a2
      {
        assert ValidSlot(|elements|, Slot(a1));
        assert ValidSlot(|elements|, Slot(a2));
      }
      BijectivityImpliesEqualCardinality(IndexSet(elements), contents.Keys, relation);
    }

    lemma CountFilledMatchesContents(elements: seq<Item<V>>, contents: map<uint64, V>)
      requires ValidElements(elements)
      requires SeqMatchesContents(elements, contents)
      ensures CountFilled(elements) == |contents|
    {
      CountFilledMatchesIndexSet(elements);
      IndexSetMatchesContents(elements, contents);
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

    function View(elements: seq<Item<V>>, start: nat): (result: seq<Item<V>>)
      requires start < |elements|
      ensures |result| == |elements|
    {
      elements[start..] + elements[..start]
    }

    lemma CountFilledAdditive(a: seq<Item<V>>, b: seq<Item<V>>)
      ensures CountFilled(a + b) == CountFilled(a) + CountFilled(b)
    {
      if |a| == 0 {
        assert a + b == b;
      } else {
        assert (a + b)[1..] == a[1..] + b;
      }
    }

    lemma ViewsHasConsistentCounts(a: seq<Item<V>>, b: seq<Item<V>>, delta: nat)
      requires delta < |a|
      requires b == View(a, delta)
      ensures CountFilled(a) == CountFilled(b)
    {
      var n := |a|;
      assert a == a[..delta] + a[delta..];
      CountFilledAdditive(a[..delta], a[delta..]);
      CountFilledAdditive(b[..n-delta], b[n-delta..]);
      assert b == b[..n-delta] + b[n-delta..];
    }

    method Probe(key: uint64) returns (skips: uint64)
      requires Inv()
      requires Count as nat < Storage.Length
      ensures ValidSlot(Storage.Length, KthSlotSuccessor(Storage.Length, SlotForKey(Storage.Length, key), skips as nat))
      ensures key in Contents ==> SlotExplainsKey(Storage[..], skips as nat, key)
      ensures key !in Contents ==> Storage[KthSlotSuccessor(Storage.Length, SlotForKey(Storage.Length, key), skips as nat).slot].Empty?
      // ensures FilledWithOtherKeys(Storage[..], SlotForKey(Storage.Length, key), , key)
    {
      var startSlotIdx := Uint64SlotForKey(key);
      skips := 0;
      ghost var viewFromStartSlot := View(Storage[..], startSlotIdx as nat);
      //while i < (Storage.Length as uint64) - 1
      //  invariant ValidSlot(Storage.Length as uint64, slot)
      //  invariant FilledWithOtherKeys(Storage[..], startSlot, slot, key)
      //  invariant FilledSlots(Storage[..], startSlot, slot)
      //  invariant Storage.Length == old(Storage.Length)
      //  invariant i <= (Storage.Length as uint64) - 1
      //  invariant NextSlotK(startSlot, i as int) == slot;
    }
    //   {
    //     if Storage[slot.slot].Empty? {
    //       if key in Contents { // contradiction
    //         ghost var keySlot :| SlotExplainsKey(Storage[..], keySlot, key);
    //         if SlotBetween(Storage.Length as uint64, startSlot, slot, keySlot) {
    //           assert FilledWithOtherKey(Storage[..], slot, key);
    //           assert false;
    //         } else {
    //           assert FilledWithOtherKey(Storage[..], keySlot, key);
    //           assert false;
    //         }
    //       }
    //       return slot;
    //     } else if Storage[slot.slot].key == key {
    //       return slot;
    //     }
    //     slot := SlotSuccessor(slot);
    //     i := i + 1;
    //   }
    // }
  }
}
