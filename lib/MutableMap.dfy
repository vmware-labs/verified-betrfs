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

  // FIXME(utaal) reduce proofs!
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

    lemma KthSlotSuccessorWrapsAround(elementsLength: nat, slot: Slot, k: nat)
      requires 0 <= k < elementsLength
      requires ValidSlot(elementsLength, slot)
      ensures if k < (elementsLength-slot.slot) then
            KthSlotSuccessor(elementsLength, slot, k).slot == slot.slot + k
          else
            KthSlotSuccessor(elementsLength, slot, k).slot == k - (elementsLength - slot.slot)
      decreases k
    {
      var elementsInRightSlice := elementsLength - slot.slot;
      if k < elementsInRightSlice {
        assert KthSlotSuccessor(elementsLength, slot, k).slot == slot.slot + k;
      } else { // k >= elementsInRightSlice
        assert KthSlotSuccessor(elementsLength, slot, elementsInRightSlice).slot == 0;
        var firstSlot := KthSlotSuccessor(elementsLength, slot, elementsInRightSlice);
        assert firstSlot.slot == 0;
        var idx: nat := k - elementsInRightSlice;
        assert k == elementsInRightSlice + idx;
        KthSlotSuccessorWrapsAround(elementsLength, firstSlot, idx);
        assert KthSlotSuccessor(elementsLength, firstSlot, idx).slot == idx;
        assert KthSlotSuccessor(elementsLength, slot, elementsInRightSlice + idx).slot == idx;
      }
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
      && Count as nat < Storage.Length 

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

    lemma ViewsHaveConsistentCounts(a: seq<Item<V>>, b: seq<Item<V>>, delta: nat)
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

    function method Uint64SlotSuccessor(slot: uint64): (nextSlot: uint64)
      requires Inv()
      requires ValidSlot(Storage.Length, Slot(slot as nat))
      ensures ValidSlot(Storage.Length, Slot(nextSlot as nat))
      ensures Slot(nextSlot as nat) == SlotSuccessor(Storage.Length, Slot(slot as nat))
      reads this, this.Storage
    {
      if slot == (Storage.Length as uint64) - 1 then
        0
      else
        slot + 1
    }

    method Probe(key: uint64) returns (slotIdx: uint64, ghost startSlotIdx: uint64, ghost ghostSkips: uint64)
      requires Inv()
      ensures Inv()
      ensures ValidSlot(Storage.Length, Slot(slotIdx as nat))
      ensures ValidSlot(Storage.Length, Slot(startSlotIdx as nat))
      ensures Slot(startSlotIdx as nat) == SlotForKey(Storage.Length, key)
      ensures 0 <= ghostSkips
      ensures slotIdx as nat == KthSlotSuccessor(Storage.Length, Slot(startSlotIdx as nat), ghostSkips as nat).slot
      ensures key in Contents ==> SlotExplainsKey(Storage[..], ghostSkips as nat, key)
      ensures key !in Contents ==> FilledWithOtherKeys(Storage[..], Slot(startSlotIdx as nat), ghostSkips as nat, key) && Storage[slotIdx].Empty?
      ensures Storage[slotIdx].Filled? ==> key in Contents && key == Storage[slotIdx].key
      ensures Storage[slotIdx].Empty? ==> key !in Contents
    {
      slotIdx := Uint64SlotForKey(key);
      startSlotIdx := slotIdx;
      ghost var startSlot := Slot(startSlotIdx as nat);

      ghost var viewFromStartSlot := View(Storage[..], startSlotIdx as nat);
      ViewsHaveConsistentCounts(Storage[..], viewFromStartSlot, startSlotIdx as nat);
      CountFilledMatchesContents(Storage[..], Contents);
      assert CountFilled(Storage[..]) == CountFilled(viewFromStartSlot) == |Contents|;

      assert Storage[startSlotIdx..] + Storage[..startSlotIdx] == viewFromStartSlot;
      assert Storage[startSlotIdx..] + Storage[..startSlotIdx] ==
        viewFromStartSlot[..Storage.Length-(startSlotIdx as int)] + viewFromStartSlot[Storage.Length-(startSlotIdx as int)..];
      assert Storage[startSlotIdx..] == viewFromStartSlot[..Storage.Length-(startSlotIdx as int)];
      assert Storage[..startSlotIdx] == viewFromStartSlot[Storage.Length-(startSlotIdx as int)..];
      forall dist: nat | dist < Storage.Length
      ensures Storage[KthSlotSuccessor(Storage.Length, startSlot, dist).slot] == viewFromStartSlot[dist]
      {
        KthSlotSuccessorWrapsAround(Storage.Length, startSlot, dist);
        if dist < Storage.Length-(startSlotIdx as int) {
          assert KthSlotSuccessor(Storage.Length, startSlot, dist).slot == startSlotIdx as int + (dist as int);
          assert Storage[KthSlotSuccessor(Storage.Length, startSlot, dist).slot] == viewFromStartSlot[dist];
        } else {
          assert KthSlotSuccessor(Storage.Length, startSlot, dist).slot == (dist as int) - (Storage.Length-(startSlotIdx as int));
          assert Storage[KthSlotSuccessor(Storage.Length, startSlot, dist).slot] == viewFromStartSlot[dist];
        }
      }

      assert forall dist: nat :: dist < Storage.Length ==>
          Storage[KthSlotSuccessor(Storage.Length, startSlot, dist).slot] == viewFromStartSlot[dist];

      var skips := 0;
      ghostSkips := 0;
      while skips < (Storage.Length as uint64)
        invariant skips <= (Storage.Length as uint64)
        invariant slotIdx < (Storage.Length as uint64)
        invariant Storage.Length == |viewFromStartSlot|
        invariant Storage[startSlotIdx..] + Storage[..startSlotIdx] == viewFromStartSlot
        invariant skips == ghostSkips
        invariant slotIdx as nat == KthSlotSuccessor(Storage.Length, startSlot, skips as nat).slot
        invariant skips < (Storage.Length as uint64) ==> Storage[slotIdx] == viewFromStartSlot[skips]
        invariant ValidSlot(Storage.Length, KthSlotSuccessor(Storage.Length, startSlot, skips as nat))
        invariant FilledWithOtherKeys(Storage[..], startSlot, skips as nat, key)
        invariant CountFilled(viewFromStartSlot[..skips]) == skips as nat
      {
        if Storage[slotIdx].Empty? {
          return;
        } else if Storage[slotIdx].key == key {
          return;
        }
        assert Storage[slotIdx].Filled?;
        assert CountFilled(viewFromStartSlot[..skips]) == skips as nat;
        assert Storage[slotIdx] == viewFromStartSlot[skips];
        assert slotIdx as nat == KthSlotSuccessor(Storage.Length, startSlot, skips as nat).slot;

        ghost var slotIdxBefore := slotIdx;
        ghost var skipsBefore := skips;

        // -- increment --
        slotIdx := Uint64SlotSuccessor(slotIdx);
        skips := skips + 1;
        ghostSkips := skips;
        // ---------------

        if skips < (Storage.Length as uint64) {
          assert Storage[KthSlotSuccessor(Storage.Length, startSlot, skips as nat).slot] == viewFromStartSlot[skips];
          assert Storage[slotIdx] == viewFromStartSlot[skips];
        }
        assert CountFilled(viewFromStartSlot[..skipsBefore]) == skipsBefore as nat;
        assert viewFromStartSlot[skipsBefore].Filled?;
        assert viewFromStartSlot[..skips] == viewFromStartSlot[..skipsBefore] + [viewFromStartSlot[skipsBefore]];
        assert CountFilled([viewFromStartSlot[skipsBefore]]) == 1;
        CountFilledAdditive(viewFromStartSlot[..skipsBefore], [viewFromStartSlot[skipsBefore]]);
        assert CountFilled(viewFromStartSlot[..skips]) == skips as nat;
      }
      assert viewFromStartSlot[..skips] == viewFromStartSlot;
      assert false;
    }

    method Insert(key: uint64, value: V)
      requires Inv()
      requires Count as nat < Storage.Length - 1
      ensures Inv()
      ensures Contents == old(Contents[key := value])
      modifies this, this.Storage
    {
      var slotIdx, /* ghost */ probeStartSlotIdx, /* ghost */ probeSkips := Probe(key);

      assert FilledWithOtherKeys(Storage[..], SlotForKey(Storage.Length, key), probeSkips as nat, key);
      assert slotIdx as nat == KthSlotSuccessor(Storage.Length, SlotForKey(Storage.Length, key), probeSkips as nat).slot;

      assert forall explainedKey :: explainedKey in Contents ==>
          exists skips :: SlotExplainsKey(Storage[..], skips, explainedKey);

      // -- mutation --
      if Storage[slotIdx].Empty? {
        assert key !in Contents;
        Count := Count + 1;
      } else {
        assert key in Contents;
      }
      Storage[slotIdx] := Filled(key, value);
      Contents := Contents[key := value];
      // --------------

      assert |Contents| == (Count as nat);
      assert FilledWithOtherKeys(Storage[..], SlotForKey(Storage.Length, key), probeSkips as nat, key);
      assert FilledWithKey(Storage[..], Slot(slotIdx as nat), key);
      assert SlotExplainsKey(Storage[..], probeSkips as nat, key);

      assert key in Contents;
      forall explainedKey | explainedKey in Contents
      ensures exists skips :: SlotExplainsKey(Storage[..], skips, explainedKey)
      {
        if key == explainedKey {
          assert SlotExplainsKey(Storage[..], probeSkips as nat, key);
          assert exists skips :: SlotExplainsKey(Storage[..], skips, explainedKey);
        } else {
          var oldSkips :| SlotExplainsKey(old(Storage[..]), oldSkips, explainedKey);
          assert SlotExplainsKey(Storage[..], oldSkips, explainedKey);
          assert exists skips :: SlotExplainsKey(Storage[..], skips, explainedKey);
        }
      }

      assert forall slot1, slot2 :: (
        && ValidSlot(Storage.Length, slot1)
        && ValidSlot(Storage.Length, slot2)
        && Storage[slot1.slot].Filled?
        && Storage[slot2.slot].Filled?
        && Storage[slot1.slot].key == Storage[slot2.slot].key
      ) ==> slot1 == slot2;
      assert Count as nat < Storage.Length;
    }

  }
}
