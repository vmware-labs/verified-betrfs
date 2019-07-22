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

  datatype Item<V(==)> = Empty | Entry(key: uint64, value: V) | Tombstone(key: uint64)

  predicate ValidSlot(elementsLength: nat, slot: Slot)
  {
    slot.slot < elementsLength
  }

  // FIXME(utaal) reduce proofs!
  class FixedSizeHashMap<V(==)> {
    var Storage: array<Item<V>>;
    var Count: uint64;

    ghost var Contents: map<uint64, Option<V>>;

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
      || (elements[slot.slot].Tombstone? && elements[slot.slot].key != excludingKey)
      || (elements[slot.slot].Entry? && elements[slot.slot].key != excludingKey)
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
      (elements[slot.slot].Entry? || elements[slot.slot].Tombstone?) && elements[slot.slot].key == key
    }

    predicate SlotExplainsKey(elements: seq<Item<V>>, skips: nat, key: uint64)
      requires ValidElements(elements)
    {
      var foundSlot := KthSlotSuccessor(|elements|, SlotForKey(|elements|, key), skips);
      && ValidSlot(|elements|, foundSlot)
      && FilledWithOtherKeys(elements, SlotForKey(|elements|, key), skips, key)
      && FilledWithKey(elements, foundSlot, key)
    }

    predicate SeqMatchesContentKeys(elements: seq<Item<V>>, contents: map<uint64, Option<V>>)
      requires ValidElements(elements)
    {
      && (forall key :: key in contents ==> exists skips :: SlotExplainsKey(elements, skips, key))
      && (forall slot :: ValidSlot(|elements|, slot) && (elements[slot.slot].Entry? || elements[slot.slot].Tombstone?) ==>
        && var key := elements[slot.slot].key;
        && key in contents)
      && (forall slot1, slot2 :: (
        && ValidSlot(|elements|, slot1)
        && ValidSlot(|elements|, slot2)
        && (elements[slot1.slot].Entry? || elements[slot1.slot].Tombstone?)
        && (elements[slot2.slot].Entry? || elements[slot2.slot].Tombstone?)
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
      && SeqMatchesContentKeys(Storage[..], Contents)
      && (forall slot :: ValidSlot(Storage.Length, slot) && Storage[slot.slot].Entry? ==>
          && var item := Storage[slot.slot];
          && Contents[item.key] == Some(item.value))
      && (forall slot :: ValidSlot(Storage.Length, slot) && Storage[slot.slot].Tombstone? ==>
          && var item := Storage[slot.slot];
          && Contents[item.key].None?)
    }

    function IndexSetThrough(elements: seq<Item<V>>, through: nat): set<int>
      requires through <= |elements|
    {
      set i | 0 <= i < through && (elements[i].Entry? || elements[i].Tombstone?)
    }

    function IndexSet(elements: seq<Item<V>>): set<int>
    {
      IndexSetThrough(elements, |elements|)
    }

    function Count1(item: Item<V>): nat
    {
      if item.Entry? || item.Tombstone? then 1 else 0
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
        if elements[i].Entry? || elements[i].Tombstone? {
          assert IndexSetThrough(elements, j) == IndexSetThrough(elements, i) + {i};
        } else {
          assert IndexSetThrough(elements, j) == IndexSetThrough(elements, i);
        }
        i := j;
      }
      assert elements[..i] == elements;
    }

    lemma IndexSetMatchesContents(elements: seq<Item<V>>, contents: map<uint64, Option<V>>)
      requires ValidElements(elements)
      requires SeqMatchesContentKeys(elements, contents)
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

    lemma CountFilledMatchesContents(elements: seq<Item<V>>, contents: map<uint64, Option<V>>)
      requires ValidElements(elements)
      requires SeqMatchesContentKeys(elements, contents)
      ensures CountFilled(elements) == |contents|
    {
      CountFilledMatchesIndexSet(elements);
      IndexSetMatchesContents(elements, contents);
    }

    constructor (size: uint64)
      requires 0 < size
      ensures Inv()
      ensures forall slot :: ValidSlot(Storage.Length, slot) ==> Storage[slot.slot].Empty?
      ensures Contents == map[]
      ensures fresh(Storage)
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
      ensures key !in Contents ==> FilledWithOtherKeys(Storage[..], Slot(startSlotIdx as nat), ghostSkips as nat, key) && (Storage[slotIdx].Empty? || (Storage[slotIdx].Tombstone? && Storage[slotIdx].key == key))
      ensures Storage[slotIdx].Entry? ==> key in Contents && key == Storage[slotIdx].key
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
        if Storage[slotIdx].Empty? || (Storage[slotIdx].Tombstone? && Storage[slotIdx].key == key) {
          return;
        } else if Storage[slotIdx].key == key {
          return;
        }
        assert Storage[slotIdx].Entry? || (Storage[slotIdx].Tombstone? && Storage[slotIdx].key != key);
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
        assert viewFromStartSlot[skipsBefore].Entry? || viewFromStartSlot[skipsBefore].Tombstone?;
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
      ensures Contents == old(Contents[key := Some(value)])
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
      Storage[slotIdx] := Entry(key, value);
      Contents := Contents[key := Some(value)];
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
        && Storage[slot1.slot].Entry?
        && Storage[slot2.slot].Entry?
        && Storage[slot1.slot].key == Storage[slot2.slot].key
      ) ==> slot1 == slot2;
      assert Count as nat < Storage.Length;
    }

    method Get(key: uint64) returns (found: Option<V>)
      requires Inv()
      requires Count as nat < Storage.Length - 1
      ensures Inv()
      ensures if key in Contents && Contents[key].Some? then found == Some(Contents[key].value) else found.None?
    {
      var slotIdx, /* ghost */ probeStartSlotIdx, /* ghost */ probeSkips := Probe(key);

      if Storage[slotIdx].Entry? {
        assert key in Contents;
        found := Some(Storage[slotIdx].value);
        assert found == Contents[key];
      } else if Storage[slotIdx].Tombstone? {
        assert key in Contents && Contents[key].None?;
        found := None;
        assert found.None?;
      } else {
        assert key !in Contents;
        found := None;
        assert found.None?;
      }
    }

    method Remove(key: uint64)
      requires Inv()
      // requires Count as nat < Storage.Length - 1
      ensures Inv()
      ensures Contents == if key in Contents
          then old(Contents[key := None])
          else old(Contents)
      ensures Count == old(Count)
      modifies this, this.Storage
    {
      var slotIdx, /* ghost */ probeStartSlotIdx, /* ghost */ probeSkips := Probe(key);

      if Storage[slotIdx].Entry? {
        assert key in Contents;

        // -- mutation --
        Storage[slotIdx] := Tombstone(key);
        Contents := Contents[key := None];
        // --------------

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

        assert Storage[slotIdx].key == old(Storage[slotIdx].key) == key;
        assert Inv();
      } else {
        assert key !in Contents || (key in Contents && Contents[key].None?);
        assert Inv();
      }
    }

  }

  class ResizingHashMap<V(==)> {
    var Underlying: FixedSizeHashMap<V>;
    var Count: uint64;

    ghost var Contents: map<uint64, V>;

    function MapFromStorage(elements: seq<Item<V>>): (result: map<uint64, V>)
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

    lemma CantEquivocateMapFromStorageKey(underlying: FixedSizeHashMap<V>)
      requires underlying.Inv()
      ensures forall slot1, slot2 :: ValidSlot(underlying.Storage.Length, slot1) && ValidSlot(underlying.Storage.Length, slot2) &&
          underlying.Storage[slot1.slot].Entry? && underlying.Storage[slot2.slot].Entry? &&
          underlying.Storage[slot1.slot].key == underlying.Storage[slot2.slot].key ==> slot1 == slot2
    {
      assert underlying.Storage.Length > 0;
      assert ValidSlot(underlying.Storage.Length, Slot(0));
      assert exists slot :: ValidSlot(underlying.Storage.Length, slot);
      var slot1 :| ValidSlot(underlying.Storage.Length, slot1);
      var slot2 :| ValidSlot(underlying.Storage.Length, slot2);
      if underlying.Storage[slot1.slot].Entry? && underlying.Storage[slot2.slot].Entry? &&
        underlying.Storage[slot1.slot].key == underlying.Storage[slot2.slot].key {

        if slot1 != slot2 {
          assert false;
        }
      }
    }

    lemma MapFromStorageProperties(elements: seq<Item<V>>, result: map<uint64, V>)
      requires forall slot1, slot2 :: ValidSlot(|elements|, slot1) && ValidSlot(|elements|, slot2) &&
          elements[slot1.slot].Entry? && elements[slot2.slot].Entry? &&
          elements[slot1.slot].key == elements[slot2.slot].key ==> slot1 == slot2
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
          assume false;
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

    predicate UnderlyingContentsMatchesContents(underlying: FixedSizeHashMap<V>)
      reads this, underlying
    {
      && (forall key :: key in Contents ==> key in underlying.Contents && underlying.Contents[key] == Some(Contents[key]))
      && (forall key :: key !in Contents ==> key !in underlying.Contents || underlying.Contents[key].None?)
    }

    predicate UnderlyingInv(underlying: FixedSizeHashMap<V>)
    reads this, underlying, underlying.Storage
    {
      && |Contents| == Count as nat
      && UnderlyingContentsMatchesContents(underlying)
      && underlying.Inv()
      && MapFromStorage(underlying.Storage[..]) == Contents
    }

    lemma UnderlyingInvImpliesMapFromStorageMatchesContents(underlying: FixedSizeHashMap<V>)
      requires UnderlyingContentsMatchesContents(underlying)
      requires underlying.Inv()
      ensures MapFromStorage(underlying.Storage[..]) == Contents
    {
      // assert forall slot :: ValidSlot(underlying.Storage.Length, slot) && underlying.Storage[slot.slot].Entry? ==>
      //     && var item := underlying.Storage[slot.slot];
      //     && underlying.Contents[item.key] == Some(item.value);
      // assert forall slot :: ValidSlot(underlying.Storage.Length, slot) && underlying.Storage[slot.slot].Tombstone? ==>
      //     && var item := underlying.Storage[slot.slot];
      //     && underlying.Contents[item.key].None?;
      // assert forall key :: key in underlying.Contents && underlying.Contents[key].Some? ==>
      //     exists slot :: ValidSlot(underlying.Storage.Length, slot) &&
      //     underlying.Storage[slot.slot] == Entry(key, underlying.Contents[key].value);
      // assert forall key :: key !in underlying.Contents || underlying.Contents[key].None? ==>
      //     forall slot :: ValidSlot(underlying.Storage.Length, slot) && underlying.Storage[slot.slot].Entry? ==>
      //     underlying.Storage[slot.slot].key != key;

      // assert forall slot :: ValidSlot(underlying.Storage.Length, slot) && underlying.Storage[slot.slot].Entry? ==>
      //     && var item := underlying.Storage[slot.slot];
      //     && Contents[item.key] == item.value;
      // assert forall slot :: ValidSlot(underlying.Storage.Length, slot) && underlying.Storage[slot.slot].Tombstone? ==>
      //     && var item := underlying.Storage[slot.slot];
      //     && item.key !in Contents;

      // assert forall key :: key in Contents ==>
      //     exists slot :: ValidSlot(underlying.Storage.Length, slot) &&
      //     underlying.Storage[slot.slot] == Entry(key, Contents[key]);
      // assert forall key :: key !in Contents ==>
      //     forall slot :: ValidSlot(underlying.Storage.Length, slot) && underlying.Storage[slot.slot].Entry? ==>
      //     underlying.Storage[slot.slot].key != key;
        
      var mapFromStorage := MapFromStorage(underlying.Storage[..]);
      CantEquivocateMapFromStorageKey(underlying);
      MapFromStorageProperties(underlying.Storage[..], mapFromStorage);
      assert MapFromStorage(underlying.Storage[..]) == Contents;
    }

    predicate Inv()
    reads this, this.Underlying, this.Underlying.Storage
    {
      && UnderlyingInv(Underlying)
      && MapFromStorage(Underlying.Storage[..]) == Contents
    }

    constructor (size: uint64)
      requires 0 < size
      ensures Inv()
      ensures Contents == map[]
    {
      Count := 0;
      Underlying := new FixedSizeHashMap(size);
      Contents := map[];

      new;

      assert forall slot :: ValidSlot(Underlying.Storage.Length, slot) ==> !Underlying.Storage[slot.slot].Entry?;
      UnderlyingInvImpliesMapFromStorageMatchesContents(Underlying);
      assert MapFromStorage(Underlying.Storage[..]) == Contents;
    }

    method Realloc()
      requires Underlying.Storage.Length < 0x10000000000000000 / 2
      requires Inv()
      ensures Inv()
      ensures Contents == old(Contents)
      ensures fresh(Underlying) && fresh(Underlying.Storage)
      modifies this
    {
      assert |Contents| == Count as nat;

      assert 0 < Underlying.Storage.Length;
      var newSize: uint64 := (Underlying.Storage.Length as uint64) * 2;
      var newUnderlying: FixedSizeHashMap<V> := new FixedSizeHashMap(newSize);

      assert MapFromStorage(Underlying.Storage[..]) == Contents;
      assert MapFromStorage(newUnderlying.Storage[..]) == map[];

      var i := 0;
      ghost var transferredContents := map[];
      while i < Underlying.Storage.Length
        invariant i <= Underlying.Storage.Length
        invariant newUnderlying.Inv()
        invariant |Contents| == Count as nat
        invariant fresh(newUnderlying) && fresh(newUnderlying.Storage)
        invariant MapFromStorage(newUnderlying.Storage[..]) == transferredContents
      {
        var item := Underlying.Storage[i];
        if item.Entry? {
          newUnderlying.Insert(item.key, item.value);
          transferredContents := transferredContents[item.key := item.value];
        }

        // -- increment --
        i := i + 1;
        // ---------------
      }

      assert |Contents| == Count as nat;
      assert forall key :: key in Contents ==> key in newUnderlying.Contents && newUnderlying.Contents[key] == Some(Contents[key]);
      assert forall key :: key !in Contents ==> key !in newUnderlying.Contents || newUnderlying.Contents[key].None?;
      assert newUnderlying.Inv();
      assert UnderlyingInv(newUnderlying);

      // -- mutation --
      Underlying := newUnderlying;
      // --------------

      assert Contents == old(Contents);
      assert Inv();
    }

    // Insert
    // if Underlying.Count as nat >= Underlying.Storage.Length - 1 {
    // }

  }
}
