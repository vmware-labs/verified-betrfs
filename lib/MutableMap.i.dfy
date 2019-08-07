include "NativeTypes.s.dfy"
include "Option.s.dfy"
include "sequences.s.dfy"
include "Sets.i.dfy"
include "SetBijectivity.i.dfy"

module MutableMap {
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened Sets
  import opened SetBijectivity

  datatype Slot = Slot(slot: nat)

  datatype Item<V(==)> = Empty | Entry(key: uint64, value: V) | Tombstone(key: uint64)

  predicate ValidSlot(elementsLength: nat, slot: Slot)
  {
    slot.slot < elementsLength
  }

  // FIXME(alattuada) reduce proofs!
  class FixedSizeHashMap<V(==)> {
    var Storage: array<Item<V>>;
    var Count: uint64;

    ghost var Contents: map<uint64, Option<V>>;
    ghost var Repr: set<object>;

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

    predicate FilledWithEntryKey(elements: seq<Item<V>>, slot: Slot, key: uint64)
      requires ValidElements(elements)
      requires ValidSlot(|elements|, slot)
    {
      && elements[slot.slot].Entry?
      && elements[slot.slot].key == key
    }

    predicate SlotExplainsKey(elements: seq<Item<V>>, skips: nat, key: uint64)
      requires ValidElements(elements)
    {
      var foundSlot := KthSlotSuccessor(|elements|, SlotForKey(|elements|, key), skips);
      && ValidSlot(|elements|, foundSlot)
      && FilledWithOtherKeys(elements, SlotForKey(|elements|, key), skips, key)
      && FilledWithKey(elements, foundSlot, key)
    }

    // hide forall trigger
    predicate TwoNonEmptyValidSlotsWithSameKey(elements: seq<Item<V>>, slot1: Slot, slot2: Slot)
      requires ValidElements(elements)
    {
      && ValidSlot(|elements|, slot1)
      && ValidSlot(|elements|, slot2)
      && (elements[slot1.slot].Entry? || elements[slot1.slot].Tombstone?)
      && (elements[slot2.slot].Entry? || elements[slot2.slot].Tombstone?)
      && elements[slot1.slot].key == elements[slot2.slot].key
    }

    // hide forall trigger
    predicate SameSlot(elementsLength: nat, slot1: Slot, slot2: Slot)
      requires ValidSlot(elementsLength, slot1)
      requires ValidSlot(elementsLength, slot2)
    {
      slot1 == slot2
    }

    predicate CantEquivocateStorageKey(elements: seq<Item<V>>)
      requires ValidElements(elements)
    {
      forall slot1, slot2 :: TwoNonEmptyValidSlotsWithSameKey(elements, slot1, slot2)
          ==> SameSlot(|elements|, slot1, slot2)
    }

    predicate SlotIsEntryOrTombstone(elements: seq<Item<V>>, slot: Slot)
    {
      ValidSlot(|elements|, slot) && (elements[slot.slot].Entry? || elements[slot.slot].Tombstone?)
    }

    predicate KeyInSlotIsInContents(elements: seq<Item<V>>, contents: map<uint64, Option<V>>, slot: Slot)
      requires SlotIsEntryOrTombstone(elements, slot)
    {
      && var key := elements[slot.slot].key;
      && key in contents
    }

    predicate SeqMatchesContentKeys(elements: seq<Item<V>>, contents: map<uint64, Option<V>>)
      requires ValidElements(elements)
    {
      && (forall key :: key in contents ==> exists skips :: SlotExplainsKey(elements, skips, key))
      && (forall slot :: SlotIsEntryOrTombstone(elements, slot)
          ==> KeyInSlotIsInContents(elements, contents, slot))
      && CantEquivocateStorageKey(elements)
    }

    predicate Inv()
      reads this, this.Repr
      ensures Inv() ==> this in Repr && this.Storage in Repr
      decreases Repr, 0
      {
      && Repr == { this, this.Storage }

      && 128 <= Storage.Length < 0x10000000000000000
      && (Count as nat) < 0x10000000000000000
      && Count as nat < Storage.Length 

      && |Contents| == (Count as nat)
      && SeqMatchesContentKeys(Storage[..], Contents)
      && (forall slot :: ValidSlot(Storage.Length, slot) && Storage[slot.slot].Entry? ==>
          && var item := Storage[slot.slot];
          && item.key in Contents
          && Contents[item.key] == Some(item.value))
      && (forall slot :: ValidSlot(Storage.Length, slot) && Storage[slot.slot].Tombstone? ==>
          && var item := Storage[slot.slot];
          && item.key in Contents
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
        assert SlotIsEntryOrTombstone(elements, slot);
      }
      forall a1, a2, b | a1 in setA && a2 in setA && b in setB && (a1, b) in relation && (a2, b) in relation
      ensures a1 == a2
      {
        assert ValidSlot(|elements|, Slot(a1));
        assert ValidSlot(|elements|, Slot(a2));
        assert SameSlot(|elements|, Slot(a1), Slot(a2));
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
      requires 128 <= size
      ensures Inv()
      ensures forall slot :: ValidSlot(Storage.Length, slot) ==> Storage[slot.slot].Empty?
      ensures Contents == map[]
      ensures size as nat == Storage.Length
      ensures fresh(this)
      ensures fresh(this.Storage)
      ensures forall r :: r in Repr ==> fresh(r)
    {
      Count := 0;
      Storage := new [size] (_ => Empty);
      Contents := map[];
      Repr := { this, Storage };
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
      ensures Storage.Length == old(Storage.Length)
      ensures ValidSlot(Storage.Length, Slot(slotIdx as nat))
      ensures ValidSlot(Storage.Length, Slot(startSlotIdx as nat))
      ensures Slot(startSlotIdx as nat) == SlotForKey(Storage.Length, key)
      ensures 0 <= ghostSkips
      ensures slotIdx as nat == KthSlotSuccessor(Storage.Length, Slot(startSlotIdx as nat), ghostSkips as nat).slot
      ensures key in Contents ==> SlotExplainsKey(Storage[..], ghostSkips as nat, key)
      ensures key !in Contents ==> FilledWithOtherKeys(Storage[..], Slot(startSlotIdx as nat), ghostSkips as nat, key) && (Storage[slotIdx].Empty? || (Storage[slotIdx].Tombstone? && Storage[slotIdx].key == key))
      ensures Storage[slotIdx].Entry? ==> key in Contents && key == Storage[slotIdx].key
      ensures Storage[slotIdx].Empty? ==> key !in Contents
      ensures Repr == old(Repr)
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
        assert FilledWithOtherKeys(Storage[..], startSlot, skips as nat, key);
      }

      assert viewFromStartSlot[..skips] == viewFromStartSlot;
      forall ensures false
      {
        calc {
          Storage.Length;
          skips as nat;
          CountFilled(viewFromStartSlot[..skips]);
          CountFilled(viewFromStartSlot);
          |Contents|;
          Count as nat;
          < Storage.Length;
        }
        assert Storage.Length < Storage.Length; // adding this line makes the proof work,
                                                // which is surprising because it's the output of the calc
      }
    }

    method Insert(key: uint64, value: V) returns (replaced: Option<V>)
      requires Inv()
      requires Count as nat < Storage.Length - 1
      ensures Inv()
      ensures Contents == old(Contents[key := Some(value)])
      ensures old(key in Contents) ==> replaced == old(Contents[key])
      ensures replaced.Some? ==> old(key in Contents)
      ensures old(key !in Contents) ==> replaced.None?
      ensures old(Count as nat) <= Count as nat <= old(Count as nat) + (if replaced.Some? then 0 else 1)
      ensures old(key !in Contents) ==> Count as nat == old(Count as nat) + 1
      ensures Storage == old(Storage) // this was a surprising requirement, can be avoided with deeply-non-aliased types?
      ensures Storage.Length == old(Storage.Length)
      ensures forall r :: r in Repr ==> r in old(Repr) || fresh(r)
      modifies Repr
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
        replaced := None;
      } else if Storage[slotIdx].Tombstone? {
        assert key in Contents;
        replaced := None;
      } else {
        assert key in Contents;
        replaced := Some(Storage[slotIdx].value);
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

      assert CantEquivocateStorageKey(Storage[..]);
      assert Count as nat < Storage.Length;

      forall slot | ValidSlot(Storage.Length, slot) && Storage[slot.slot].Entry?
      ensures && var item := Storage[slot.slot];
              && Contents[item.key] == Some(item.value)
      {
        var item := Storage[slot.slot];
        if slot == Slot(slotIdx as nat) {
          assert Contents[item.key] == Some(item.value);
        } else {
          assert Storage[slot.slot] == old(Storage[slot.slot]);
          if item.key == key {
            assert TwoNonEmptyValidSlotsWithSameKey(Storage[..], slot, Slot(slotIdx as nat));
            assert false;
          }
          assert item.key != key;
          assert Contents[item.key] == Some(item.value);
        }
      }
      forall slot | ValidSlot(Storage.Length, slot) && Storage[slot.slot].Tombstone?
      ensures && var item := Storage[slot.slot];
              && Contents[item.key].None?
      {
        var item := Storage[slot.slot];
        if slot == Slot(slotIdx as nat) {
          assert Contents[item.key].None?;
        } else {
          if item.key == key {
            assert TwoNonEmptyValidSlotsWithSameKey(Storage[..], slot, Slot(slotIdx as nat));
            assert false;
          }
          assert item.key != key;
          assert Contents[item.key].None?;
        }
      }
    }

    method Get(key: uint64) returns (found: Option<V>)
      requires Inv()
      ensures Inv()
      ensures Contents == old(Contents)
      ensures Count == old(Count)
      ensures Repr == old(Repr)
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

    method Remove(key: uint64) returns (removed: Option<V>)
      requires Inv()
      // requires Count as nat < Storage.Length - 1
      ensures Inv()
      ensures Contents == if key in old(Contents)
          then old(Contents[key := None])
          else old(Contents)
      ensures removed == if old(key in Contents) && old(Contents[key].Some?)
          then Some(old(Contents[key].value))
          else None
      ensures Count == old(Count)
      ensures Repr == old(Repr)
      modifies Repr
    {
      var slotIdx, /* ghost */ probeStartSlotIdx, /* ghost */ probeSkips := Probe(key);

      if Storage[slotIdx].Entry? {
        assert key in Contents;

        // -- mutation --
        removed := Some(Storage[slotIdx].value);
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
        assert CantEquivocateStorageKey(Storage[..]);

        forall slot | ValidSlot(Storage.Length, slot) && Storage[slot.slot].Entry?
        ensures && var item := Storage[slot.slot];
                && Contents[item.key] == Some(item.value)
        {
          var item := Storage[slot.slot];
          if slot == Slot(slotIdx as nat) {
          } else {
            if item.key == key {
              assert TwoNonEmptyValidSlotsWithSameKey(Storage[..], slot, Slot(slotIdx as nat));
              assert false;
            }
            assert item.key != key;
          }
        }
        assert Inv();
      } else {
        removed := None;
        assert removed == if old(key in Contents) && old(Contents[key].Some?)
            then Some(old(Contents[key].value))
            else None;
        assert key !in Contents || (key in Contents && Contents[key].None?);
        assert Inv();
      }
    }

  }

  class ResizingHashMap<V(==)> {
    var Underlying: FixedSizeHashMap<V>;
    var Count: uint64;

    ghost var Contents: map<uint64, V>;
    ghost var Repr: set<object>;

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
      forall slot1, slot2 | (
        && ValidSlot(underlying.Storage.Length, slot1) && ValidSlot(underlying.Storage.Length, slot2)
        && underlying.Storage[slot1.slot].Entry? && underlying.Storage[slot2.slot].Entry?
        && underlying.Storage[slot1.slot].key == underlying.Storage[slot2.slot].key)
      ensures slot1 == slot2
      {
        assert underlying.CantEquivocateStorageKey(underlying.Storage[..]);
        if underlying.Storage[slot1.slot].Entry? && underlying.Storage[slot2.slot].Entry? &&
          underlying.Storage[slot1.slot].key == underlying.Storage[slot2.slot].key {

          assert underlying.TwoNonEmptyValidSlotsWithSameKey(underlying.Storage[..], slot1, slot2);
          if slot1 != slot2 {
            assert false;
          }
          assert slot1 == slot2;
        } else {
          assert slot1 == slot2;
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

    predicate UnderlyingContentsMatchesContents(underlying: FixedSizeHashMap<V>, contents: map<uint64, V>)
      reads this, underlying
    {
      && (forall key :: key in contents ==> key in underlying.Contents && underlying.Contents[key] == Some(contents[key]))
      && (forall key :: key !in contents ==> key !in underlying.Contents || underlying.Contents[key].None?)
    }

    predicate UnderlyingInv(underlying: FixedSizeHashMap<V>)
    reads this, this.Repr, underlying, underlying.Repr
    {
      && |Contents| == Count as nat
      && UnderlyingContentsMatchesContents(underlying, Contents)
      && underlying.Inv()
      && MapFromStorage(underlying.Storage[..]) == Contents
    }

    lemma UnderlyingInvImpliesMapFromStorageMatchesContents(underlying: FixedSizeHashMap<V>, contents: map<uint64, V>)
      requires UnderlyingContentsMatchesContents(underlying, contents)
      requires underlying.Inv()
      ensures MapFromStorage(underlying.Storage[..]) == contents
    {
      var mapFromStorage := MapFromStorage(underlying.Storage[..]);
      CantEquivocateMapFromStorageKey(underlying);
      MapFromStorageProperties(underlying.Storage[..], mapFromStorage);
      assert MapFromStorage(underlying.Storage[..]) == contents;
    }

    predicate ReprInv()
      reads this, this.Repr
      ensures ReprInv() ==> this in Repr && this.Underlying in Repr
    {
      && { this, this.Underlying } <= Repr
      && { this, this.Underlying } + this.Underlying.Repr == Repr
      && this.Underlying.Repr == { this.Underlying, this.Underlying.Storage }
    }

    protected predicate Inv()
      reads this, this.Repr
      ensures Inv() ==> ReprInv() // make ReprInv transparent
    {
      && ReprInv()

      && UnderlyingInv(Underlying)
      && MapFromStorage(Underlying.Storage[..]) == Contents
      && |Contents| == Count as nat
    }

    constructor (size: uint64)
      requires 128 <= size
      ensures Inv()
      ensures Contents == map[]
      ensures fresh(this)
      ensures fresh(this.Underlying)
      ensures fresh(this.Underlying.Storage)
      ensures forall r :: r in Repr ==> fresh(r)
    {
      Count := 0;
      Underlying := new FixedSizeHashMap(size);
      Contents := map[];

      new;

      Repr := { this, Underlying } + Underlying.Repr;

      assert forall slot :: ValidSlot(Underlying.Storage.Length, slot) ==> !Underlying.Storage[slot.slot].Entry?;
      UnderlyingInvImpliesMapFromStorageMatchesContents(Underlying, Contents);
      assert MapFromStorage(Underlying.Storage[..]) == Contents;
    }

    method ToArray() returns (result: array<(uint64, V)>)
      requires Inv()
      ensures Contents == old(Contents)
      ensures forall i: nat, j: nat :: i < result.Length && j < result.Length && result[i].0 == result[j].0
          ==> i == j
      ensures Contents == map i | 0 <= i < result.Length :: result[i].0 := result[i].1
      ensures Repr == old(Repr)
    {
      if Count == 0 {
        assert Contents == map[];
        result := new [0];
        assert Contents == map i | 0 <= i < result.Length :: result[i].0 := result[i].1;
        return;
      }
      assert Count > 0;
      assert exists i: nat :: i < Underlying.Storage.Length && Underlying.Storage[i].Entry?;


      var storagePos := 0;
      while storagePos < Underlying.Storage.Length && !Underlying.Storage[storagePos].Entry?
        invariant 0 <= storagePos <= Underlying.Storage.Length
        invariant MapFromStorage(Underlying.Storage[..storagePos]) == map[]
        invariant forall i: nat :: i < storagePos ==> !Underlying.Storage[i].Entry?
      {
        assert MapFromStorage(Underlying.Storage[..storagePos]) == map[];
        assert !Underlying.Storage[storagePos].Entry?;
        assert DropLast(Underlying.Storage[..storagePos+1]) == Underlying.Storage[..storagePos];
        assert MapFromStorage(Underlying.Storage[..storagePos+1]) == map[];

        // -- increment --
        storagePos := storagePos + 1;
        // ---------------
      }
      if storagePos == Underlying.Storage.Length {
        assert false;
      }

      ghost var transferredContents := map[];
      assert MapFromStorage(Underlying.Storage[..storagePos]) == transferredContents;
      assert transferredContents.Keys <= Contents.Keys;

      assert storagePos < Underlying.Storage.Length;
      var firstEntry := Underlying.Storage[storagePos];
      assume firstEntry.key in Contents;
      // -- mutation --
      result := new [Count] (_ => (firstEntry.key, firstEntry.value));
      transferredContents := transferredContents[firstEntry.key := firstEntry.value];
      // --------------

      assert DropLast(Underlying.Storage[..storagePos+1]) == Underlying.Storage[..storagePos];
      assert MapFromStorage(Underlying.Storage[..storagePos+1]) == transferredContents;
      assert transferredContents.Keys <= Contents.Keys;

      // -- increment --
      storagePos := storagePos + 1;
      // ---------------

      assert MapFromStorage(Underlying.Storage[..storagePos]) == transferredContents;

      var resultPos := 1;
      while storagePos < Underlying.Storage.Length
        invariant 0 <= storagePos <= Underlying.Storage.Length
        invariant result.Length == Count as nat
        invariant resultPos == |transferredContents|
        invariant transferredContents.Keys <= Contents.Keys
        invariant MapFromStorage(Underlying.Storage[..storagePos]) == transferredContents
        invariant MapFromStorage(Underlying.Storage[..]) == Contents
      {
        var item := Underlying.Storage[storagePos];

        if item.Entry? {
          if resultPos > result.Length {
            assert |transferredContents| > result.Length;
            assert |transferredContents| > |Contents|;
            assert |transferredContents.Keys| > |Contents.Keys|;
            SetInclusionImpliesSmallerCardinality(transferredContents.Keys, Contents.Keys);
            assert false;
          } else if resultPos == result.Length {
            assume false;
            assert |transferredContents| == |Contents|;
            assert |transferredContents.Keys| == |Contents.Keys|;
            SetInclusionAndEqualCardinalityImpliesSetEquality(transferredContents.Keys, Contents.Keys);
            assert transferredContents.Keys == Contents.Keys;
            assert transferredContents == Contents;
            MapFromStorageProperties(Underlying.Storage[..], Contents);
            assert exists slot :: (
                && ValidSlot(Underlying.Storage.Length, slot)
                && slot.slot < storagePos
                && Underlying.FilledWithEntryKey(Underlying.Storage[..], slot, item.key));
          }
          assert resultPos < result.Length;
          // -- mutation --
          result[resultPos] := (item.key, item.value);
          // --------------

          assume item.key !in transferredContents;

          // -- mutation --
          transferredContents := transferredContents[item.key := item.value];
          resultPos := resultPos + 1;
          // --------------

          assert resultPos == |transferredContents|;
        }

        assume false;

        assert DropLast(Underlying.Storage[..storagePos+1]) == Underlying.Storage[..storagePos];

        // -- increment --
        storagePos := storagePos + 1;
        // ---------------

        assert resultPos == |transferredContents|;
      }

      assume false;
      assert forall i: nat, j: nat :: i < result.Length && j < result.Length && result[i].0 == result[j].0
          ==> i == j;
      assert Contents == map i | 0 <= i < result.Length :: result[i].0 := result[i].1;
    }

    method ToMap() returns (result: map<uint64, V>)
      requires Inv()
      ensures Contents == old(Contents)
      ensures Contents == result
      ensures Repr == old(Repr)
    {
      assume false;
      var asArray := ToArray();
      result := map i: nat | i < asArray.Length :: asArray[i].0 := asArray[i].1;
    }

    method Realloc()
      requires Count as nat < 0x10000000000000000 / 8
      requires Inv()
      ensures Inv()
      ensures Contents == old(Contents)
      ensures Underlying.Count as nat < Underlying.Storage.Length - 2
      ensures fresh(Underlying)
      ensures fresh(Underlying.Storage)
      ensures forall r :: r in Repr ==> r in old(Repr) || fresh(r)
      modifies this
    {

      assert |Contents| == Count as nat;

      var newSize: uint64 := (128 + Count) * 4;
      print "(debug) Count ", Count, ", Realloc ", newSize, "\n";

      var newUnderlying := new FixedSizeHashMap(newSize);
      assert fresh(newUnderlying) && fresh(newUnderlying.Storage);
      
      assert newUnderlying.Storage.Length == newSize as nat;
      // assert newUnderlying.Storage.Length == (Underlying.Storage.Length as uint64 * 2) as nat;

      assert MapFromStorage(Underlying.Storage[..]) == Contents;
      UnderlyingInvImpliesMapFromStorageMatchesContents(newUnderlying, map[]);
      assert MapFromStorage(newUnderlying.Storage[..]) == map[];

      var i := 0;
      ghost var transferredContents := map[];
      while i < Underlying.Storage.Length
        invariant i <= Underlying.Storage.Length
        invariant newUnderlying.Inv()
        invariant |Contents| == Count as nat
        invariant Contents == old(Contents) // this is necessary because of `modifies this` (?)
        invariant UnderlyingContentsMatchesContents(newUnderlying, transferredContents)
        invariant MapFromStorage(Underlying.Storage[..i]) == transferredContents
        invariant MapFromStorage(Underlying.Storage[..]) == Contents

        invariant newUnderlying.Count as nat <= i
        invariant Underlying == old(Underlying)
        invariant Underlying.Inv()
        invariant Underlying.Count == old(Underlying.Count)
        invariant Underlying.Storage.Length == old(Underlying.Storage.Length)
        invariant newUnderlying.Storage.Length == newSize as nat
        // invariant newUnderlying.Storage.Length == (Underlying.Storage.Length as uint64 * 2) as nat

        invariant |transferredContents| == newUnderlying.Count as nat
        invariant transferredContents.Keys <= Contents.Keys
        invariant forall key :: key in newUnderlying.Contents ==> exists slot: Slot :: (
            && slot.slot < i
            && ValidSlot(Underlying.Storage.Length, slot)
            && Underlying.FilledWithEntryKey(Underlying.Storage[..], slot, key))

        invariant fresh(newUnderlying)
        invariant fresh(newUnderlying.Storage)
        decreases Underlying.Storage.Length - i
      {
        var item := Underlying.Storage[i];
        assert Underlying.Storage[..i+1] == Underlying.Storage[..i] + [Underlying.Storage[i]];

        if item.Entry? {
          assert MapFromStorage(Underlying.Storage[..i]) == transferredContents;
          assert |transferredContents| == newUnderlying.Count as nat;

          assert fresh(newUnderlying);
          assert fresh(newUnderlying.Storage);
          if item.key in newUnderlying.Contents {
            var j :| (
                && 0 <= j < i
                && ValidSlot(Underlying.Storage.Length, Slot(j))
                && Underlying.Storage[Slot(j).slot].Entry?
                && Underlying.Storage[Slot(j).slot].key == item.key);
            assert ValidSlot(Underlying.Storage.Length, Slot(i));
            assert i != j;
            assert Slot(i) != Slot(j);
            assert Underlying.Storage[Slot(j).slot].key == Underlying.Storage[Slot(i).slot].key;
            CantEquivocateMapFromStorageKey(Underlying);
            assert false;
          }
          assert item.key !in newUnderlying.Contents;

          assert transferredContents.Keys <= Contents.Keys;
          SetInclusionImpliesSmallerCardinality(transferredContents.Keys, Contents.Keys);
          assert |transferredContents.Keys| <= |Contents.Keys|;
          assert |transferredContents.Keys| == |transferredContents|;
          assert |Contents.Keys| == |Contents|;
          assert |transferredContents| <= |Contents|;
          assert newUnderlying.Count as nat < newUnderlying.Storage.Length - 1;
          // -- mutation --
          ghost var _ := newUnderlying.Insert(item.key, item.value);
          transferredContents := transferredContents[item.key := item.value];
          // --------------

          forall key | key in newUnderlying.Contents
          ensures exists slot: Slot :: (
              && slot.slot < i + 1
              && ValidSlot(Underlying.Storage.Length, slot)
              && Underlying.Storage[slot.slot].Entry?
              && Underlying.Storage[slot.slot].key == key)
          {
            if key == item.key {
              assert ValidSlot(Underlying.Storage.Length, Slot(i));
              assert exists slot: Slot :: (
                  && slot.slot < i + 1
                  && ValidSlot(Underlying.Storage.Length, slot)
                  && Underlying.Storage[slot.slot].Entry?
                  && Underlying.Storage[slot.slot].key == key);
            } else {
              assert exists slot: Slot :: (
                  && slot.slot < i + 1
                  && ValidSlot(Underlying.Storage.Length, slot)
                  && Underlying.Storage[slot.slot].Entry?
                  && Underlying.Storage[slot.slot].key == key);
            }
          }
          assert |transferredContents| == newUnderlying.Count as nat;
          assert MapFromStorage(Underlying.Storage[..i+1]) == transferredContents;
        } else {
          assert forall key :: key in newUnderlying.Contents ==> exists slot: Slot :: (
              && slot.slot < i
              && ValidSlot(Underlying.Storage.Length, slot)
              && Underlying.Storage[slot.slot].Entry?
              && Underlying.Storage[slot.slot].key == key);
          assert |transferredContents| <= newUnderlying.Count as nat;
          assert MapFromStorage(Underlying.Storage[..i+1]) == transferredContents;
        }

        // -- increment --
        i := i + 1;
        // ---------------

        assert MapFromStorage(Underlying.Storage[..i]) == transferredContents;
      }

      assert i == Underlying.Storage.Length;
      assert Underlying.Storage[..i] == Underlying.Storage[..];

      assert MapFromStorage(Underlying.Storage[..]) == transferredContents;
      UnderlyingInvImpliesMapFromStorageMatchesContents(newUnderlying, transferredContents);
      assert transferredContents == Contents;

      assert |Contents| == Count as nat;

      assert forall key :: key in Contents ==> key in newUnderlying.Contents && newUnderlying.Contents[key] == Some(Contents[key]);
      assert forall key :: key !in Contents ==> key !in newUnderlying.Contents || newUnderlying.Contents[key].None?;

      assert newUnderlying.Inv();
      assert UnderlyingInv(newUnderlying);
      assert UnderlyingContentsMatchesContents(newUnderlying, Contents);
      assert MapFromStorage(newUnderlying.Storage[..]) == Contents;
      assert newUnderlying.Count as nat < newUnderlying.Storage.Length - 2;

      assert fresh(newUnderlying);
      assert fresh(newUnderlying.Storage);

      // -- mutation --
      Underlying := newUnderlying;
      // --------------

      assert fresh(Underlying);
      assert fresh(Underlying.Storage);
      Repr := { this, Underlying } + Underlying.Repr;
      assert Underlying.Repr == { Underlying, Underlying.Storage };
      assert Repr == { this, Underlying, Underlying.Storage };
      assert forall r :: r in Repr ==> r in old(Repr) || fresh(r);

      assert Underlying.Count as nat < Underlying.Storage.Length - 2;
      assert Contents == old(Contents);
      assert Count == old(Count);
      assert Count <= Underlying.Count;
      assert Inv();
    }

    method Insert(key: uint64, value: V) returns (replaced: Option<V>)
      requires Inv()
      requires Count as nat < 0x10000000000000000 / 8
      ensures Inv()
      ensures Contents == old(Contents[key := value])
      ensures Count as nat == old(Count as nat) + (if replaced.Some? then 0 else 1)
      ensures forall r :: r in Repr ==> r in old(Repr) || fresh(r)
      modifies Repr
    {
      // print "Insert ", key, "\n";

      // -- mutation --
      if Underlying.Storage.Length / 2 <= Underlying.Count as nat {
        Realloc();
      }
      // --------------

      assert MapFromStorage(Underlying.Storage[..]) == Contents;
      assert Underlying.Count as nat < Underlying.Storage.Length - 2;

      // -- mutation --
      replaced := Underlying.Insert(key, value);
      Contents := Contents[key := value];
      // --------------

      if replaced.None? {
        assert old(key !in Contents);
        Count := Count + 1;
      } else {
        assert old(key in Contents);
      }

      assert Underlying.Count as nat < Underlying.Storage.Length - 1;

      UnderlyingInvImpliesMapFromStorageMatchesContents(Underlying, Contents);
      assert MapFromStorage(Underlying.Storage[..]) == Contents;
      assert UnderlyingInv(Underlying);
      assert Inv();
    }

    method Remove(key: uint64) returns (removed: Option<V>)
      requires Inv()
      ensures Inv()
      ensures Contents == if key in old(Contents)
          then map k | old(k in Contents) && k != key :: old(Contents[k])
          else old(Contents)
      ensures removed == if old(key in Contents)
          then Some(old(Contents)[key])
          else None
      ensures Count as nat == old(Count as nat) - (if removed.Some? then 1 else 0)
      ensures Repr == old(Repr)
      modifies Repr
    {
      // -- mutation --
      removed := Underlying.Remove(key);
      assert Contents == old(Contents);
      Contents := map k | k in Contents && k != key :: Contents[k];
      if removed.Some? {
        Count := Count - 1;
        assert old(key in Contents);
        assert Contents.Keys <= old(Contents.Keys);
        assert old(|Contents|) == Count as nat + 1;
        assert old(|Contents.Keys|) == Count as nat + 1;
        assert old(|Contents.Keys - {key}|) == old(|Contents.Keys| - |{key}|);
        assert old(Contents.Keys - {key}) == Contents.Keys;
        assert |Contents| == old(|Contents|) - 1;
        assert |Contents| == Count as nat;
      } else {
        assert old(key !in Contents);
        assert Contents == old(Contents);
        assert |Contents| == Count as nat;
      }
      // --------------

      assert UnderlyingContentsMatchesContents(Underlying, Contents);
      UnderlyingInvImpliesMapFromStorageMatchesContents(Underlying, Contents);
      assert MapFromStorage(Underlying.Storage[..]) == Contents;
      assert |Contents| == Count as nat;
    }

    method Get(key: uint64) returns (found: Option<V>)
      requires Inv()
      ensures Inv()
      ensures Count == old(Count)
      ensures Repr == old(Repr)
      ensures if key in Contents then found == Some(Contents[key]) else found.None?
      ensures found.Some? <==> key in Contents
    {
      found := Underlying.Get(key);
    }
  }
}
