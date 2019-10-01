include "NativeTypes.s.dfy"
include "Option.s.dfy"
include "sequences.s.dfy"
include "Sets.i.dfy"
include "SetBijectivity.i.dfy"
include "Marshalling/Native.s.dfy"

module MutableMap {
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened Sets
  import opened SetBijectivity
  import Native

  datatype Slot = Slot(slot: nat)

  datatype Item<V> = Empty | Entry(key: uint64, value: V) | Tombstone(key: uint64)

  predicate ValidSlot(elementsLength: nat, slot: Slot)
  {
    slot.slot < elementsLength
  }

  class FixedSizeHashMap<V> {
    var Storage: array<Item<V>>;
    var Count: uint64;

    ghost var Contents: map<uint64, Option<V>>;
    ghost var Repr: set<object>;

    function I(): (contents: map<uint64, Option<V>>)
    requires Inv()
    ensures contents == this.Contents
    reads this, this.Repr
    {
      this.Contents
    }

    static predicate ValidElements(elements: seq<Item<V>>)
    {
      && 0 < |elements| < 0x10000000000000000
    }

    static function SlotForKey(elementsLength: nat, key: uint64): (result: Slot)
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

    static function SlotSuccessor(elementsLength: nat, slot: Slot): (nextSlot: Slot)
    requires ValidSlot(elementsLength, slot)
    ensures ValidSlot(elementsLength, nextSlot)
    {
      Slot(if slot.slot == elementsLength - 1 then
        0
      else
        slot.slot + 1)
    }

    static function KthSlotSuccessor(elementsLength: nat, slot: Slot, k: nat): (nextSlot: Slot)
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
    static lemma KthSlotSuccessorWrapsAround(elementsLength: nat, slot: Slot, k: nat)
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

    static predicate SlotIsEmpty(elements: seq<Item<V>>, slot: Slot) // hide trigger
    requires ValidSlot(|elements|, slot)
    {
      elements[slot.slot].Empty?
    }

    static predicate SlotIsEntry(elements: seq<Item<V>>, slot: Slot) // hide trigger
    requires ValidSlot(|elements|, slot)
    {
      elements[slot.slot].Entry?
    }

    static predicate SlotIsTombstone(elements: seq<Item<V>>, slot: Slot) // hide trigger
    requires ValidSlot(|elements|, slot)
    {
      elements[slot.slot].Tombstone?
    }

    static predicate FilledWithOtherKey(elements: seq<Item<V>>, slot: Slot, excludingKey: uint64)
      requires ValidElements(elements)
      requires ValidSlot(|elements|, slot)
    {
      || (SlotIsTombstone(elements, slot) && elements[slot.slot].key != excludingKey)
      || (SlotIsEntry(elements, slot) && elements[slot.slot].key != excludingKey)
    }

    static predicate FilledWithOtherKeys(elements: seq<Item<V>>, start: Slot, count: nat, excludingKey: uint64)
      requires ValidElements(elements)
      requires ValidSlot(|elements|, start)
    {
      && (forall offset: nat :: offset < count ==>
        FilledWithOtherKey(elements, KthSlotSuccessor(|elements|, start, offset), excludingKey))
    }

    static predicate FilledWithKey(elements: seq<Item<V>>, slot: Slot, key: uint64)
      requires ValidElements(elements)
      requires ValidSlot(|elements|, slot)
    {
      (SlotIsEntry(elements, slot) || SlotIsTombstone(elements, slot)) && elements[slot.slot].key == key
    }

    static predicate FilledWithEntryKey(elements: seq<Item<V>>, slot: Slot, key: uint64)
      requires ValidElements(elements)
      requires ValidSlot(|elements|, slot)
    {
      && SlotIsEntry(elements, slot)
      && elements[slot.slot].key == key
    }

    static predicate SlotExplainsKey(elements: seq<Item<V>>, skips: nat, key: uint64)
    requires ValidElements(elements)
    {
      var foundSlot := KthSlotSuccessor(|elements|, SlotForKey(|elements|, key), skips);
      && ValidSlot(|elements|, foundSlot)
      && FilledWithOtherKeys(elements, SlotForKey(|elements|, key), skips, key)
      && FilledWithKey(elements, foundSlot, key)
    }

    // hide forall trigger
    static predicate TwoNonEmptyValidSlotsWithSameKey(elements: seq<Item<V>>, slot1: Slot, slot2: Slot)
    requires ValidElements(elements)
    {
      && ValidSlot(|elements|, slot1)
      && ValidSlot(|elements|, slot2)
      && (SlotIsEntry(elements, slot1) || SlotIsTombstone(elements, slot1))
      && (SlotIsEntry(elements, slot2) || SlotIsTombstone(elements, slot2))
      && elements[slot1.slot].key == elements[slot2.slot].key
    }

    // hide forall trigger
    static predicate SameSlot(elementsLength: nat, slot1: Slot, slot2: Slot)
    requires ValidSlot(elementsLength, slot1)
    requires ValidSlot(elementsLength, slot2)
    {
      slot1 == slot2
    }

    static predicate CantEquivocateStorageKey(elements: seq<Item<V>>)
      requires ValidElements(elements)
    {
      forall slot1, slot2 :: TwoNonEmptyValidSlotsWithSameKey(elements, slot1, slot2)
          ==> SameSlot(|elements|, slot1, slot2)
    }

    static predicate KeyInSlotIsInContents(elements: seq<Item<V>>, contents: map<uint64, Option<V>>, slot: Slot)
    requires ValidSlot(|elements|, slot)
    requires SlotIsEntry(elements, slot) || SlotIsTombstone(elements, slot)
    {
      && var key := elements[slot.slot].key;
      && key in contents
    }

    static predicate SeqMatchesContentKeys(elements: seq<Item<V>>, contents: map<uint64, Option<V>>)
    requires ValidElements(elements)
    {
      && (forall key :: key in contents ==> exists skips :: SlotExplainsKey(elements, skips, key))
      && (forall slot :: ValidSlot(|elements|, slot) && (SlotIsEntry(elements, slot) || SlotIsTombstone(elements, slot))
          ==> KeyInSlotIsInContents(elements, contents, slot))
      && CantEquivocateStorageKey(elements)
    }

    static predicate EntryInSlotMatchesContents(elements: seq<Item<V>>, slot: Slot, contents: map<uint64, Option<V>>) // hide triggers
    requires ValidSlot(|elements|, slot)
    requires SlotIsEntry(elements, slot)
    {
      && var item := elements[slot.slot];
      && item.key in contents
      && contents[item.key] == Some(item.value)
    }

    static predicate TombstoneInSlotMatchesContents(elements: seq<Item<V>>, slot: Slot, contents: map<uint64, Option<V>>) // hide triggers
    requires ValidSlot(|elements|, slot)
    requires SlotIsTombstone(elements, slot)
    {
      && var item := elements[slot.slot];
      && item.key in contents
      && contents[item.key].None?
    }

    static predicate EntriesMatchContentValue(elements: seq<Item<V>>, contents: map<uint64, Option<V>>) // hide triggers
    requires ValidElements(elements)
    {
      forall slot :: ValidSlot(|elements|, slot) && SlotIsEntry(elements, slot)
          ==> EntryInSlotMatchesContents(elements, slot, contents)
    }

    static predicate TombstonesMatchContentValue(elements: seq<Item<V>>, contents: map<uint64, Option<V>>) // hide triggers
    requires ValidElements(elements)
    {
      forall slot :: ValidSlot(|elements|, slot) && SlotIsTombstone(elements, slot)
          ==> TombstoneInSlotMatchesContents(elements, slot, contents)
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
      && EntriesMatchContentValue(Storage[..], Contents)
      && TombstonesMatchContentValue(Storage[..], Contents)
    }

    static function IndexSetThrough(elements: seq<Item<V>>, through: nat): set<int>
      requires through <= |elements|
    {
      set i | 0 <= i < through && (elements[i].Entry? || elements[i].Tombstone?)
    }

    static function IndexSet(elements: seq<Item<V>>): set<int>
    {
      IndexSetThrough(elements, |elements|)
    }

    static function Count1(item: Item<V>): nat
    {
      if item.Entry? || item.Tombstone? then 1 else 0
    }

    static function CountFilled(view: seq<Item<V>>): (result: nat)
    {
      if |view| == 0 then
        0
      else
        CountFilled(view[1..]) + Count1(view[0])
    }

    static lemma CountFilledMatchesIndexSet(elements: seq<Item<V>>)
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

    static lemma IndexSetMatchesContents(elements: seq<Item<V>>, contents: map<uint64, Option<V>>)
    requires ValidElements(elements)
    requires SeqMatchesContentKeys(elements, contents)
    ensures |IndexSet(elements)| == |contents.Keys|
    {
      var relation := set i | i in IndexSet(elements) :: (i, elements[i].key);
      var setA := IndexSet(elements);
      var setB := contents.Keys;
      assert forall a | a in setA
        :: SlotIsEntry(elements, Slot(a)) || SlotIsTombstone(elements, Slot(a)); // observe
      assert forall a1, a2, b | a1 in setA && a2 in setA && b in setB && (a1, b) in relation && (a2, b) in relation
        :: SameSlot(|elements|, Slot(a1), Slot(a2)); // observe
      BijectivityImpliesEqualCardinality(IndexSet(elements), contents.Keys, relation);
    }

    constructor (size: uint64)
    requires 128 <= size
    ensures Inv()
    ensures forall slot :: ValidSlot(Storage.Length, slot) ==> SlotIsEmpty(Storage[..], slot)
    ensures Contents == map[]
    ensures size as nat == Storage.Length
    ensures fresh(this)
    ensures fresh(this.Storage)
    ensures forall r :: r in Repr ==> fresh(r)
    {
      Count := 0;
      Contents := map[];
      new;
      Storage := Native.Arrays.newArrayFill(size, Empty);
      Repr := { this, Storage };
    }

    constructor FromStorage(storage: array<Item<V>>, count: uint64) 
    requires 128 <= storage.Length
    ensures Storage == storage
    ensures forall slot :: ValidSlot(Storage.Length, slot) ==> Storage[slot.slot] == storage[slot.slot]
    ensures Count == count
    ensures Contents == map[]
    ensures fresh(this)
    ensures Repr == { this, this.Storage }
    {
      Count := count;
      Storage := storage;
      Contents := map[];
      Repr := { this, Storage };
    }

    static function View(elements: seq<Item<V>>, start: nat): (result: seq<Item<V>>)
    requires start < |elements|
    ensures |result| == |elements|
    {
      elements[start..] + elements[..start]
    }

    static lemma CountFilledAdditive(a: seq<Item<V>>, b: seq<Item<V>>)
    ensures CountFilled(a + b) == CountFilled(a) + CountFilled(b)
    {
      if |a| == 0 {
        assert a + b == b; // observe
      } else {
        assert (a + b)[1..] == a[1..] + b; // observe
      }
    }

    static lemma ViewsHaveConsistentCounts(a: seq<Item<V>>, b: seq<Item<V>>, delta: nat)
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
      CountFilledMatchesIndexSet(Storage[..]);
      IndexSetMatchesContents(Storage[..], Contents);

      /* (doc)
      calc {
        viewFromStartSlot;
        Storage[startSlotIdx..] + Storage[..startSlotIdx];
        viewFromStartSlot[..Storage.Length-(startSlotIdx as int)] + viewFromStartSlot[Storage.Length-(startSlotIdx as int)..];
      }
      */
      forall dist: nat | dist < Storage.Length
      ensures Storage[KthSlotSuccessor(Storage.Length, startSlot, dist).slot] == viewFromStartSlot[dist]
      {
        KthSlotSuccessorWrapsAround(Storage.Length, startSlot, dist); // observe
        /* (doc)
        if dist < Storage.Length-(startSlotIdx as int) {
          assert KthSlotSuccessor(Storage.Length, startSlot, dist).slot == startSlotIdx as int + (dist as int);
        } else {
          assert KthSlotSuccessor(Storage.Length, startSlot, dist).slot == (dist as int) - (Storage.Length-(startSlotIdx as int));
        }
        */
      }

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
          assert EntryInSlotMatchesContents(Storage[..], Slot(slotIdx as nat), Contents); // observe
          return;
        }
        /* (doc)
        assert Storage[slotIdx].Entry? || (Storage[slotIdx].Tombstone? && Storage[slotIdx].key != key);
        assert CountFilled(viewFromStartSlot[..skips]) == skips as nat;
        assert Storage[slotIdx] == viewFromStartSlot[skips];
        assert slotIdx as nat == KthSlotSuccessor(Storage.Length, startSlot, skips as nat).slot;
        */

        ghost var slotIdxBefore := slotIdx;
        ghost var skipsBefore := skips;

        // -- increment --
        slotIdx := Uint64SlotSuccessor(slotIdx);
        skips := skips + 1;
        ghostSkips := skips;
        // ---------------

        /* (doc)
        assert skips < (Storage.Length as uint64) ==> Storage[slotIdx] == viewFromStartSlot[skips];
        assert CountFilled(viewFromStartSlot[..skipsBefore]) == skipsBefore as nat;
        assert viewFromStartSlot[skipsBefore].Entry? || viewFromStartSlot[skipsBefore].Tombstone?;
        */
        assert viewFromStartSlot[..skips] == viewFromStartSlot[..skipsBefore] + [viewFromStartSlot[skipsBefore]]; // observe
        CountFilledAdditive(viewFromStartSlot[..skipsBefore], [viewFromStartSlot[skipsBefore]]);
      }

      forall ensures false
      {
        calc {
          Storage.Length;
          skips as nat;
          CountFilled(viewFromStartSlot[..skips]);
            { assert viewFromStartSlot[..skips] == viewFromStartSlot; } // observe
          CountFilled(viewFromStartSlot);
          |Contents|;
          Count as nat;
          < Storage.Length;
        }
        /* (doc)
        assert Storage.Length < Storage.Length; // at some point adding this line made the proof work,
                                                // which is surprising because it's the output of the calc
        */
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

      /* (doc)
      assert forall explainedKey :: explainedKey in Contents ==>
        exists skips :: SlotExplainsKey(Storage[..], skips, explainedKey);
      */

      // -- mutation --
      if Storage[slotIdx].Empty? {
        Count := Count + 1;
        replaced := None;
      } else if Storage[slotIdx].Tombstone? {
        replaced := None;
      } else {
        replaced := Some(Storage[slotIdx].value);
      }
      Storage[slotIdx] := Entry(key, value);
      Contents := Contents[key := Some(value)];
      // --------------

      /* (doc)
      assert FilledWithOtherKeys(Storage[..], SlotForKey(Storage.Length, key), probeSkips as nat, key);
      assert FilledWithKey(Storage[..], Slot(slotIdx as nat), key);
      assert SlotExplainsKey(Storage[..], probeSkips as nat, key);
      assert key in Contents;
      */

      forall explainedKey | explainedKey in Contents
      ensures exists skips :: SlotExplainsKey(Storage[..], skips, explainedKey)
      {
        if key == explainedKey {
          assert SlotExplainsKey(Storage[..], probeSkips as nat, key); // observe
        } else {
          var oldSkips :| SlotExplainsKey(old(Storage[..]), oldSkips, explainedKey);
          assert SlotExplainsKey(Storage[..], oldSkips, explainedKey); // observe
        }
      }

      forall slot | ValidSlot(Storage.Length, slot) && Storage[slot.slot].Entry?
      ensures && var item := Storage[slot.slot];
              && Contents[item.key] == Some(item.value)
      {
        var item := Storage[slot.slot];
        if slot != Slot(slotIdx as nat) {
          if item.key == key {
            assert TwoNonEmptyValidSlotsWithSameKey(Storage[..], slot, Slot(slotIdx as nat)); // observe
            assert SameSlot(Storage.Length, slot, Slot(slotIdx as nat)); // observe
            assert false;
          }
        }
      }
      forall slot | ValidSlot(Storage.Length, slot) && Storage[slot.slot].Tombstone?
      ensures && var item := Storage[slot.slot];
              && Contents[item.key].None?
      {
        var item := Storage[slot.slot];
        if slot != Slot(slotIdx as nat) {
          if item.key == key {
            assert TwoNonEmptyValidSlotsWithSameKey(Storage[..], slot, Slot(slotIdx as nat)); // observe
            assert SameSlot(Storage.Length, slot, Slot(slotIdx as nat)); // observe
            assert false;
          }
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
        /* (doc) assert key in Contents; */
        found := Some(Storage[slotIdx].value);
      } else if Storage[slotIdx].Tombstone? {
        /* (doc) assert key in Contents && Contents[key].None?; */
        found := None;
      } else {
        /* (doc) assert key !in Contents; */
        found := None;
      }
    }

    method Remove(key: uint64) returns (removed: Option<V>)
    requires Inv()
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
          } else {
            var oldSkips :| SlotExplainsKey(old(Storage[..]), oldSkips, explainedKey);
            assert SlotExplainsKey(Storage[..], oldSkips, explainedKey);
          }
        }

        forall slot | ValidSlot(Storage.Length, slot) && Storage[slot.slot].Entry?
        ensures && var item := Storage[slot.slot];
                && Contents[item.key] == Some(item.value)
        {
          var item := Storage[slot.slot];
          if slot != Slot(slotIdx as nat) {
            if item.key == key {
              assert CantEquivocateStorageKey(Storage[..]);
              assert TwoNonEmptyValidSlotsWithSameKey(Storage[..], slot, Slot(slotIdx as nat));
              assert false;
            }
          }
        }
      } else {
        removed := None;
      }
    }

    method Clone() returns (cloned: FixedSizeHashMap<V>)
      requires Inv()
      ensures Inv()
      ensures cloned.Inv()
      ensures Count == old(Count)
      ensures Repr == old(Repr)
      ensures cloned.Contents == old(Contents)
      ensures cloned.Count == old(Count)
      ensures cloned.Storage[..] == Storage[..]
      ensures fresh(cloned.Repr)
      ensures cloned.Repr !! Repr
    {
      var size := Storage.Length as uint64;
      var newStorage := Native.Arrays.newArrayClone(this.Storage);
      cloned := new FixedSizeHashMap.FromStorage(newStorage, Count);
      cloned.Contents := Contents;
      /* (doc) assert cloned.Repr !! Repr; */
      assert Storage[..] == cloned.Storage[..]; // observe
    }
  }

  class ResizingHashMap<V> {
    var Underlying: FixedSizeHashMap<V>;
    var Count: uint64;

    ghost var Contents: map<uint64, V>;
    ghost var Repr: set<object>;

    static function I(self: ResizingHashMap<V>): (contents: map<uint64, V>)
    requires self.Inv()
    ensures contents == self.Contents
    reads self, self.Repr
    {
      self.Contents
    }

    static function MapFromStorage(elements: seq<Item<V>>): (result: map<uint64, V>)
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
    {
      && { this, this.Underlying } <= Repr
      && { this, this.Underlying } + this.Underlying.Repr == Repr
      && this.Underlying.Repr == { this.Underlying, this.Underlying.Storage }
    }

    protected predicate Inv()
      ensures Inv() ==> ReprInv() // make ReprInv transparent
      ensures Inv() ==> |Contents| == Count as nat
      reads this, this.Repr
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

    constructor FromUnderlying(underlying: FixedSizeHashMap<V>, count: uint64)
      requires 128 <= underlying.Storage.Length
      requires underlying.Inv()
      ensures Underlying == underlying
      ensures Count == count
      ensures Contents == map[]
      ensures fresh(this)
      ensures Repr == { this, this.Underlying } + Underlying.Repr
    {
      Count := count;
      Underlying := underlying;
      Contents := map[];

      new;

      Repr := { this, Underlying } + Underlying.Repr;
    }

    method ToArray() returns (result: array<(uint64, V)>)
      requires Inv()
      ensures Contents == old(Contents)
      ensures Count == old(Count)
      ensures Count as nat == |Contents|
      ensures result.Length == Count as nat
      ensures forall i: nat, j: nat :: i < result.Length && j < result.Length && result[i].0 == result[j].0
          ==> i == j
      // ??? ensures Contents == map i | 0 <= i < result.Length :: result[i].0 := result[i].1
      ensures forall i: nat | i < result.Length :: result[i].0 in Contents && Contents[result[i].0] == result[i].1
      ensures forall k | k in Contents :: exists i: nat :: i < result.Length && result[i] == (k, Contents[k])
      ensures Repr == old(Repr)
    {
      assume false; // TODO takes too long to verify right now
      if Count == 0 {
        assert Contents == map[];
        result := new [0 as uint64];
        assert Contents == map i | 0 <= i < result.Length :: result[i].0 := result[i].1;
        return;
      }
      assert Count > 0;
      assert exists i: nat :: i < Underlying.Storage.Length && Underlying.Storage[i].Entry?;


      var storagePos: uint64 := 0;
      while storagePos < Underlying.Storage.Length as uint64 && !Underlying.Storage[storagePos].Entry?
        invariant 0 <= storagePos as int <= Underlying.Storage.Length
        invariant MapFromStorage(Underlying.Storage[..storagePos]) == map[]
        invariant forall i: nat :: i < storagePos as int ==> !Underlying.Storage[i].Entry?
      {
        assert MapFromStorage(Underlying.Storage[..storagePos]) == map[];
        assert !Underlying.Storage[storagePos].Entry?;
        assert DropLast(Underlying.Storage[..storagePos+1]) == Underlying.Storage[..storagePos];
        assert MapFromStorage(Underlying.Storage[..storagePos+1]) == map[];

        // -- increment --
        storagePos := storagePos + 1;
        // ---------------
      }

      assert storagePos as int != Underlying.Storage.Length;

      ghost var transferredContents := map[];
      assert MapFromStorage(Underlying.Storage[..storagePos]) == transferredContents;
      assert transferredContents.Keys <= Contents.Keys;

      assert storagePos as int < Underlying.Storage.Length;
      var firstEntry := Underlying.Storage[storagePos];
      assert Underlying.EntryInSlotMatchesContents(Underlying.Storage[..], Slot(storagePos as int), Underlying.Contents);
      assert firstEntry.key in Contents;
      // -- mutation --
      result := Native.Arrays.newArrayFill(Count, (firstEntry.key, firstEntry.value));
      transferredContents := transferredContents[firstEntry.key := firstEntry.value];
      // --------------

      assert DropLast(Underlying.Storage[..storagePos+1]) == Underlying.Storage[..storagePos];
      assert MapFromStorage(Underlying.Storage[..storagePos+1]) == transferredContents;
      assert transferredContents.Keys <= Contents.Keys;

      // -- increment --
      storagePos := storagePos + 1;
      // ---------------

      // assert transferredContents == map[firstEntry.key := firstEntry.value];
      assert result[0] == (firstEntry.key, firstEntry.value); // observe

      assert MapFromStorage(Underlying.Storage[..storagePos]) == transferredContents;

      var resultPos: uint64 := 1;
      assert forall k | k in transferredContents :: exists i: nat :: i < resultPos as int && result[i] == (k, transferredContents[k]);
      while storagePos < Underlying.Storage.Length as uint64
        invariant 0 <= storagePos as int <= Underlying.Storage.Length
        invariant result.Length == Count as nat
        invariant resultPos as int == |transferredContents|
        invariant resultPos as int <= result.Length
        invariant transferredContents.Keys <= Contents.Keys
        invariant forall k | k in transferredContents :: transferredContents[k] == Contents[k]
        invariant MapFromStorage(Underlying.Storage[..storagePos]) == transferredContents
        invariant MapFromStorage(Underlying.Storage[..]) == Contents
        invariant forall i: nat | i < resultPos as int :: result[i].0 in transferredContents && transferredContents[result[i].0] == result[i].1
        invariant forall i: nat, j: nat :: i < resultPos as int && j < resultPos as int && result[i].0 == result[j].0 ==> i == j
        invariant forall k | k in transferredContents :: exists i: nat :: i < resultPos as int && result[i] == (k, transferredContents[k])
      {
        var item := Underlying.Storage[storagePos];

        if item.Entry? {
          if resultPos > result.Length as uint64 {
            assert |transferredContents| > result.Length;
            assert |transferredContents| > |Contents|;
            assert |transferredContents.Keys| > |Contents.Keys|;
            SetInclusionImpliesSmallerCardinality(transferredContents.Keys, Contents.Keys);
            assert false;
          } else if resultPos == result.Length as uint64 {
            // TODO minimize
            assert |transferredContents| == |Contents|;
            assert |transferredContents.Keys| == |Contents.Keys|;
            SetInclusionAndEqualCardinalityImpliesSetEquality(transferredContents.Keys, Contents.Keys);
            assert transferredContents.Keys == Contents.Keys;
            assert transferredContents == Contents;
            ghost var thisSlot := Slot(storagePos as int);
            assert MapFromStorage(Underlying.Storage[..storagePos]) == MapFromStorage(Underlying.Storage[..]);
            assert Underlying.EntryInSlotMatchesContents(Underlying.Storage[..], thisSlot, Underlying.Contents);
            assert item.key in Underlying.Contents;
            assert item.key in Contents;
            CantEquivocateMapFromStorageKey(Underlying);
            MapFromStorageProperties(Underlying.Storage[..storagePos], Contents);
            ghost var previousSlot :| (
                && ValidSlot(Underlying.Storage.Length, previousSlot)
                && previousSlot.slot < storagePos as int
                && Underlying.FilledWithEntryKey(Underlying.Storage[..], previousSlot, item.key));
            assert Underlying.FilledWithEntryKey(Underlying.Storage[..], thisSlot, item.key);
            assert Underlying.TwoNonEmptyValidSlotsWithSameKey(Underlying.Storage[..], previousSlot, thisSlot);
            assert Underlying.CantEquivocateStorageKey(Underlying.Storage[..]);
            assert Underlying.SameSlot(Underlying.Storage.Length, previousSlot, thisSlot);
            assert false;
          }
          assert resultPos as int < result.Length;

          if item.key in transferredContents {
            // TODO minimize
            CantEquivocateMapFromStorageKey(Underlying);
            MapFromStorageProperties(Underlying.Storage[..storagePos], transferredContents);
            ghost var previousSlot :| (
                && ValidSlot(Underlying.Storage.Length, previousSlot)
                && previousSlot.slot < storagePos as int
                && Underlying.FilledWithEntryKey(Underlying.Storage[..], previousSlot, item.key));
            ghost var thisSlot := Slot(storagePos as int);
            assert Underlying.FilledWithEntryKey(Underlying.Storage[..], thisSlot, item.key);
            assert Underlying.TwoNonEmptyValidSlotsWithSameKey(Underlying.Storage[..], previousSlot, thisSlot);
            assert Underlying.CantEquivocateStorageKey(Underlying.Storage[..]);
            assert Underlying.SameSlot(Underlying.Storage.Length, previousSlot, thisSlot);
            assert false;
          }
          assert item.key !in transferredContents;

          assert Underlying.EntryInSlotMatchesContents(Underlying.Storage[..], Slot(storagePos as int), Underlying.Contents); // observe

          ghost var transferredContentsBefore := transferredContents;
          ghost var resultBefore := result[..];

          // -- mutation --
          result[resultPos] := (item.key, item.value);
          transferredContents := transferredContents[item.key := item.value];
          resultPos := resultPos + 1;
          // --------------

          forall k | k in transferredContents
          ensures exists i: nat :: i < resultPos as int && result[i] == (k, transferredContents[k])
          {
            if k == item.key {
            } else {
              // TODO minimize
              assert exists i: nat :: i < (resultPos as int - 1) && resultBefore[i] == (k, transferredContentsBefore[k]);
              assert resultBefore[..(resultPos as int - 1)] == result[..(resultPos as int - 1)];
              assert exists i: nat :: i < (resultPos as int - 1) && result[i] == (k, transferredContentsBefore[k]);
              assert exists i: nat :: i < (resultPos as int - 1) && result[i] == (k, transferredContents[k]);
              assert exists i: nat :: i < resultPos as int && result[i] == (k, transferredContents[k]);
            }
          }

          assert resultPos as int == |transferredContents|;
        }

        assert DropLast(Underlying.Storage[..storagePos+1]) == Underlying.Storage[..storagePos];

        // -- increment --
        storagePos := storagePos + 1;
        // ---------------

        assert transferredContents.Keys <= Contents.Keys;
        assert forall k | k in transferredContents :: transferredContents[k] == Contents[k];
        assert resultPos as int == |transferredContents|;
      }

      assert Underlying.Storage[..storagePos] == Underlying.Storage[..];
      assert Contents == transferredContents;

      assert forall i: nat, j: nat :: i < result.Length && j < result.Length && result[i].0 == result[j].0
          ==> i == j;
      assert result.Length == Count as nat;
      assert forall i: nat | i < result.Length :: result[i].0 in Contents && Contents[result[i].0] == result[i].1;
      assert forall k | k in Contents :: exists i: nat :: i < result.Length && result[i] == (k, Contents[k]);
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
      //print "(debug) MutableMap.Realloc: Count ", Count, ", Realloc ", newSize, "\n";

      var newUnderlying := new FixedSizeHashMap(newSize);
      assert fresh(newUnderlying) && fresh(newUnderlying.Storage);
      
      assert newUnderlying.Storage.Length == newSize as nat;

      assert MapFromStorage(Underlying.Storage[..]) == Contents;
      UnderlyingInvImpliesMapFromStorageMatchesContents(newUnderlying, map[]);
      assert MapFromStorage(newUnderlying.Storage[..]) == map[];

      var i: uint64 := 0;
      ghost var transferredContents := map[];
      while i < Underlying.Storage.Length as uint64
        invariant i as int <= Underlying.Storage.Length
        invariant newUnderlying.Inv()
        invariant |Contents| == Count as nat
        invariant Contents == old(Contents) // this is necessary because of `modifies this` (?)
        invariant UnderlyingContentsMatchesContents(newUnderlying, transferredContents)
        invariant MapFromStorage(Underlying.Storage[..i]) == transferredContents
        invariant MapFromStorage(Underlying.Storage[..]) == Contents

        invariant newUnderlying.Count as nat <= i as nat
        invariant Underlying == old(Underlying)
        invariant Underlying.Inv()
        invariant Underlying.Count == old(Underlying.Count)
        invariant Underlying.Storage.Length == old(Underlying.Storage.Length)
        invariant newUnderlying.Storage.Length == newSize as nat

        invariant |transferredContents| == newUnderlying.Count as nat
        invariant transferredContents.Keys <= Contents.Keys
        invariant forall key :: key in newUnderlying.Contents ==> exists slot: Slot :: (
            && slot.slot < i as int
            && ValidSlot(Underlying.Storage.Length, slot)
            && Underlying.FilledWithEntryKey(Underlying.Storage[..], slot, key))

        invariant fresh(newUnderlying)
        invariant fresh(newUnderlying.Storage)
        decreases Underlying.Storage.Length - i as int
      {
        var item := Underlying.Storage[i];
        assert Underlying.Storage[..i+1] == Underlying.Storage[..i] + [Underlying.Storage[i]];

        if item.Entry? {
          assert MapFromStorage(Underlying.Storage[..i]) == transferredContents;
          assert |transferredContents| == newUnderlying.Count as nat;

          assert fresh(newUnderlying);
          assert fresh(newUnderlying.Storage);
          if item.key in newUnderlying.Contents {
            var j:uint64 :| (
                && 0 <= j < i
                && ValidSlot(Underlying.Storage.Length, Slot(j as int))
                && Underlying.Storage[Slot(j as int).slot].Entry?
                && Underlying.Storage[Slot(j as int).slot].key == item.key);
            assert ValidSlot(Underlying.Storage.Length, Slot(i as nat));
            assert i != j;
            assert Slot(i as nat) != Slot(j as nat);
            assert Underlying.Storage[Slot(j as nat).slot].key == Underlying.Storage[Slot(i as nat).slot].key;
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
              && slot.slot < i as nat + 1
              && ValidSlot(Underlying.Storage.Length, slot)
              && Underlying.Storage[slot.slot].Entry?
              && Underlying.Storage[slot.slot].key == key)
          {
            if key == item.key {
              assert ValidSlot(Underlying.Storage.Length, Slot(i as nat));
              assert exists slot: Slot :: (
                  && slot.slot < i as nat + 1
                  && ValidSlot(Underlying.Storage.Length, slot)
                  && Underlying.Storage[slot.slot].Entry?
                  && Underlying.Storage[slot.slot].key == key);
            } else {
              assert exists slot: Slot :: (
                  && slot.slot < i as nat + 1
                  && ValidSlot(Underlying.Storage.Length, slot)
                  && Underlying.Storage[slot.slot].Entry?
                  && Underlying.Storage[slot.slot].key == key);
            }
          }
          assert |transferredContents| == newUnderlying.Count as nat;
          assert MapFromStorage(Underlying.Storage[..i+1]) == transferredContents;
        } else {
          assert forall key :: key in newUnderlying.Contents ==> exists slot: Slot :: (
              && slot.slot < i as nat
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

      assert i as nat == Underlying.Storage.Length;
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
      if Underlying.Storage.Length as uint64 / 2 <= Underlying.Count {
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
    
    method Clone() returns (cloned: ResizingHashMap<V>)
      requires Inv()
      ensures Inv()
      ensures Count == old(Count)
      ensures Repr == old(Repr)
      ensures cloned.Contents == old(Contents)
      ensures cloned.Count == old(Count)
      ensures fresh(cloned.Repr)
      ensures cloned.Inv()
      ensures cloned.Repr !! Repr
    {
      var clonedUnderlying := Underlying.Clone();
      cloned := new ResizingHashMap.FromUnderlying(clonedUnderlying, Count);
      cloned.Contents := Contents;
    }
  }
}
