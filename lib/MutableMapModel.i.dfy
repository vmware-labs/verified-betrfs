include "NativeTypes.s.dfy"
include "Option.s.dfy"
include "sequences.s.dfy"
include "Sets.i.dfy"
include "SetBijectivity.i.dfy"
include "Marshalling/Native.s.dfy"

module MutableMapModel {
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened Sets
  import opened SetBijectivity
  import Native

  datatype Slot = Slot(ghost slot: nat)

  datatype Item<V> = Empty | Entry(key: uint64, value: V) | Tombstone(key: uint64)

  predicate ValidSlot(elementsLength: nat, slot: Slot)
  {
    slot.slot < elementsLength
  }

  datatype LinearHashMap<V> = LinearHashMap(
    storage: seq<Item<V>>,
    count: uint64,
    /* ghost */ contents: map<uint64, Option<V>>)

  predicate ValidElements<V>(elements: seq<Item<V>>)
  {
    && 0 < |elements| < 0x10000000000000000
  }

  function SlotForKey(elementsLength: nat, key: uint64): (result: Slot)
  requires 0 < elementsLength
  ensures ValidSlot(elementsLength, result)
  {
    Slot((key as nat) % elementsLength)
  }

  function method Uint64SlotForKey<V>(self: LinearHashMap<V>, key: uint64): (result: uint64)
  requires 0 < |self.storage| < 0x10000000000000000
  ensures ValidSlot(|self.storage|, Slot(result as nat))
  ensures Slot(result as nat) == SlotForKey(|self.storage|, key)
  {
    key % (|self.storage| as uint64)
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

  protected predicate Inv<V>(self: LinearHashMap<V>)
  {
    && 128 <= |self.storage| < 0x10000000000000000
    && (self.count as nat) < 0x10000000000000000
    && self.count as nat < |self.storage|

    && |self.contents| == (self.count as nat)
    && SeqMatchesContentKeys(self.storage, self.contents)
    && EntriesMatchContentValue(self.storage, self.contents)
    && TombstonesMatchContentValue(self.storage[..], self.contents)
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
    var relation := set i | i in IndexSet(elements) :: (i, elements[i].key);
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

  function ConstructorFromSize<V>(size: uint64): (self: LinearHashMap<V>)
  requires 128 <= size
  ensures Inv(self)
  ensures forall slot :: ValidSlot(|self.storage|, slot) ==> SlotIsEmpty(self.storage, slot)
  ensures self.contents == map[]
  ensures size as nat == |self.storage|
  {
    LinearHashMap(
     /* storage := */ SeqOfLength(size as nat, Empty),
     /* count := */ 0,
     /* contents := */ map[])
  }

  // TODO is this necessary in functional land?
  function ConstructorFromStorage<V>(storage: seq<Item<V>>, count: uint64) 
  : (self: LinearHashMap<V>)
  requires 128 <= |storage|
  ensures self.storage == storage
  ensures forall slot :: ValidSlot(|self.storage|, slot) ==>
    self.storage[slot.slot] == storage[slot.slot]
  ensures self.count == count
  ensures self.contents == map[]
  {
    LinearHashMap(
     /* storage := */ storage,
     /* count := */ count,
     /* contents := */ map[])
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
    if slot == (elementsLength as uint64) - 1 then
      0
    else
      slot + 1
  }

  datatype ProbeResult<V> = ProbeResult(slotIdx: uint64, /* ghost */ startSlotIdx: uint64, /* ghost */ ghostSkips: uint64)

  function ProbeIterate<V>(
    self: LinearHashMap<V>,
    key: uint64,
    slotIdx: uint64,
    // startSlotIdx: uint64,
    // viewFromStartSlot: seq<Item<V>>,
    skips: uint64
  ) : (foundSlotIdx: uint64)
  {
    if self.storage[slotIdx].Empty? || self.storage[slotIdx].key == key then
      slotIdx
    else
      ProbeIterate(self, key, Uint64SlotSuccessor(|self.storage|, slotIdx), skips + 1)
  }

  function Probe<V>(self: LinearHashMap<V>, key: uint64): (result: ProbeResult<V>)
  requires Inv(self)
  ensures Inv(self)
  ensures ValidSlot(|self.storage|, Slot(result.slotIdx as nat))
  ensures ValidSlot(|self.storage|, Slot(result.startSlotIdx as nat))
  ensures Slot(result.startSlotIdx as nat) == SlotForKey(|self.storage|, key)
  ensures 0 <= result.ghostSkips
  ensures result.slotIdx as nat == KthSlotSuccessor(|self.storage|, Slot(result.startSlotIdx as nat), result.ghostSkips as nat).slot
  ensures key in self.contents ==> SlotExplainsKey(self.storage, result.ghostSkips as nat, key)
  ensures key !in self.contents ==> FilledWithOtherKeys(self.storage, Slot(result.startSlotIdx as nat), result.ghostSkips as nat, key) && (self.storage[result.slotIdx].Empty? || (self.storage[result.slotIdx].Tombstone? && self.storage[result.slotIdx].key == key))
  ensures self.storage[result.slotIdx].Entry? ==> key in self.contents && key == self.storage[result.slotIdx].key
  ensures self.storage[result.slotIdx].Empty? ==> key !in self.contents
  {
    var slotIdx := Uint64SlotForKey(self, key);
    var startSlotIdx := slotIdx;
    // ghost var startSlot := Slot(startSlotIdx as nat);

    ghost var viewFromStartSlot := View(self.storage, startSlotIdx as nat);
    ViewsHaveConsistentCounts(self.storage, viewFromStartSlot, startSlotIdx as nat);
    CountFilledMatchesIndexSet(self.storage);
    IndexSetMatchesContents(self.storage, self.contents);

  //   /* (doc)
  //   calc {
  //     viewFromStartSlot;
  //     Storage[startSlotIdx..] + Storage[..startSlotIdx];
  //     viewFromStartSlot[..Storage.Length-(startSlotIdx as int)] + viewFromStartSlot[Storage.Length-(startSlotIdx as int)..];
  //   }
  //   */

  // TODO proof?
  //  forall dist: nat | dist < |self.storage|
  //  ensures Storage[KthSlotSuccessor(|self.storage|, startSlot, dist).slot] == viewFromStartSlot[dist]
  //  {
  //    KthSlotSuccessorWrapsAround(|self.storage|, startSlot, dist); // observe
  //    /* (doc)
  //    if dist < Storage.Length-(startSlotIdx as int) {
  //      assert KthSlotSuccessor(Storage.Length, startSlot, dist).slot == startSlotIdx as int + (dist as int);
  //    } else {
  //      assert KthSlotSuccessor(Storage.Length, startSlot, dist).slot == (dist as int) - (Storage.Length-(startSlotIdx as int));
  //    }
  //    */
  //  }

    ProbeResult(0, 0, 0)

  //   var skips := 0;
  //   ghostSkips := 0;
  //   while skips < (Storage.Length as uint64)
  //     invariant skips <= (Storage.Length as uint64)
  //     invariant slotIdx < (Storage.Length as uint64)
  //     invariant Storage.Length == |viewFromStartSlot|
  //     invariant Storage[startSlotIdx..] + Storage[..startSlotIdx] == viewFromStartSlot
  //     invariant skips == ghostSkips
  //     invariant slotIdx as nat == KthSlotSuccessor(Storage.Length, startSlot, skips as nat).slot
  //     invariant skips < (Storage.Length as uint64) ==> Storage[slotIdx] == viewFromStartSlot[skips]
  //     invariant ValidSlot(Storage.Length, KthSlotSuccessor(Storage.Length, startSlot, skips as nat))
  //     invariant FilledWithOtherKeys(Storage[..], startSlot, skips as nat, key)
  //     invariant CountFilled(viewFromStartSlot[..skips]) == skips as nat
  //   {
  //     if Storage[slotIdx].Empty? || (Storage[slotIdx].Tombstone? && Storage[slotIdx].key == key) {
  //       return;
  //     } else if Storage[slotIdx].key == key {
  //       assert EntryInSlotMatchesContents(Storage[..], Slot(slotIdx as nat), Contents); // observe
  //       return;
  //     }
  //     /* (doc)
  //     assert Storage[slotIdx].Entry? || (Storage[slotIdx].Tombstone? && Storage[slotIdx].key != key);
  //     assert CountFilled(viewFromStartSlot[..skips]) == skips as nat;
  //     assert Storage[slotIdx] == viewFromStartSlot[skips];
  //     assert slotIdx as nat == KthSlotSuccessor(Storage.Length, startSlot, skips as nat).slot;
  //     */

  //     ghost var slotIdxBefore := slotIdx;
  //     ghost var skipsBefore := skips;

  //     // -- increment --
  //     slotIdx := Uint64SlotSuccessor(slotIdx);
  //     skips := skips + 1;
  //     ghostSkips := skips;
  //     // ---------------

  //     /* (doc)
  //     assert skips < (Storage.Length as uint64) ==> Storage[slotIdx] == viewFromStartSlot[skips];
  //     assert CountFilled(viewFromStartSlot[..skipsBefore]) == skipsBefore as nat;
  //     assert viewFromStartSlot[skipsBefore].Entry? || viewFromStartSlot[skipsBefore].Tombstone?;
  //     */
  //     assert viewFromStartSlot[..skips] == viewFromStartSlot[..skipsBefore] + [viewFromStartSlot[skipsBefore]]; // observe
  //     CountFilledAdditive(viewFromStartSlot[..skipsBefore], [viewFromStartSlot[skipsBefore]]);
  //   }

  //   forall ensures false
  //   {
  //     calc {
  //       Storage.Length;
  //       skips as nat;
  //       CountFilled(viewFromStartSlot[..skips]);
  //         { assert viewFromStartSlot[..skips] == viewFromStartSlot; } // observe
  //       CountFilled(viewFromStartSlot);
  //       |Contents|;
  //       Count as nat;
  //       < Storage.Length;
  //     }
  //     /* (doc)
  //     assert Storage.Length < Storage.Length; // at some point adding this line made the proof work,
  //                                             // which is surprising because it's the output of the calc
  //     */
  //   }
  }

  datatype Iterator<V> = Iterator(
    i: uint64, // index in hash table item list
    ghost s: set<uint64>,
    next: Option<(uint64, V)>)

  protected predicate WFIter<V>(self: LinearHashMap<V>, it: Iterator<V>)
  ensures WFIter(self, it) ==> (it.next.None? ==> it.s == self.contents.Keys)
  {
    && 0 <= it.i as int <= |self.storage|
    && (it.next.Some? ==>
      && it.i as int < |self.storage|
      && self.storage[it.i].Entry?
      && self.storage[it.i].key == it.next.value.0
      && self.storage[it.i].value == it.next.value.1
    )
    && (it.next.None? ==> (
      && it.s == self.contents.Keys
      && it.i as int == |self.storage|
    ))
    && (forall j | 0 <= j < it.i as int ::
        self.storage[j].Entry? ==> self.storage[j].key in it.s)
    && (forall key | key in it.s ::
        exists j | 0 <= j < it.i as int ::
        && self.storage[j].Entry?
        && key == self.storage[j].key)
  }

  function iterToNext<V>(self: LinearHashMap<V>, i: uint64) : (res: (uint64, Option<(uint64, V)>))
  requires Inv(self)
  requires 0 <= i as int <= |self.storage|
  ensures res.1.Some? ==> res.0 as int < |self.storage|
  ensures res.1.Some? ==> self.storage[res.0].Entry?
  ensures res.1.Some? ==> self.storage[res.0].key == res.1.value.0
  ensures res.1.Some? ==> self.storage[res.0].value == res.1.value.1
  ensures res.1.None? ==> res.0 as int == |self.storage|
  ensures forall j | i <= j < res.0 :: !self.storage[j].Entry?
  decreases |self.storage| - i as int
  {
    if i as int == |self.storage| then (
      (i, None)
    ) else if self.storage[i].Entry? then (
      (i, Some((self.storage[i].key, self.storage[i].value)))
    ) else (
      iterToNext(self, i+1)
    )
  }

  lemma EmptySetOfNoEntries<V>(self: LinearHashMap<V>)
  requires Inv(self)
  ensures (forall j | 0 <= j < |self.storage| :: !self.storage[j].Entry?) ==>
      self.contents.Keys == {};
  /*{
    if (forall j | 0 <= j < |self.storage| :: !self.storage[j].Entry?) {
      forall key | key in self.contents.Keys
      ensures false
      {
        assert key in self.contents;
        var skips :| SlotExplainsKey(self.storage, skips, key);
      }
      //assert self.contents == map[];
    }
  }*/

  function {:opaque} IterStart<V>(self: LinearHashMap<V>) : (it' : Iterator<V>)
  requires Inv(self)
  ensures WFIter(self, it')
  ensures it'.s == {}
  {
    EmptySetOfNoEntries(self);

    var (i, next) := iterToNext(self, 0);
    Iterator(i, {}, next)
  }

  /*
  function {:opaque} IterInc<V>(self: HashTable, it: Iterator) : (it' : Iterator)
  requires it.next.Some?
  requires WFIter(self, it)
  ensures WFIter(self, it')
  ensures it'.s == it.s + {it.next.value.0}
  ensures it'.next.None? ==> s == self.Contents.Keys
  {
  }
  */
}
