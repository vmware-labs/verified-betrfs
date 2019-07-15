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
    
    // lemma EmptySlotPresentWhenNotFull()
    //   requires Inv()
    //   ensures (Count as int) < Storage.Length ==> (
    //     exists slot :: ValidSlot(Storage.Length as uint64, slot) && Storage[slot.slot].Empty?)
    // {
    //   if (Count as int) == Storage.Length {
    //   } else if (Count as int) < Storage.Length {
    //     assume exists slot :: ValidSlot(Storage.Length as uint64, slot) && Storage[slot.slot].Empty?;
    //   } else {
    //     assert false;
    //   }
    // }

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
      assume (Count as int) < Storage.Length ==> Storage[emptySlot.slot].Empty?;
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
      // && ValidSlot(Storage.Length as uint64, s);
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
      if key in Contents {
        assert false;
      }
      assert key !in Contents;
    }

    // method InsertNewKey(key: uint64)
    //   requires key !in Contents
    //   ensures newContents == contents[item.0 := item.1]


  // //method insert_internal<V(==)>(
  // //  storage: array<Option<(uint64, V)>>,
  // //  item: (uint64, V),
  // //  ghost contents: map<uint64, V>,
  // //  count: uint64) returns (ghost newContents: map<uint64, V>, newCount: uint64)

  // //  requires (count as int) < storage.Length // exists i :: 0 <= i < storage.Length && storage[i].None?
  // //  requires StorageInv(storage, contents, count)
  // //  ensures StorageInv(storage, newContents, newCount)
  // //  ensures newContents == contents[item.0 := item.1]
  // //  modifies storage
  // //{
  // //  // ghost var hole :| 0 <= hole < storage.Length && storage[hole].None?;
  // //  // ghost var storageSeq := storage[..];

  // //  var (key, value) := item;
  // //  var pos: uint64 := key % (storage.Length as uint64);
  // //  var startPos: uint64 := pos;

  // //  // ghost var left := storageSeq[..startPos];
  // //  // ghost var right := storageSeq[startPos..];
  // //  // assert left + right == storageSeq;

  // //  while (pos as int) < storage.Length && storage[pos].Some? && storage[pos].value.0 != key
  // //    invariant (pos as int) <= storage.Length
  // //    invariant storage == old(storage)
  // //    invariant forall i :: (startPos as int) <= i < (pos as int) ==> storage[i].Some? && storage[i].value.0 != key
  // //  {
  // //    pos := pos + 1; // % (storage.Length as uint64);
  // //  }

  // //  assert (startPos as int) < storage.Length;

  // //  if (pos as int) == storage.Length {
  // //    assert forall i :: (startPos as int) <= i < storage.Length ==> storage[i].Some? && storage[i].value.0 != key;
  // //    // assert forall i :: 0 <= i < |right| ==> right[i].Some? && hole != i;

  // //    pos := 0;
  // //    if 0 < startPos {
  // //      while pos < (startPos - 1) && storage[pos].Some? && storage[pos].value.0 != key
  // //        invariant pos < startPos
  // //        invariant storage == old(storage)
  // //        invariant forall i :: (startPos as int) <= i < storage.Length ==> storage[i].Some? && storage[i].value.0 != key
  // //        invariant forall i :: 0 <= i < (pos as int) ==> storage[i].Some? && storage[i].value.0 != key
  // //      {
  // //        pos := pos + 1;
  // //      }
  // //    }
  // //  }

  // //  assert 0 <= (pos as int) < storage.Length;
  // //  assert storage[pos].None? || storage[pos].value.0 == key;

  // //  var found := false;

  // //  if storage[pos].None? {
  // //  } else {
  // //    found := true;
  // //    assert storage[pos].Some? && storage[pos].value.0 == key;
  // //    assert key in contents;
  // //  }

  // //  assert (forall i :: (0 <= i < storage.Length && storage[i].Some?) ==>
  // //      storage[i].value.0 in contents && storage[i].value.1 == contents[storage[i].value.0]);

  // //  storage[pos] := Some(item);
  // //  newCount := if found then count else count + 1;
  // //  newContents := contents[item.0 := item.1];

  // //  if !found {
  // //    assert !found;
  // //    assert newCount == count + 1;
  // //    assert key !in contents; //

  // //    assert |newContents| == (newCount as int);
  // //    assert forall k :: k in newContents ==> (
  // //        exists i :: 0 <= i < storage.Length && storage[i].Some? && storage[i].value == (k, newContents[k]));
  // //    assert newCount as int < storage.Length ==> exists hole :: 0 <= hole < storage.Length && storage[hole].None?;
  // //    assert (forall i :: (0 <= i < storage.Length && storage[i].Some?) ==>
  // //        storage[i].value.0 in contents && storage[i].value.1 == contents[storage[i].value.0]);
  // //  } else {
  // //    assert found;
  // //    assert old(storage[pos]).Some? && old(storage[pos]).value.0 == key;
  // //    assert newCount == count;
  // //    assert item == old(item);
  // //    assert item.0 in contents; //
  // //    assert |newContents| == (newCount as int);
  // //    assert forall k :: k in newContents ==> (
  // //        exists i :: 0 <= i < storage.Length && storage[i].Some? && storage[i].value == (k, newContents[k]));
  // //    assert newCount as int < storage.Length ==> exists hole :: 0 <= hole < storage.Length && storage[hole].None?;
  // //    assert (forall i :: (0 <= i < storage.Length && storage[i].Some?) ==>
  // //        storage[i].value.0 in contents && storage[i].value.1 == contents[storage[i].value.0]);
  // //  }
  // //}

    // function ContentsLessAKey(contents: map<uint64, V>, key: uint64): (result: map<uint64, V>)
    //   requires key in contents
    //   ensures |result| == |contents| - 1
    // {
    //   // assert |MapRemove(contents, {key})| == |contents| - 1;
    //   var newKeys := contents.Keys - { key };
    //   assert |newKeys| == |contents| - 1;
    //   var result := map j | j in newKeys :: contents[j];
    //   // assert result == MapRemove(contents, {key});
    //   result
    // }

    // lemma HoleRecursion(elements: seq<Item<V>>, contents: map<uint64, V>)
    //   requires ValidElements(elements)
    //   requires 1 < |elements|
    //   requires SeqMatchesContents(elements, contents)
    //   requires Last(elements).Filled?
    //   requires Last(elements).key in contents
    //   ensures SeqMatchesContents(DropLast(elements), ContentsLessAKey(contents, Last(elements).key))
    // {
    // }

    // lemma NonFullStorageHasHole(elements: seq<Item<V>>, contents: map<uint64, V>) returns (hole: Slot)
    //   requires ValidElements(elements)
    //   requires |contents| < |elements|
    //   requires SeqMatchesContents(elements, contents)
    //   ensures ValidSlot(|elements| as uint64, hole)
    //   ensures elements[hole.slot].Empty?
    // {
    //   if Last(elements).Empty? {
    //     hole := Slot((|elements| - 1) as uint64);
    //   } else {
    //     var slot := Slot((|elements| - 1) as uint64);
    //     assert ValidSlot(|elements| as uint64, slot);
    //     assert Last(elements).key in contents;
    //     assert 0 < |contents|;
    //     if |elements| == 1 {
    //       assert false;
    //     } else {
    //       HoleRecursion(elements, contents);
    //       hole := NonFullStorageHasHole(DropLast(elements), ContentsLessAKey(contents, Last(elements).key));
    //     }
    //   }
    //   assert ValidSlot(|elements| as uint64, hole);
    //   assert elements[hole.slot].Empty?;
    // }
  }

  // class HashMap<V(==)> {
  //   var Storage: array<Option<(uint64, V)>>;
  //   var Count: uint64;

  //   ghost var Contents: map<uint64, V>;

  //   predicate Inv()
  //     reads this
  //     reads Storage
  //   {
  //     && StorageInv(Storage, Contents, Count)
  //   }

  //   constructor (size: uint64)
  //     requires 0 < size
  //     ensures Inv()
  //     ensures Contents == map[]
  //   {
  //     Count := 0;
  //     Storage := new [size] (_ => None);
  //     Contents := map[];

  //     new;

  //     assert forall i :: 0 <= i < Storage.Length ==> Storage[i].None?;
  //     assert forall k :: k !in Contents ==> (
  //         forall i :: 0 <= i < Storage.Length && (Storage[i].None? || Storage[i].value.0 != k));
  //     assert Count as int < Storage.Length;
  //     assert Count as int < Storage.Length ==> exists hole :: 0 <= hole < Storage.Length && Storage[hole].None?;
  //     assert StorageInv(Storage, Contents, Count);
  //   }

  //   method key_position(key: uint64) returns (result: Option<uint64>)
  //     requires Inv()
  //     ensures Inv()
  //     ensures (if key in Contents
  //       then (result.Some? && Storage[result.value].Some? && Storage[result.value].value.0 == key)
  //       else result.None?)
  //   {

  //   }



  //   // method realloc()
  //   //   requires Inv()
  //   //   requires Storage.Length < (0x10000000000000000 / 2)
  //   //   ensures Inv()
  //   //   ensures Contents == old(Contents)
  //   //   ensures Count == old(Count)
  //   //   ensures Count as int < Storage.Length
  //   //   ensures fresh(this.Storage)
  //   //   modifies this
  //   // {
  //   //   var targetSize := Storage.Length * 2;
  //   //   var newStorage := new [targetSize] (_ => None);

  //   //   var k := 0;
  //   //   while k < Storage.Length
  //   //   {
  //   //     var element := Storage[k];
  //   //     if element.Some? {
  //   //       insert_internal(newStorage, element.value);
  //   //     }
  //   //     k := k + 1;
  //   //   }

  //   //   // var k := 0;
  //   //   // while k < Length
  //   //   //   invariant Inv()
  //   //   //   invariant (k as int) <= Array.Length <= newArray.Length
  //   //   //   invariant forall i :: 0 <= i < k ==> newArray[i] == Array[i]
  //   //   //   invariant forall i :: (Length as int) <= i < newArray.Length ==> newArray[i].None?
  //   //   //   invariant Contents == old(Contents);
  //   //   //   invariant Length == old(Length)
  //   //   // {
  //   //   //   newArray[k] := Array[k];
  //   //   //   k := k + 1;
  //   //   // }

  //   //   Storage := newStorage;
  //   // }

  //   // method insert(value: V)
  //   //   requires Inv()
  //   //   requires Array.Length < (0x10000000000000000 / 2)
  //   //   ensures Inv()
  //   //   ensures Contents == old(Contents) + [value]
  //   //   ensures Length == old(Length) + 1
  //   //   modifies this.Array
  //   //   modifies this
  //   // {
  //   //   if Length as int == Array.Length {
  //   //     realloc();
  //   //   }
  //   //   Contents := Contents + [value];
  //   //   Array[Length] := Some(value);
  //   //   Length := Length + 1;
  //   // }

  //   // // Removes the element at index and moves the last element to index.
  //   // method removeSwap(index: uint64) returns (removed: V)
  //   //   requires Inv()
  //   //   requires 0 <= (index as int) < (Length as int)
  //   //   ensures Inv()
  //   //   ensures (
  //   //     if (index as int) < ((old(Length) as int) - 1) then
  //   //       Contents == old(Contents)[..(index as int)] + [old(Contents)[|old(Contents)| - 1]] + old(Contents)[(index as int)+1..|old(Contents)|-1]
  //   //     else
  //   //       Contents == old(Contents)[..(index as int)])
  //   //   ensures Length == old(Length) - 1
  //   //   ensures removed == old(Contents)[index]
  //   //   modifies this.Array
  //   //   modifies this
  //   // {
  //   //   removed := Array[index].value;

  //   //   Array[index] := Array[Length - 1];
  //   //   Array[Length - 1] := None;
  //   //   Length := Length - 1;

  //   //   if (index as int) < (old(Length) as int) - 1 {
  //   //     Contents := old(Contents)[..index] + [old(Contents)[|old(Contents)| - 1]] + old(Contents)[(index as int)+1..|old(Contents)|-1];
  //   //   } else {
  //   //     Contents := old(Contents)[..(index as int)];
  //   //   }
  //   // }

  //   // method pop() returns (removed: V)
  //   //   requires Inv()
  //   //   requires 1 < Length
  //   //   ensures Inv()
  //   //   ensures Contents == old(Contents)[..|old(Contents)|-1]
  //   //   ensures Length == old(Length) - 1
  //   //   ensures removed == old(Contents)[|old(Contents)|-1]
  //   //   modifies this.Array
  //   //   modifies this
  //   // {
  //   //   removed := Array[Length - 1].value;

  //   //   Array[Length - 1] := None;
  //   //   Length := Length - 1;

  //   //   Contents := old(Contents)[..|old(Contents)|-1];
  //   // }

  //   // method get(index: uint64) returns (result: V)
  //   //   requires Inv()
  //   //   requires 0 <= (index as int) < (Length as int)
  //   //   ensures Inv()
  //   //   ensures Contents == old(Contents)
  //   //   ensures Length == old(Length)
  //   //   ensures result == Contents[index]
  //   // {
  //   //   result := Array[index].value;
  //   // }

  //   // // FIXME
  //   // // method toSeq() returns (result: seq<V>)
  //   // //   requires Inv()
  //   // //   ensures Inv()
  //   // //   ensures Contents == old(Contents)
  //   // //   ensures Length == old(Length)
  //   // //   ensures result == Contents
  //   // // {
  //   // //   assert forall i :: 0 <= i < Length ==> Array[i].Some?;
  //   // //   // ???
  //   // //   var contents: array<V> := new [Length] (i => Array[i].value);
  //   // //   result := contents[..];

  //   // //   // FIXME result := Apply(unwrap, contents);
  //   // // }

  // }
}
