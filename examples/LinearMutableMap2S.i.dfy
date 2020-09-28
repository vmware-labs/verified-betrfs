include "LinearSequence.s.dfy"
include "LinearSequence.i.dfy"

include "../lib/Lang/NativeTypes.s.dfy"
include "../lib/Base/Option.s.dfy"
include "../lib/Base/sequences.i.dfy"
include "../lib/Base/Sets.i.dfy"
include "../lib/Base/Maps.i.dfy"
include "../lib/Base/SetBijectivity.i.dfy"
include "../lib/Lang/System/Arithmetic.s.dfy"

include "LinearFixedSizeMutableMapS.i.dfy"

// module MutableMapModel {
  linear datatype LinearHashMap<V> = LinearHashMap(
    linear underlying: FixedSizeLinearHashMap<V>,
    count: uint64,
    ghost contents: map<uint64, V>)

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
    assert MapFromStorage(underlying.storage) == contents;
  }

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

  method Constructor<V>(size: uint64) returns (linear self: LinearHashMap<V>)
  requires 128 <= size
  ensures Inv(self)
  ensures self.contents == map[]
  {
    linear var underlying := ConstructorFromSize(size);
    self := LinearHashMap(underlying, 0, map[]);

    assert forall slot :: ValidSlot(|self.underlying.storage|, slot) ==> !self.underlying.storage[slot.slot].Entry?;
    UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents);
    assert MapFromStorage(self.underlying.storage) == self.contents;
  }

  lemma LemmaEntryKeyInContents<V>(self: LinearHashMap<V>, i: uint64)
  requires Inv(self)
  requires 0 <= i as int < |self.underlying.storage|
  requires self.underlying.storage[i].Entry?
  ensures self.underlying.storage[i].key in self.contents
  {
    assert EntryInSlotMatchesContents(self.underlying.storage, Slot(i as nat), self.underlying.contents); // trigger
  }

  // TODO (chris) HALP!
  //   1. how do we throw away `selfUnderlying`?
  //   2. why is it complaining that newUnderlying must be unavailable, we are using it
  //   3. why is it complaining that the return variable must be assigned? it is!
  method Realloc<V>(linear self: LinearHashMap<V>) returns (linear self': LinearHashMap<V>)
    requires self.count as nat < 0x10000000000000000 / 8
    requires Inv(self)
  {
    linear var LinearHashMap(selfUnderlying, selfCount, selfContents) := self;

    var newSize: uint64 := (128 + selfCount) * 4;

    linear var newUnderlying := ConstructorFromSize(newSize);
    var i: uint64 := 0;

    // linear var FixedSizeLinearHashMap(
    //   selfUnderlyingStorage, selfUnderlyingCount, selfUnderlyingContents) := selfUnderlying;

    while i < seq_length(selfUnderlying.storage) as uint64
    invariant FixedSizeInv(newUnderlying);
    invariant 0 <= i as int <= |selfUnderlying.storage|
    invariant self.count as int < |newUnderlying.storage| - 1
    invariant newUnderlying.contents.Keys <= selfContents.Keys
    // invariant Inv(self')
    {
      var item := seq_get(selfUnderlying.storage, i as nat);
      if item.Entry? {
        SetInclusionImpliesSmallerCardinality(newUnderlying.contents.Keys, self.contents.Keys);
        LemmaEntryKeyInContents(self, i);

        var replaced;
        newUnderlying, replaced := FixedSizeInsert(newUnderlying, item.key, item.value);
      }
      i := i + 1;
    }

    self' := LinearHashMap(newUnderlying, selfCount, selfContents);

    linear var FixedSizeLinearHashMap(storage, _, _) := selfUnderlying;
    var _ := seq_free(storage);
  }
// 
//   function {:opaque} ReallocInternal<V>(self: LinearHashMap<V>) : (self' : LinearHashMap<V>)
//     requires self.count as nat < 0x1_0000_0000_0000_0000 / 8
//     requires Inv(self)
//   {
//     var newSize: uint64 := (128 + self.count) * 4;
//     var newUnderlying := ReallocIterate(self, ConstructorFromSize(newSize), 0);
//     self.(underlying := newUnderlying)
//   }
// 
//   function Realloc<V>(self: LinearHashMap<V>) : (self': LinearHashMap<V>)
//     requires self.count as nat < 0x1_0000_0000_0000_0000 / 8
//     requires Inv(self)
//     ensures Inv(self')
//     ensures self'.contents == self.contents
//     ensures self'.underlying.count as nat < |self'.underlying.storage| - 2
//   {
//     var self' := ReallocInternal(self);
//     LemmaReallocResult(self);
//     self'
//   }
// 
//   lemma LemmaReallocIterateResult<V>(self: LinearHashMap<V>, newUnderlying: FixedSizeLinearHashMap<V>, i: uint64, transferredContents: map<uint64, V>,
//       newSize: uint64)
//     requires Inv(self)
//     requires FixedSizeInv(newUnderlying);
//     requires 0 <= i as int <= |self.underlying.storage|
//     requires self.count as int < |newUnderlying.storage| - 1
//     requires self.count as nat < 0x1_0000_0000_0000_0000 / 8
//     requires newUnderlying.contents.Keys <= self.contents.Keys
//     requires |newUnderlying.storage| == newSize as nat
//     requires newSize == (128 + self.count) * 4
// 
//     requires |self.contents| == self.count as nat
//     requires UnderlyingContentsMatchesContents(newUnderlying, transferredContents)
//     requires MapFromStorage(self.underlying.storage[..i]) == transferredContents
//     requires MapFromStorage(self.underlying.storage) == self.contents
// 
//     requires newUnderlying.count as nat <= i as nat
//     requires FixedSizeInv(self.underlying)
// 
//     requires |transferredContents| == newUnderlying.count as nat
//     requires transferredContents.Keys <= self.contents.Keys
//     requires forall key :: key in newUnderlying.contents ==> exists slot: Slot :: (
//         && slot.slot < i as int
//         && ValidSlot(|self.underlying.storage|, slot)
//         && FilledWithEntryKey(self.underlying.storage, slot, key))
// 
//     ensures var newUnderlying' := ReallocIterate(self, newUnderlying, i);
//       && FixedSizeInv(newUnderlying')
//       && newUnderlying'.count == self.count
//       && UnderlyingInv(self.(underlying := newUnderlying'), newUnderlying')
//       && newUnderlying'.count as nat < |newUnderlying'.storage| - 2
// 
//     decreases |self.underlying.storage| - i as int
//   {
//     if i as int == |self.underlying.storage| {
//       assert i as nat == |self.underlying.storage|;
//       assert self.underlying.storage[..i] == self.underlying.storage;
// 
//       assert MapFromStorage(self.underlying.storage) == transferredContents;
//       UnderlyingInvImpliesMapFromStorageMatchesContents(newUnderlying, transferredContents);
//       assert transferredContents == self.contents;
// 
//       assert |self.contents| == self.count as nat;
// 
//       assert forall key :: key in self.contents ==> key in newUnderlying.contents && newUnderlying.contents[key] == Some(self.contents[key]);
//       assert forall key :: key !in self.contents ==> key !in newUnderlying.contents || newUnderlying.contents[key].None?;
// 
//       var self' := self.(underlying := newUnderlying);
// 
//       assert FixedSizeInv(newUnderlying);
//       assert UnderlyingInv(self', newUnderlying);
//       assert UnderlyingContentsMatchesContents(newUnderlying, self.contents);
//       assert MapFromStorage(newUnderlying.storage) == self.contents;
//       assert newUnderlying.count as nat < |newUnderlying.storage| - 2;
// 
//       assert self'.underlying.count as nat < |self'.underlying.storage| - 2;
//       assert self'.contents == self.contents;
//       assert self'.count == self.count;
//       assert self'.count <= self'.underlying.count;
//       assert Inv(self');
// 
//       return;
//     }
// 
//     var item := self.underlying.storage[i];
//     assert self.underlying.storage[..i+1] == self.underlying.storage[..i] + [self.underlying.storage[i]];
// 
//     var newUnderlying';
//     var transferredContents';
// 
//     if item.Entry? {
//       assert MapFromStorage(self.underlying.storage[..i]) == transferredContents;
//       assert |transferredContents| == newUnderlying.count as nat;
// 
//       if item.key in newUnderlying.contents {
//         var j:uint64 :| (
//             && 0 <= j < i
//             && ValidSlot(|self.underlying.storage|, Slot(j as int))
//             && self.underlying.storage[Slot(j as int).slot].Entry?
//             && self.underlying.storage[Slot(j as int).slot].key == item.key);
//         assert ValidSlot(|self.underlying.storage|, Slot(i as nat));
//         assert i != j;
//         assert Slot(i as nat) != Slot(j as nat);
//         assert self.underlying.storage[Slot(j as nat).slot].key == self.underlying.storage[Slot(i as nat).slot].key;
//         CantEquivocateMapFromStorageKey(self.underlying);
//         assert false;
//       }
//       assert item.key !in newUnderlying.contents;
// 
//       assert transferredContents.Keys <= self.contents.Keys;
//       SetInclusionImpliesSmallerCardinality(transferredContents.Keys, self.contents.Keys);
//       assert |transferredContents.Keys| <= |self.contents.Keys|;
//       assert |transferredContents.Keys| == |transferredContents|;
//       assert |self.contents.Keys| == |self.contents|;
//       assert |transferredContents| <= |self.contents|;
//       assert newUnderlying.count as nat < |newUnderlying.storage| - 1;
// 
//       LemmaFixedSizeInsertResult(newUnderlying, item.key, item.value);
// 
//       // -- mutation --
//       newUnderlying' := FixedSizeInsert(newUnderlying, item.key, item.value).0;
//       transferredContents' := transferredContents[item.key := item.value];
//       // --------------
// 
//       forall key | key in newUnderlying'.contents
//       ensures exists slot: Slot :: (
//           && slot.slot < i as nat + 1
//           && ValidSlot(|self.underlying.storage|, slot)
//           && self.underlying.storage[slot.slot].Entry?
//           && self.underlying.storage[slot.slot].key == key)
//       {
//         if key == item.key {
//           assert ValidSlot(|self.underlying.storage|, Slot(i as nat));
//           assert exists slot: Slot :: (
//               && slot.slot < i as nat + 1
//               && ValidSlot(|self.underlying.storage|, slot)
//               && self.underlying.storage[slot.slot].Entry?
//               && self.underlying.storage[slot.slot].key == key);
//         } else {
//           assert exists slot: Slot :: (
//               && slot.slot < i as nat + 1
//               && ValidSlot(|self.underlying.storage|, slot)
//               && self.underlying.storage[slot.slot].Entry?
//               && self.underlying.storage[slot.slot].key == key);
//         }
//       }
//       assert |transferredContents'| == newUnderlying'.count as nat;
//       assert MapFromStorage(self.underlying.storage[..i+1]) == transferredContents';
//     } else {
//       newUnderlying' := newUnderlying;
//       transferredContents' := transferredContents;
// 
//       assert forall key :: key in newUnderlying.contents ==> exists slot: Slot :: (
//           && slot.slot < i as nat
//           && ValidSlot(|self.underlying.storage|, slot)
//           && self.underlying.storage[slot.slot].Entry?
//           && self.underlying.storage[slot.slot].key == key);
//       assert |transferredContents'| <= newUnderlying.count as nat;
//       assert MapFromStorage(self.underlying.storage[..i+1]) == transferredContents';
//     }
// 
//     assert MapFromStorage(self.underlying.storage[..i+1]) == transferredContents';
// 
//     LemmaReallocIterateResult(self, newUnderlying', i+1, transferredContents', newSize);
//   }
// 
// 
//   lemma LemmaReallocResult(self: LinearHashMap)
//     requires self.count as nat < 0x1_0000_0000_0000_0000 / 8
//     requires Inv(self)
//     ensures var self' := ReallocInternal(self);
//       && Inv(self')
//       && self'.contents == self.contents
//       && self'.underlying.count as nat < |self'.underlying.storage| - 2
//   {
//     var self' := ReallocInternal(self);
//     reveal_ReallocInternal();
// 
//     assert |self.contents| == self.count as nat;
// 
//     var newSize: uint64 := (128 + self.count) * 4;
//     //print "(debug) MutableMap.ReallocInternal: Count ", Count, ", ReallocInternal ", newSize, "\n";
// 
//     var newUnderlying := ConstructorFromSize(newSize);
//     
//     assert |newUnderlying.storage| == newSize as nat;
// 
//     assert MapFromStorage(self.underlying.storage) == self.contents;
//     UnderlyingInvImpliesMapFromStorageMatchesContents(newUnderlying, map[]);
//     assert MapFromStorage(newUnderlying.storage) == map[];
// 
//     LemmaReallocIterateResult(self, newUnderlying, 0, map[], newSize);
// 
//     var newUnderlying' := ReallocIterate(self, newUnderlying, 0);
//     
//     assert self' == self.(underlying := newUnderlying');
// 
//     assert FixedSizeInv(newUnderlying');
//     assert UnderlyingInv(self', newUnderlying');
//     assert UnderlyingContentsMatchesContents(newUnderlying', self.contents);
//     assert MapFromStorage(newUnderlying'.storage) == self.contents;
//     assert newUnderlying'.count as nat < |newUnderlying'.storage| - 2;
// 
//     assert self'.underlying.count as nat < |self'.underlying.storage| - 2;
//     assert self'.contents == self.contents;
//     assert self'.count == self.count;
//     assert self'.count <= self'.underlying.count;
//     assert Inv(self');
//   }
// 
//   function {:opaque} InsertAndGetOld<V>(self: LinearHashMap, key: uint64, value: V)
//   : (res: (LinearHashMap, Option<V>))
//     requires Inv(self)
//     requires self.count as nat < 0x1_0000_0000_0000_0000 / 8
//     ensures var (self', replaced) := res;
//       && Inv(self')
//       && self'.contents == self.contents[key := value]
//       && self'.count as nat == self.count as nat + (if replaced.Some? then 0 else 1)
//       && (replaced.Some? ==> MapsTo(self.contents, key, replaced.value))
//       && (replaced.None? ==> key !in self.contents)
//   {
//     // -- mutation --
//     var self1 := if |self.underlying.storage| as uint64 / 2 <= self.underlying.count then (
//       Realloc(self)
//     ) else (
//       self
//     );
//     // --------------
// 
//     //assert MapFromStorage(self1.underlying.storage) == self1.contents;
//     //assert self1.underlying.count as nat < |self1.underlying.storage| - 2;
// 
//     // -- mutation --
//     var (underlying', replaced) := FixedSizeInsert(self1.underlying, key, value);
//     var self' := self1
//         .(underlying := underlying')
//         .(contents := self1.contents[key := value])
//         .(count := if replaced.None? then self1.count + 1 else self1.count);
//     // --------------
// 
//     LemmaFixedSizeInsertResult(self1.underlying, key, value);
// 
//     //assert replaced.None? ==> key !in self.contents;
//     //assert !replaced.None? ==> key in self'.contents;
// 
//     //assert self'.underlying.count as nat < |self'.underlying.storage| - 1;
// 
//     UnderlyingInvImpliesMapFromStorageMatchesContents(self'.underlying, self'.contents);
//     //assert MapFromStorage(self'.underlying.storage[..]) == self'.contents;
//     //assert UnderlyingInv(self', self'.underlying);
//     //assert Inv(self');
// 
//     (self', replaced)
//   }
// 
//   function {:opaque} Insert<V>(self: LinearHashMap, key: uint64, value: V)
//   : (self': LinearHashMap)
//     requires Inv(self)
//     requires self.count as nat < 0x1_0000_0000_0000_0000 / 8
//     ensures
//       && Inv(self')
//       && self'.contents == self.contents[key := value]
//       && (self'.count as nat == self.count as nat ||
//          self'.count as nat == self.count as nat + 1)
//   {
//     InsertAndGetOld(self, key, value).0
//   }
// 
//   function RemoveInternal<V>(self: LinearHashMap, key: uint64)
//   : (res: (LinearHashMap, Option<V>))
//     requires Inv(self)
//     ensures var (self', removed) := res;
//       && (self'.underlying, removed) == FixedSizeRemove(self.underlying, key)
//       && FixedSizeInv(self'.underlying)
//       && (self'.underlying.contents == if key in self.underlying.contents
//         then self.underlying.contents[key := None]
//         else self.underlying.contents)
//       && (removed == if key in self.underlying.contents && self.underlying.contents[key].Some?
//         then Some(self.underlying.contents[key].value)
//         else None)
//       && (self'.underlying.count == self.underlying.count)
//   {
//     // -- mutation --
//     var (underlying', removed) := FixedSizeRemove(self.underlying, key);
//     // --------------
// 
//     LemmaFixedSizeRemoveResult(self.underlying, key);
// 
//     var self' := self
//       .(underlying := underlying')
//       .(contents := map k | k in self.contents && k != key :: self.contents[k])
//       .(count := if removed.Some? then self.count - 1 else self.count);
// 
//     (self', removed)
//   }
// 
//   lemma RemoveCountCorrect<V>(self: LinearHashMap, key: uint64, res: (LinearHashMap, Option<V>))
//   requires Inv(self)
//   requires res == RemoveInternal(self, key)
//   ensures var (self', removed) := res;
//     self'.count as nat == |self'.contents|
//   {
//     var (self', removed) := res;
//     if removed.Some? {
//       assert key in self.contents;
//       assert self'.contents.Keys <= self.contents.Keys;
//       assert |self.contents| == self'.count as nat + 1;
//       assert |self.contents.Keys| == self'.count as nat + 1;
//       assert |self.contents.Keys - {key}| == |self.contents.Keys| - |{key}|;
//       assert self.contents.Keys - {key} == self'.contents.Keys;
//       assert |self'.contents| == |self.contents| - 1;
//       assert |self'.contents| == self'.count as nat;
//     } else {
//       assert key !in self.contents;
//       assert self'.contents == self.contents;
//       assert |self'.contents| == self'.count as nat;
//     }
//   }
// 
//   function RemoveAndGet<V>(self: LinearHashMap, key: uint64)
//   : (res: (LinearHashMap, Option<V>))
//     requires Inv(self)
//     ensures var (self', removed) := res;
//       && Inv(self')
//       && (self'.contents == if key in self.contents
//         then map k | k in self.contents && k != key :: self.contents[k]
//         else self.contents)
//       && (removed == if key in self.contents
//         then Some(self.contents[key])
//         else None)
//   {
//     var (self', removed) := RemoveInternal(self, key);
// 
//     LemmaFixedSizeRemoveResult(self.underlying, key);
//     RemoveCountCorrect(self, key, (self', removed));
//     UnderlyingInvImpliesMapFromStorageMatchesContents(self'.underlying, self'.contents); 
// 
//     (self', removed)
//   }
// 
//   function Remove<V>(self: LinearHashMap, key: uint64)
//   : (self': LinearHashMap)
//     requires Inv(self)
//     ensures
//       && Inv(self')
//       && (self'.contents == if key in self.contents
//         then map k | k in self.contents && k != key :: self.contents[k]
//         else self.contents)
//   {
//     RemoveAndGet(self, key).0
//   }
// 
//   function Get<V>(self: LinearHashMap, key: uint64)
//   : (found: Option<V>)
//     requires Inv(self)
//     ensures if key in self.contents then found == Some(self.contents[key]) else found.None?
//     ensures found.Some? <==> key in self.contents
//   {
//     var found := FixedSizeGet(self.underlying, key);
//     LemmaFixedSizeGetResult(self.underlying, key);
//     found
//   }
// 
//   //////// Iterator
// 
//   // We have two types of iterators.
//   //
//   // Iterator is usually more convenient as it has the IteratorOutput
//   // built-in.
//   //
//   // SimpleIterator doesn't (you have to call SimpleIteratorOutput)
//   // but has the advantage that the WFSimpleIter condition doesn't
//   // depend on the key/value being correct. Thus the well-formedness
//   // of a SimpleIterator can be preserved across (some) modifications
//   // of the hash map.
//   //
//   // TODO fix the duplicated code that results.
// 
//   datatype IteratorOutput<V> = Next(key: uint64, value: V) | Done
// 
//   datatype Iterator<V> = Iterator(
//     i: uint64, // index in hash table item list
//     ghost s: set<uint64>,   // set of values returned so far
//     ghost decreaser: ORDINAL,
//     next: IteratorOutput)
// 
//   datatype SimpleIterator = SimpleIterator(
//     i: uint64, // index in hash table item list
//     ghost s: set<uint64>,   // set of values returned so far
//     ghost decreaser: ORDINAL)
// 
//   predicate NextExplainedByI<V>(self: LinearHashMap<V>, i : uint64, output:IteratorOutput)
//   {
//     && (output.Next? ==>
//       && i as int < |self.underlying.storage|
//       && self.underlying.storage[i].Entry?
//       && self.underlying.storage[i].key == output.key
//       && self.underlying.storage[i].value == output.value)
//     && (output.Done? ==> i as int == |self.underlying.storage|)
//   }
// 
//   predicate ValidI<V>(self: LinearHashMap<V>, it: Iterator<V>)
//   {
//     && 0 <= it.i as int <= |self.underlying.storage|
//   }
// 
//   predicate EachReturnedKeyExplainedByPassedIndex<V>(self: LinearHashMap<V>, s: set<uint64>, i: uint64)
//   requires 0 <= i as int <= |self.underlying.storage|
//   {
//     forall key | key in s ::
//         exists j | 0 <= j < i as int ::
//         && self.underlying.storage[j].Entry?
//         && key == self.underlying.storage[j].key
//   }
// 
//   protected predicate WFIter<V>(self: LinearHashMap<V>, it: Iterator<V>)
//   ensures WFIter(self, it) ==> (it.next.Done? ==> it.s == self.contents.Keys)
//   ensures WFIter(self, it) ==> (it.next.Next? ==>
//       MapsTo(self.contents, it.next.key, it.next.value));
//   ensures WFIter(self, it) ==> (it.next.Next? ==> it.next.key !in it.s)
//   ensures WFIter(self, it) ==> it.s <= self.contents.Keys
//   {
//     && ValidI(self, it)
//     && NextExplainedByI(self, it.i, it.next)
//     // Done justified by exhausting i
//     && (it.next.Done? ==> (it.s == self.contents.Keys))
//     // Each passed index appears in s
//     && (forall j | 0 <= j < it.i as int ::
//         self.underlying.storage[j].Entry? ==> self.underlying.storage[j].key in it.s)
//     && EachReturnedKeyExplainedByPassedIndex(self, it.s, it.i)
//     && it.decreaser == (|self.underlying.storage| - it.i as int) as ORDINAL
//     && (it.next.Next? ==> MapsTo(self.contents, it.next.key, it.next.value))
//     && (it.next.Next? ==> it.next.key !in it.s)
//     && it.s <= self.contents.Keys
//   }
// 
//   protected predicate WFSimpleIter<V>(self: LinearHashMap<V>, it: SimpleIterator)
//   ensures WFSimpleIter(self, it) ==> it.s <= self.contents.Keys
//   {
//     && 0 <= it.i as int <= |self.underlying.storage|
//     && (it.i as int == |self.underlying.storage| ==> (it.s == self.contents.Keys))
//     && (it.i as int < |self.underlying.storage| ==> self.underlying.storage[it.i].Entry?)
//     // Each passed index appears in s
//     && (forall j | 0 <= j < it.i as int ::
//         self.underlying.storage[j].Entry? ==> self.underlying.storage[j].key in it.s)
//     && EachReturnedKeyExplainedByPassedIndex(self, it.s, it.i)
//     && it.decreaser == (|self.underlying.storage| - it.i as int) as ORDINAL
//     && (it.i as int < |self.underlying.storage| ==> (
//       && MapsTo(self.contents, self.underlying.storage[it.i].key, self.underlying.storage[it.i].value)
//       && self.underlying.storage[it.i].key !in it.s
//     ))
//     && it.s <= self.contents.Keys
//   }
// 
//   function indexOutput<V>(self: LinearHashMap<V>, i: uint64) : (next: IteratorOutput<V>)
//   requires 0 <= i as int <= |self.underlying.storage|
//   requires i as int < |self.underlying.storage| ==> self.underlying.storage[i].Entry?
//   {
//     if i as int == |self.underlying.storage| then (
//       Done
//     ) else (
//       Next(
//         self.underlying.storage[i].key,
//         self.underlying.storage[i].value)
//     )
//   }
// 
//   protected function SimpleIterOutput<V>(self: LinearHashMap<V>, it: SimpleIterator) : (next: IteratorOutput<V>)
//   requires WFSimpleIter(self, it)
//   ensures (next.Done? ==> it.s == self.contents.Keys)
//   ensures (next.Next? ==>
//       MapsTo(self.contents, next.key, next.value));
//   ensures (next.Next? ==> next.key !in it.s)
//   {
//     indexOutput(self, it.i)
//   }
// 
//   lemma LemmaWFIterImpliesILt<V>(self: LinearHashMap<V>, it: Iterator<V>)
//   requires WFIter(self, it)
//   ensures it.next.Next? ==> it.i as int < |self.underlying.storage|
//   {
//   }
// 
//   lemma LemmaWFSimpleIterImpliesEntry<V>(self: LinearHashMap<V>, it: SimpleIterator)
//   requires WFSimpleIter(self, it)
//   ensures
//     && 0 <= it.i as int <= |self.underlying.storage|
//     && (SimpleIterOutput(self, it).Next? ==> it.i as int < |self.underlying.storage|)
//     && (it.i as int < |self.underlying.storage| ==>
//       && self.underlying.storage[it.i].Entry?
//     )
//   {
//   }
// 
//   lemma LemmaIterNextNotInS<V>(self: LinearHashMap<V>, it: Iterator<V>)
//   requires 0 <= it.i as int <= |self.underlying.storage|
//   requires ValidElements(self.underlying.storage)
//   requires CantEquivocateStorageKey(self.underlying.storage)
//   requires NextExplainedByI(self, it.i, it.next)
//   requires EachReturnedKeyExplainedByPassedIndex(self, it.s, it.i)
//   ensures (it.next.Next? ==> it.next.key !in it.s)
//   {
//     if it.next.Next? {
//       if it.next.key in it.s {
//         var j :| 0 <= j < it.i as int
//           && self.underlying.storage[j].Entry?
//           && it.next.key == self.underlying.storage[j].key;
//         assert TwoNonEmptyValidSlotsWithSameKey<V>(self.underlying.storage, Slot(it.i as int), Slot(j));  // trigger
//         // assert false; // proof by contradiction
//       }
//     }
//   }
// 
//   function iterToNext<V>(self: LinearHashMap<V>, i: uint64) : (res: (uint64, IteratorOutput))
//   requires Inv(self)
//   requires 0 <= i as int <= |self.underlying.storage|
//   ensures NextExplainedByI(self, res.0, res.1)
//   ensures forall j | i <= j < res.0 :: !self.underlying.storage[j].Entry?
//   ensures i <= res.0
//   decreases |self.underlying.storage| - i as int
//   {
//     if i as int == |self.underlying.storage| then (
//       (i, Done)
//     ) else if self.underlying.storage[i].Entry? then (
//       (i, Next(self.underlying.storage[i].key, self.underlying.storage[i].value))
//     ) else (
//       iterToNext(self, i+1)
//     )
//   }
// 
//   function simpleIterToNext<V>(self: LinearHashMap<V>, i: uint64) : (i': uint64)
//   requires Inv(self)
//   requires 0 <= i as int <= |self.underlying.storage|
//   ensures 0 <= i' as int <= |self.underlying.storage|
//   ensures forall j | i <= j < i' :: !self.underlying.storage[j].Entry?
//   ensures i' as int < |self.underlying.storage| ==>
//       self.underlying.storage[i'].Entry?
//   ensures i <= i'
//   decreases |self.underlying.storage| - i as int
//   {
//     if i as int == |self.underlying.storage| then (
//       i
//     ) else if self.underlying.storage[i].Entry? then (
//       i
//     ) else (
//       simpleIterToNext(self, i+1)
//     )
//   }
// 
//   lemma lemmaIterToNextValidKeyValuePair<V>(self: LinearHashMap<V>, i: uint64)
//   requires Inv(self)
//   requires 0 <= i as int <= |self.underlying.storage|
//   ensures iterToNext(self, i).1.Next? ==>
//       MapsTo(self.contents, 
//           iterToNext(self, i).1.key,
//           iterToNext(self, i).1.value)
//   {
//     var j := iterToNext(self, i).0;
//     var next := iterToNext(self, i).1;
//     if next.Next? {
//       UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents);
//       CantEquivocateMapFromStorageKey(self.underlying);
//       MapFromStorageProperties(self.underlying.storage, self.contents);
//       assert self.underlying.storage[Slot(j as int).slot].value == next.value; // trigger
//     }
//   }
// 
//   function {:opaque} IterStart<V>(self: LinearHashMap<V>) : (it' : Iterator<V>)
//   requires Inv(self)
//   ensures WFIter(self, it')
//   ensures it'.s == {}
//   {
//     lemmaIterToNextValidKeyValuePair(self, 0);
// 
//     var (i, next) := iterToNext(self, 0);
//     var it' := Iterator(i, {}, (|self.underlying.storage| - i as int) as ORDINAL, next);
// 
//     LemmaIterNextNotInS(self, it');
// 
//     it'
//   }
// 
//   function {:opaque} SimpleIterStart<V>(self: LinearHashMap<V>) : (it' : SimpleIterator)
//   requires Inv(self)
//   ensures WFSimpleIter(self, it')
//   ensures it'.s == {}
//   {
//     lemmaIterToNextValidKeyValuePair(self, 0);
// 
//     var i := simpleIterToNext(self, 0);
//     var it' := SimpleIterator(i, {}, (|self.underlying.storage| - i as int) as ORDINAL);
// 
//     LemmaIterNextNotInS(self,
//       Iterator(it'.i, it'.s, it'.decreaser, indexOutput(self, it'.i)));
// 
//     it'
//   }
// 
//   function {:opaque} IterInc<V>(self: LinearHashMap<V>, it: Iterator) : (it' : Iterator)
//   requires Inv(self)
//   requires WFIter(self, it)
//   requires it.next.Next?
//   ensures WFIter(self, it')
//   ensures it'.s == it.s + {it.next.key}
//   ensures it'.next.Done? ==> it'.s == self.contents.Keys
//   ensures it'.decreaser < it.decreaser
//   {
//     lemmaIterToNextValidKeyValuePair(self, it.i + 1);
// 
//     var (i, next) := iterToNext(self, it.i + 1);
//     var it' := Iterator(i, it.s + {it.next.key}, (|self.underlying.storage| - i as int) as ORDINAL, next);
// 
//     assert (forall key | key in it'.s ::
//         exists j | 0 <= j < it'.i as int ::
//         && self.underlying.storage[j].Entry?
//         && key == self.underlying.storage[j].key);
//     assert (it'.next.Done? ==> it'.s == self.contents.Keys);
// 
//     LemmaIterNextNotInS(self, it');
// 
//     it'
//   }
// 
//   function {:opaque} SimpleIterInc<V>(self: LinearHashMap<V>, it: SimpleIterator) : (it' : SimpleIterator)
//   requires Inv(self)
//   requires WFSimpleIter(self, it)
//   requires SimpleIterOutput(self, it).Next?
//   ensures WFSimpleIter(self, it')
//   ensures it'.s == it.s + {SimpleIterOutput(self, it).key}
//   ensures it'.decreaser < it.decreaser
//   {
//     lemmaIterToNextValidKeyValuePair(self, it.i + 1);
// 
//     var i := simpleIterToNext(self, it.i + 1);
//     var it' := SimpleIterator(i, it.s + {SimpleIterOutput(self, it).key}, (|self.underlying.storage| - i as int) as ORDINAL);
// 
//     assert (forall key | key in it'.s ::
//         exists j | 0 <= j < it'.i as int ::
//         && self.underlying.storage[j].Entry?
//         && key == self.underlying.storage[j].key);
// 
//     LemmaIterNextNotInS(self,
//       Iterator(it'.i, it'.s, it'.decreaser, indexOutput(self, it'.i)));
// 
//     it'
//   }
// 
//   lemma LemmaIterIndexLtCount<V>(self: LinearHashMap<V>, it: Iterator<V>)
//   requires Inv(self)
//   requires WFIter(self, it)
//   ensures it.next.Next? ==> |it.s| < self.count as int
//   {
//     if it.next.Next? {
//       ProperSubsetImpliesSmallerCardinality(it.s, self.contents.Keys);
//     }
//   }
// 
//   function MaxKeyIterate<V>(self: LinearHashMap<V>, it: Iterator<V>, m: uint64) : (res : uint64)
//   requires Inv(self)
//   requires WFIter(self, it)
//   requires forall key | key in it.s :: key <= m
//   ensures forall key | key in self.contents :: key <= res
//   decreases it.decreaser
//   {
//     if it.next.Done? then (
//       m
//     ) else (
//       var key := it.next.key;
//       MaxKeyIterate(self, IterInc(self, it), if m < key then key else m)
//     )
//   }
// 
//   function {:opaque} MaxKey<V>(self: LinearHashMap<V>) : (res : uint64)
//   requires Inv(self)
//   ensures forall key | key in self.contents :: key <= res
//   {
//     MaxKeyIterate(self, IterStart(self), 0)    
//   }
// 
//   function {:opaque} UpdateByIter<V>(self: LinearHashMap<V>, it: SimpleIterator, value: V)
//     : (self': LinearHashMap)
//   requires Inv(self)
//   requires WFSimpleIter(self, it)
//   requires SimpleIterOutput(self, it).Next?
//   ensures Inv(self')
//   ensures self'.contents == self.contents[SimpleIterOutput(self, it).key := value]
//   ensures self'.count == self.count
//   {
//     assume false;
//     var underlying := FixedSizeUpdateBySlot(self.underlying, it.i, value);
//     LinearHashMap(underlying, self.count,
//         self.contents[SimpleIterOutput(self, it).key := value])
//   }
// 
//   lemma UpdatePreservesSimpleIter<V>(
//     self: LinearHashMap<V>, it: SimpleIterator, value: V,
//     preserved: SimpleIterator)
//   requires UpdateByIter.requires(self, it, value)
//   requires WFSimpleIter(self, preserved)
//   ensures WFSimpleIter(UpdateByIter(self, it, value), preserved)
//   {
//     assume false;
//   }
// 
//   function {:opaque} FindSimpleIter<V>(self: LinearHashMap<V>, key: uint64)
//     : (it : SimpleIterator)
//   requires Inv(self)
//   ensures WFSimpleIter(self, it)
//   ensures key in self.contents ==> SimpleIterOutput(self, it) == Next(key, self.contents[key])
//   ensures key !in self.contents ==> SimpleIterOutput(self, it) == Done
//   {
//     assume false;
//     var i := Probe(self.underlying, key);
//     if self.underlying.storage[i].Entry? then (
//       // TODO the ghosty {} is wrong
//       SimpleIterator(i, {}, (|self.underlying.storage| - i as int) as ORDINAL)
//     ) else (
//       SimpleIterator(|self.underlying.storage| as uint64, self.contents.Keys, 0)
//     )
//   }
// } // module
