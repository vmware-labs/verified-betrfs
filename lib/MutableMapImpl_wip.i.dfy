include "NativeTypes.s.dfy"
include "Option.s.dfy"
include "sequences.s.dfy"
include "Sets.i.dfy"
include "SetBijectivity.i.dfy"
include "Marshalling/Native.s.dfy"
include "MutableMapModel.i.dfy"

module MutableMap {
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened Sets
  import opened SetBijectivity
  import Native
  import opened MutableMapModel

  class FixedSizeHashMap<V> {
    var Storage: array<Item<V>>;
    var Count: uint64;

    ghost var Contents: map<uint64, Option<V>>;
    ghost var Repr: set<object>;

    predicate WF()
    reads this
    {
      && Repr == { this, this.Storage }
    }

    protected static function ModelI(self: FixedSizeHashMap<V>): (model: FixedSizeLinearHashMap<V>)
    requires self.WF()
    ensures model.contents == self.Contents
    reads self, self.Repr
    {
      FixedSizeLinearHashMap(
        self.Storage[..],
        self.Count,
        self.Contents)
    }

    protected predicate Inv()
    requires WF()
    reads this, this.Repr
    {
      && FixedSizeInv(ModelI(this))
    }

    constructor (size: uint64)
    requires 128 <= size
    ensures WF()
    ensures ModelI(this) == ConstructorFromSize(size)
    ensures Inv()
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
    ensures WF()
    ensures ModelI(this) == ConstructorFromStorage(storage[..], count)
    ensures Storage == storage
    ensures Count == count
    ensures fresh(this)
    {
      Count := count;
      Storage := storage;
      Contents := map[];
      Repr := { this, Storage };
    }

    method Uint64SlotForKey(key: uint64) returns (result: uint64)
    requires WF()
    requires Inv()
    requires 0 < this.Storage.Length < 0x1_0000_0000_0000_0000
    ensures result == MutableMapModel.Uint64SlotForKey(ModelI(this), key)
    {
      result := key % (Storage.Length as uint64);
    }

    method Uint64SlotSuccessor(slot: uint64) returns (nextSlot: uint64)
    requires WF()
    requires Inv()
    requires this.Storage.Length < 0x1_0000_0000_0000_0000
    requires ValidSlot(this.Storage.Length, Slot(slot as nat))
    ensures nextSlot == MutableMapModel.Uint64SlotSuccessor(|ModelI(this).storage|, slot)
    {
      if slot == (this.Storage.Length as uint64) - 1 {
        return 0;
      } else {
        return slot + 1;
      }
    }

    method Probe(key: uint64) returns (slotIdx: uint64)
    requires WF()
    requires Inv()
    requires Count as int < Storage.Length
    ensures slotIdx == MutableMapModel.Probe(ModelI(this), key)
    ensures Repr == old(Repr)
    {
      reveal_Probe();

      slotIdx := Uint64SlotForKey(key);

      while true
        invariant 0 <= slotIdx as int < |ModelI(this).storage|
        invariant MutableMapModel.Probe(ModelI(this), key) == ProbeIterate(ModelI(this), key, slotIdx)
        decreases var wit := getEmptyWitness(ModelI(this), 0);
          if slotIdx > wit
            then wit as int - slotIdx as int + |ModelI(this).storage|
            else wit as int - slotIdx as int
      {
        if Storage[slotIdx].Empty? || (Storage[slotIdx].Tombstone? && Storage[slotIdx].key == key) {
          return;
        } else if Storage[slotIdx].key == key {
          return;
        }
        slotIdx := Uint64SlotSuccessor(slotIdx);
      }
    }

    method Insert(key: uint64, value: V) returns (replaced : Option<V>)
    requires WF()
    requires Inv()
    requires Count as nat < Storage.Length - 1
    ensures WF()
    ensures Inv()
    ensures (ModelI(this), replaced) ==
        MutableMapModel.FixedSizeInsert(old(ModelI(this)), key, value)
    ensures forall r :: r in Repr ==> r in old(Repr) || fresh(r)
    modifies Repr
    {
      MutableMapModel.reveal_FixedSizeInsert();
      MutableMapModel.LemmaFixedSizeInsertResult(ModelI(this), key, value);

      var slotIdx := Probe(key);

      if Storage[slotIdx].Empty? {
        this.Count := this.Count + 1;
        replaced := None;
      } else if Storage[slotIdx].Tombstone? {
        replaced := None;
      } else {
        replaced := Some(Storage[slotIdx].value);
      }
      this.Storage[slotIdx as int] := Entry(key, value);

      // ghost:
      this.Contents := Contents[key := Some(value)];
    }

    // TODO rename to GetOpt
    method Get(key: uint64) returns (found: Option<V>)
    requires WF()
    requires Inv()
    ensures found == FixedSizeGet(ModelI(this), key)
    {
      MutableMapModel.reveal_FixedSizeGet();

      var slotIdx := Probe(key);

      if Storage[slotIdx].Entry? {
        found := Some(Storage[slotIdx].value);
      } else {
        found := None;
      }
    }

    method Remove(key: uint64) returns (removed: Option<V>)
    requires WF()
    requires Inv()
    ensures WF()
    ensures Inv()
    ensures (ModelI(this), removed) == FixedSizeRemove(old(ModelI(this)), key)
    ensures Count == old(Count)
    ensures Repr == old(Repr)
    modifies Repr
    {
      MutableMapModel.reveal_FixedSizeRemove();
      MutableMapModel.LemmaFixedSizeRemoveResult(ModelI(this), key);

      var slotIdx := Probe(key);

      if Storage[slotIdx].Entry? {
        removed := Some(Storage[slotIdx].value);
        Storage[slotIdx] := Tombstone(key);
        // ghost:
        Contents := Contents[key := None];
      } else {
        removed := None;
      }
    }

    method Clone() returns (cloned: FixedSizeHashMap<V>)
      requires WF()
      requires Inv()
      ensures cloned.WF()
      ensures cloned.Inv()
      ensures cloned.Contents == old(Contents)
      ensures cloned.Count == old(Count)
      ensures cloned.Storage[..] == Storage[..]
      ensures fresh(cloned.Repr)
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

    predicate ReprInv()
      reads this, this.Repr
    {
      && { this, this.Underlying } <= Repr
      && { this, this.Underlying } + this.Underlying.Repr == Repr
      && this.Underlying.Repr == { this.Underlying, this.Underlying.Storage }
    }

    protected predicate Inv()
      ensures Inv() ==> this in this.Repr
      ensures Inv() ==> |Contents| == Count as nat
      reads this, this.Repr
    {
      && ReprInv()

      && Underlying.WF()
      && Underlying.Inv()
      && MutableMapModel.Inv(MutableMapModel.LinearHashMap(
          FixedSizeHashMap.ModelI(Underlying), Count, Contents))
    }

    protected function I() : MutableMapModel.LinearHashMap<V>
      reads this, this.Repr
      requires Inv()
    {
      MutableMapModel.LinearHashMap(
          FixedSizeHashMap.ModelI(Underlying), Count, Contents)
    }

    //static function I(self: ResizingHashMap<V>): (contents: map<uint64, V>)
    //requires self.Inv()
    //ensures contents == self.Contents
    //reads self, self.Repr
    //{
    //  self.Contents
    //}

  //   static function MapFromStorage(elements: seq<Item<V>>): (result: map<uint64, V>)
  //   {
  //     if |elements| == 0 then
  //       map[]
  //     else
  //       var item := Last(elements);
  //       var dropLastMap := MapFromStorage(DropLast(elements));
  //       if item.Entry? then
  //         dropLastMap[item.key := item.value]
  //       else
  //         dropLastMap
  //   }

  //   lemma CantEquivocateMapFromStorageKey(underlying: FixedSizeHashMap<V>)
  //     requires underlying.Inv()
  //     ensures forall slot1, slot2 :: ValidSlot(underlying.Storage.Length, slot1) && ValidSlot(underlying.Storage.Length, slot2) &&
  //         underlying.Storage[slot1.slot].Entry? && underlying.Storage[slot2.slot].Entry? &&
  //         underlying.Storage[slot1.slot].key == underlying.Storage[slot2.slot].key ==> slot1 == slot2
  //   {
  //     assert underlying.Storage.Length > 0;
  //     assert ValidSlot(underlying.Storage.Length, Slot(0));
  //     assert exists slot :: ValidSlot(underlying.Storage.Length, slot);
  //     forall slot1, slot2 | (
  //       && ValidSlot(underlying.Storage.Length, slot1) && ValidSlot(underlying.Storage.Length, slot2)
  //       && underlying.Storage[slot1.slot].Entry? && underlying.Storage[slot2.slot].Entry?
  //       && underlying.Storage[slot1.slot].key == underlying.Storage[slot2.slot].key)
  //     ensures slot1 == slot2
  //     {
  //       assert underlying.CantEquivocateStorageKey(underlying.Storage[..]);
  //       if underlying.Storage[slot1.slot].Entry? && underlying.Storage[slot2.slot].Entry? &&
  //         underlying.Storage[slot1.slot].key == underlying.Storage[slot2.slot].key {

  //         assert underlying.TwoNonEmptyValidSlotsWithSameKey(underlying.Storage[..], slot1, slot2);
  //         if slot1 != slot2 {
  //           assert false;
  //         }
  //         assert slot1 == slot2;
  //       } else {
  //         assert slot1 == slot2;
  //       }
  //     }
  //   }

  //   lemma MapFromStorageProperties(elements: seq<Item<V>>, result: map<uint64, V>)
  //     requires forall slot1, slot2 :: ValidSlot(|elements|, slot1) && ValidSlot(|elements|, slot2) &&
  //         elements[slot1.slot].Entry? && elements[slot2.slot].Entry? &&
  //         elements[slot1.slot].key == elements[slot2.slot].key ==> slot1 == slot2
  //     requires MapFromStorage(elements) == result
  //     ensures forall slot :: ValidSlot(|elements|, slot) && elements[slot.slot].Entry? ==>
  //         && var item := elements[slot.slot];
  //         && item.key in result && result[item.key] == item.value
  //     ensures forall key :: key in result ==>
  //         exists slot :: ValidSlot(|elements|, slot) && elements[slot.slot] == Entry(key, result[key])
  //     ensures forall key :: key !in result ==>
  //         forall slot :: ValidSlot(|elements|, slot) && elements[slot.slot].Entry?
  //             ==> elements[slot.slot].key != key
  //   {
  //     if |elements| == 0 {
  //     } else if Last(elements).Entry? {
  //       var item := Last(elements);
  //       assert elements == DropLast(elements) + [Last(elements)];
  //       var dropLastMap := MapFromStorage(DropLast(elements));
  //       MapFromStorageProperties(DropLast(elements), dropLastMap);

  //       forall slot | ValidSlot(|elements|, slot) && elements[slot.slot].Entry?
  //       ensures && var item := elements[slot.slot];
  //               && item.key in result && result[item.key] == item.value
  //       {
  //         var slotItem := elements[slot.slot];
  //         if item.key == elements[slot.slot].key {
  //           if slot.slot == |elements| - 1 {
  //             assert slotItem.key in result && result[slotItem.key] == slotItem.value;
  //           } else {
  //             var slot := Slot(|elements| - 1);
  //             assert ValidSlot(|elements|, slot);
  //             assert false;
  //           }
  //         } else {
  //           assert slotItem.key in result && result[slotItem.key] == slotItem.value;
  //         }
  //       }
  //       forall key | key in result
  //       ensures exists slot :: ValidSlot(|elements|, slot) && elements[slot.slot] == Entry(key, result[key])
  //       {
  //         if key == item.key {
  //           var slot := Slot(|elements| - 1);
  //           assert ValidSlot(|elements|, slot);
  //           assert elements[slot.slot] == Entry(key, result[key]);
  //         } else {
  //           assert exists slot :: ValidSlot(|elements|, slot) && elements[slot.slot] == Entry(key, result[key]);
  //         }
  //       }
  //     } else {
  //     }
  //   }

  //   predicate UnderlyingContentsMatchesContents(underlying: FixedSizeHashMap<V>, contents: map<uint64, V>)
  //     reads this, underlying
  //   {
  //     && (forall key :: key in contents ==> key in underlying.Contents && underlying.Contents[key] == Some(contents[key]))
  //     && (forall key :: key !in contents ==> key !in underlying.Contents || underlying.Contents[key].None?)
  //   }

  //   predicate UnderlyingInv(underlying: FixedSizeHashMap<V>)
  //   reads this, this.Repr, underlying, underlying.Repr
  //   {
  //     && |Contents| == Count as nat
  //     && UnderlyingContentsMatchesContents(underlying, Contents)
  //     && underlying.Inv()
  //     && MapFromStorage(underlying.Storage[..]) == Contents
  //   }

  //   lemma UnderlyingInvImpliesMapFromStorageMatchesContents(underlying: FixedSizeHashMap<V>, contents: map<uint64, V>)
  //     requires UnderlyingContentsMatchesContents(underlying, contents)
  //     requires underlying.Inv()
  //     ensures MapFromStorage(underlying.Storage[..]) == contents
  //   {
  //     var mapFromStorage := MapFromStorage(underlying.Storage[..]);
  //     CantEquivocateMapFromStorageKey(underlying);
  //     MapFromStorageProperties(underlying.Storage[..], mapFromStorage);
  //     assert MapFromStorage(underlying.Storage[..]) == contents;
  //   }

  //   predicate ReprInv()
  //     reads this, this.Repr
  //   {
  //     && { this, this.Underlying } <= Repr
  //     && { this, this.Underlying } + this.Underlying.Repr == Repr
  //     && this.Underlying.Repr == { this.Underlying, this.Underlying.Storage }
  //   }

  //   protected predicate Inv()
  //     ensures Inv() ==> ReprInv() // make ReprInv transparent
  //     ensures Inv() ==> |Contents| == Count as nat
  //     reads this, this.Repr
  //   {
  //     && ReprInv()

  //     && UnderlyingInv(Underlying)
  //     && MapFromStorage(Underlying.Storage[..]) == Contents
  //     && |Contents| == Count as nat
  //   }

    constructor (size: uint64)
      requires 128 <= size
      ensures Inv()
      ensures I() == MutableMapModel.Constructor(size)
      ensures fresh(Repr)
    {
      Count := 0;
      Underlying := new FixedSizeHashMap(size);
      Contents := map[];

      new;

      Repr := { this, Underlying } + Underlying.Repr;
      MutableMapModel.reveal_Constructor();

      // mention this to trigger its ensures clause:
      ghost var c := MutableMapModel.Constructor<V>(size);
    }

  //   constructor FromUnderlying(underlying: FixedSizeHashMap<V>, count: uint64)
  //     requires 128 <= underlying.Storage.Length
  //     requires underlying.Inv()
  //     ensures Underlying == underlying
  //     ensures Count == count
  //     ensures Contents == map[]
  //     ensures fresh(this)
  //     ensures Repr == { this, this.Underlying } + Underlying.Repr
  //   {
  //     Count := count;
  //     Underlying := underlying;
  //     Contents := map[];

  //     new;

  //     Repr := { this, Underlying } + Underlying.Repr;
  //   }

  //   method ToArray() returns (result: array<(uint64, V)>)
  //     requires Inv()
  //     ensures Contents == old(Contents)
  //     ensures Count == old(Count)
  //     ensures Count as nat == |Contents|
  //     ensures result.Length == Count as nat
  //     ensures forall i: nat, j: nat :: i < result.Length && j < result.Length && result[i].0 == result[j].0
  //         ==> i == j
  //     // ??? ensures Contents == map i | 0 <= i < result.Length :: result[i].0 := result[i].1
  //     ensures forall i: nat | i < result.Length :: result[i].0 in Contents && Contents[result[i].0] == result[i].1
  //     ensures forall k | k in Contents :: exists i: nat :: i < result.Length && result[i] == (k, Contents[k])
  //     ensures Repr == old(Repr)
  //   {
  //     assume false; // TODO takes too long to verify right now
  //     if Count == 0 {
  //       assert Contents == map[];
  //       result := new [0 as uint64];
  //       assert Contents == map i | 0 <= i < result.Length :: result[i].0 := result[i].1;
  //       return;
  //     }
  //     assert Count > 0;
  //     assert exists i: nat :: i < Underlying.Storage.Length && Underlying.Storage[i].Entry?;


  //     var storagePos: uint64 := 0;
  //     while storagePos < Underlying.Storage.Length as uint64 && !Underlying.Storage[storagePos].Entry?
  //       invariant 0 <= storagePos as int <= Underlying.Storage.Length
  //       invariant MapFromStorage(Underlying.Storage[..storagePos]) == map[]
  //       invariant forall i: nat :: i < storagePos as int ==> !Underlying.Storage[i].Entry?
  //     {
  //       assert MapFromStorage(Underlying.Storage[..storagePos]) == map[];
  //       assert !Underlying.Storage[storagePos].Entry?;
  //       assert DropLast(Underlying.Storage[..storagePos+1]) == Underlying.Storage[..storagePos];
  //       assert MapFromStorage(Underlying.Storage[..storagePos+1]) == map[];

  //       // -- increment --
  //       storagePos := storagePos + 1;
  //       // ---------------
  //     }

  //     assert storagePos as int != Underlying.Storage.Length;

  //     ghost var transferredContents := map[];
  //     assert MapFromStorage(Underlying.Storage[..storagePos]) == transferredContents;
  //     assert transferredContents.Keys <= Contents.Keys;

  //     assert storagePos as int < Underlying.Storage.Length;
  //     var firstEntry := Underlying.Storage[storagePos];
  //     assert Underlying.EntryInSlotMatchesContents(Underlying.Storage[..], Slot(storagePos as int), Underlying.Contents);
  //     assert firstEntry.key in Contents;
  //     // -- mutation --
  //     result := Native.Arrays.newArrayFill(Count, (firstEntry.key, firstEntry.value));
  //     transferredContents := transferredContents[firstEntry.key := firstEntry.value];
  //     // --------------

  //     assert DropLast(Underlying.Storage[..storagePos+1]) == Underlying.Storage[..storagePos];
  //     assert MapFromStorage(Underlying.Storage[..storagePos+1]) == transferredContents;
  //     assert transferredContents.Keys <= Contents.Keys;

  //     // -- increment --
  //     storagePos := storagePos + 1;
  //     // ---------------

  //     // assert transferredContents == map[firstEntry.key := firstEntry.value];
  //     assert result[0] == (firstEntry.key, firstEntry.value); // observe

  //     assert MapFromStorage(Underlying.Storage[..storagePos]) == transferredContents;

  //     var resultPos: uint64 := 1;
  //     assert forall k | k in transferredContents :: exists i: nat :: i < resultPos as int && result[i] == (k, transferredContents[k]);
  //     while storagePos < Underlying.Storage.Length as uint64
  //       invariant 0 <= storagePos as int <= Underlying.Storage.Length
  //       invariant result.Length == Count as nat
  //       invariant resultPos as int == |transferredContents|
  //       invariant resultPos as int <= result.Length
  //       invariant transferredContents.Keys <= Contents.Keys
  //       invariant forall k | k in transferredContents :: transferredContents[k] == Contents[k]
  //       invariant MapFromStorage(Underlying.Storage[..storagePos]) == transferredContents
  //       invariant MapFromStorage(Underlying.Storage[..]) == Contents
  //       invariant forall i: nat | i < resultPos as int :: result[i].0 in transferredContents && transferredContents[result[i].0] == result[i].1
  //       invariant forall i: nat, j: nat :: i < resultPos as int && j < resultPos as int && result[i].0 == result[j].0 ==> i == j
  //       invariant forall k | k in transferredContents :: exists i: nat :: i < resultPos as int && result[i] == (k, transferredContents[k])
  //     {
  //       var item := Underlying.Storage[storagePos];

  //       if item.Entry? {
  //         if resultPos > result.Length as uint64 {
  //           assert |transferredContents| > result.Length;
  //           assert |transferredContents| > |Contents|;
  //           assert |transferredContents.Keys| > |Contents.Keys|;
  //           SetInclusionImpliesSmallerCardinality(transferredContents.Keys, Contents.Keys);
  //           assert false;
  //         } else if resultPos == result.Length as uint64 {
  //           // TODO minimize
  //           assert |transferredContents| == |Contents|;
  //           assert |transferredContents.Keys| == |Contents.Keys|;
  //           SetInclusionAndEqualCardinalityImpliesSetEquality(transferredContents.Keys, Contents.Keys);
  //           assert transferredContents.Keys == Contents.Keys;
  //           assert transferredContents == Contents;
  //           ghost var thisSlot := Slot(storagePos as int);
  //           assert MapFromStorage(Underlying.Storage[..storagePos]) == MapFromStorage(Underlying.Storage[..]);
  //           assert Underlying.EntryInSlotMatchesContents(Underlying.Storage[..], thisSlot, Underlying.Contents);
  //           assert item.key in Underlying.Contents;
  //           assert item.key in Contents;
  //           CantEquivocateMapFromStorageKey(Underlying);
  //           MapFromStorageProperties(Underlying.Storage[..storagePos], Contents);
  //           ghost var previousSlot :| (
  //               && ValidSlot(Underlying.Storage.Length, previousSlot)
  //               && previousSlot.slot < storagePos as int
  //               && Underlying.FilledWithEntryKey(Underlying.Storage[..], previousSlot, item.key));
  //           assert Underlying.FilledWithEntryKey(Underlying.Storage[..], thisSlot, item.key);
  //           assert Underlying.TwoNonEmptyValidSlotsWithSameKey(Underlying.Storage[..], previousSlot, thisSlot);
  //           assert Underlying.CantEquivocateStorageKey(Underlying.Storage[..]);
  //           assert Underlying.SameSlot(Underlying.Storage.Length, previousSlot, thisSlot);
  //           assert false;
  //         }
  //         assert resultPos as int < result.Length;

  //         if item.key in transferredContents {
  //           // TODO minimize
  //           CantEquivocateMapFromStorageKey(Underlying);
  //           MapFromStorageProperties(Underlying.Storage[..storagePos], transferredContents);
  //           ghost var previousSlot :| (
  //               && ValidSlot(Underlying.Storage.Length, previousSlot)
  //               && previousSlot.slot < storagePos as int
  //               && Underlying.FilledWithEntryKey(Underlying.Storage[..], previousSlot, item.key));
  //           ghost var thisSlot := Slot(storagePos as int);
  //           assert Underlying.FilledWithEntryKey(Underlying.Storage[..], thisSlot, item.key);
  //           assert Underlying.TwoNonEmptyValidSlotsWithSameKey(Underlying.Storage[..], previousSlot, thisSlot);
  //           assert Underlying.CantEquivocateStorageKey(Underlying.Storage[..]);
  //           assert Underlying.SameSlot(Underlying.Storage.Length, previousSlot, thisSlot);
  //           assert false;
  //         }
  //         assert item.key !in transferredContents;

  //         assert Underlying.EntryInSlotMatchesContents(Underlying.Storage[..], Slot(storagePos as int), Underlying.Contents); // observe

  //         ghost var transferredContentsBefore := transferredContents;
  //         ghost var resultBefore := result[..];

  //         // -- mutation --
  //         result[resultPos] := (item.key, item.value);
  //         transferredContents := transferredContents[item.key := item.value];
  //         resultPos := resultPos + 1;
  //         // --------------

  //         forall k | k in transferredContents
  //         ensures exists i: nat :: i < resultPos as int && result[i] == (k, transferredContents[k])
  //         {
  //           if k == item.key {
  //           } else {
  //             // TODO minimize
  //             assert exists i: nat :: i < (resultPos as int - 1) && resultBefore[i] == (k, transferredContentsBefore[k]);
  //             assert resultBefore[..(resultPos as int - 1)] == result[..(resultPos as int - 1)];
  //             assert exists i: nat :: i < (resultPos as int - 1) && result[i] == (k, transferredContentsBefore[k]);
  //             assert exists i: nat :: i < (resultPos as int - 1) && result[i] == (k, transferredContents[k]);
  //             assert exists i: nat :: i < resultPos as int && result[i] == (k, transferredContents[k]);
  //           }
  //         }

  //         assert resultPos as int == |transferredContents|;
  //       }

  //       assert DropLast(Underlying.Storage[..storagePos+1]) == Underlying.Storage[..storagePos];

  //       // -- increment --
  //       storagePos := storagePos + 1;
  //       // ---------------

  //       assert transferredContents.Keys <= Contents.Keys;
  //       assert forall k | k in transferredContents :: transferredContents[k] == Contents[k];
  //       assert resultPos as int == |transferredContents|;
  //     }

  //     assert Underlying.Storage[..storagePos] == Underlying.Storage[..];
  //     assert Contents == transferredContents;

  //     assert forall i: nat, j: nat :: i < result.Length && j < result.Length && result[i].0 == result[j].0
  //         ==> i == j;
  //     assert result.Length == Count as nat;
  //     assert forall i: nat | i < result.Length :: result[i].0 in Contents && Contents[result[i].0] == result[i].1;
  //     assert forall k | k in Contents :: exists i: nat :: i < result.Length && result[i] == (k, Contents[k]);
  //   }

  //   method ToMap() returns (result: map<uint64, V>)
  //     requires Inv()
  //     ensures Contents == old(Contents)
  //     ensures Contents == result
  //     ensures Repr == old(Repr)
  //   {
  //     assume false;
  //     var asArray := ToArray();
  //     result := map i: nat | i < asArray.Length :: asArray[i].0 := asArray[i].1;
  //   }

  //   method Realloc()
  //     requires Count as nat < 0x10000000000000000 / 8
  //     requires Inv()
  //     ensures Inv()
  //     ensures Contents == old(Contents)
  //     ensures Underlying.Count as nat < Underlying.Storage.Length - 2
  //     ensures fresh(Underlying)
  //     ensures fresh(Underlying.Storage)
  //     ensures forall r :: r in Repr ==> r in old(Repr) || fresh(r)
  //     modifies this
  //   {
  //     assert |Contents| == Count as nat;

  //     var newSize: uint64 := (128 + Count) * 4;
  //     //print "(debug) MutableMap.Realloc: Count ", Count, ", Realloc ", newSize, "\n";

  //     var newUnderlying := new FixedSizeHashMap(newSize);
  //     assert fresh(newUnderlying) && fresh(newUnderlying.Storage);
  //     
  //     assert newUnderlying.Storage.Length == newSize as nat;

  //     assert MapFromStorage(Underlying.Storage[..]) == Contents;
  //     UnderlyingInvImpliesMapFromStorageMatchesContents(newUnderlying, map[]);
  //     assert MapFromStorage(newUnderlying.Storage[..]) == map[];

  //     var i: uint64 := 0;
  //     ghost var transferredContents := map[];
  //     while i < Underlying.Storage.Length as uint64
  //       invariant i as int <= Underlying.Storage.Length
  //       invariant newUnderlying.Inv()
  //       invariant |Contents| == Count as nat
  //       invariant Contents == old(Contents) // this is necessary because of `modifies this` (?)
  //       invariant UnderlyingContentsMatchesContents(newUnderlying, transferredContents)
  //       invariant MapFromStorage(Underlying.Storage[..i]) == transferredContents
  //       invariant MapFromStorage(Underlying.Storage[..]) == Contents

  //       invariant newUnderlying.Count as nat <= i as nat
  //       invariant Underlying == old(Underlying)
  //       invariant Underlying.Inv()
  //       invariant Underlying.Count == old(Underlying.Count)
  //       invariant Underlying.Storage.Length == old(Underlying.Storage.Length)
  //       invariant newUnderlying.Storage.Length == newSize as nat

  //       invariant |transferredContents| == newUnderlying.Count as nat
  //       invariant transferredContents.Keys <= Contents.Keys
  //       invariant forall key :: key in newUnderlying.Contents ==> exists slot: Slot :: (
  //           && slot.slot < i as int
  //           && ValidSlot(Underlying.Storage.Length, slot)
  //           && Underlying.FilledWithEntryKey(Underlying.Storage[..], slot, key))

  //       invariant fresh(newUnderlying)
  //       invariant fresh(newUnderlying.Storage)
  //       decreases Underlying.Storage.Length - i as int
  //     {
  //       var item := Underlying.Storage[i];
  //       assert Underlying.Storage[..i+1] == Underlying.Storage[..i] + [Underlying.Storage[i]];

  //       if item.Entry? {
  //         assert MapFromStorage(Underlying.Storage[..i]) == transferredContents;
  //         assert |transferredContents| == newUnderlying.Count as nat;

  //         assert fresh(newUnderlying);
  //         assert fresh(newUnderlying.Storage);
  //         if item.key in newUnderlying.Contents {
  //           var j:uint64 :| (
  //               && 0 <= j < i
  //               && ValidSlot(Underlying.Storage.Length, Slot(j as int))
  //               && Underlying.Storage[Slot(j as int).slot].Entry?
  //               && Underlying.Storage[Slot(j as int).slot].key == item.key);
  //           assert ValidSlot(Underlying.Storage.Length, Slot(i as nat));
  //           assert i != j;
  //           assert Slot(i as nat) != Slot(j as nat);
  //           assert Underlying.Storage[Slot(j as nat).slot].key == Underlying.Storage[Slot(i as nat).slot].key;
  //           CantEquivocateMapFromStorageKey(Underlying);
  //           assert false;
  //         }
  //         assert item.key !in newUnderlying.Contents;

  //         assert transferredContents.Keys <= Contents.Keys;
  //         SetInclusionImpliesSmallerCardinality(transferredContents.Keys, Contents.Keys);
  //         assert |transferredContents.Keys| <= |Contents.Keys|;
  //         assert |transferredContents.Keys| == |transferredContents|;
  //         assert |Contents.Keys| == |Contents|;
  //         assert |transferredContents| <= |Contents|;
  //         assert newUnderlying.Count as nat < newUnderlying.Storage.Length - 1;
  //         // -- mutation --
  //         ghost var _ := newUnderlying.Insert(item.key, item.value);
  //         transferredContents := transferredContents[item.key := item.value];
  //         // --------------

  //         forall key | key in newUnderlying.Contents
  //         ensures exists slot: Slot :: (
  //             && slot.slot < i as nat + 1
  //             && ValidSlot(Underlying.Storage.Length, slot)
  //             && Underlying.Storage[slot.slot].Entry?
  //             && Underlying.Storage[slot.slot].key == key)
  //         {
  //           if key == item.key {
  //             assert ValidSlot(Underlying.Storage.Length, Slot(i as nat));
  //             assert exists slot: Slot :: (
  //                 && slot.slot < i as nat + 1
  //                 && ValidSlot(Underlying.Storage.Length, slot)
  //                 && Underlying.Storage[slot.slot].Entry?
  //                 && Underlying.Storage[slot.slot].key == key);
  //           } else {
  //             assert exists slot: Slot :: (
  //                 && slot.slot < i as nat + 1
  //                 && ValidSlot(Underlying.Storage.Length, slot)
  //                 && Underlying.Storage[slot.slot].Entry?
  //                 && Underlying.Storage[slot.slot].key == key);
  //           }
  //         }
  //         assert |transferredContents| == newUnderlying.Count as nat;
  //         assert MapFromStorage(Underlying.Storage[..i+1]) == transferredContents;
  //       } else {
  //         assert forall key :: key in newUnderlying.Contents ==> exists slot: Slot :: (
  //             && slot.slot < i as nat
  //             && ValidSlot(Underlying.Storage.Length, slot)
  //             && Underlying.Storage[slot.slot].Entry?
  //             && Underlying.Storage[slot.slot].key == key);
  //         assert |transferredContents| <= newUnderlying.Count as nat;
  //         assert MapFromStorage(Underlying.Storage[..i+1]) == transferredContents;
  //       }

  //       // -- increment --
  //       i := i + 1;
  //       // ---------------

  //       assert MapFromStorage(Underlying.Storage[..i]) == transferredContents;
  //     }

  //     assert i as nat == Underlying.Storage.Length;
  //     assert Underlying.Storage[..i] == Underlying.Storage[..];

  //     assert MapFromStorage(Underlying.Storage[..]) == transferredContents;
  //     UnderlyingInvImpliesMapFromStorageMatchesContents(newUnderlying, transferredContents);
  //     assert transferredContents == Contents;

  //     assert |Contents| == Count as nat;

  //     assert forall key :: key in Contents ==> key in newUnderlying.Contents && newUnderlying.Contents[key] == Some(Contents[key]);
  //     assert forall key :: key !in Contents ==> key !in newUnderlying.Contents || newUnderlying.Contents[key].None?;

  //     assert newUnderlying.Inv();
  //     assert UnderlyingInv(newUnderlying);
  //     assert UnderlyingContentsMatchesContents(newUnderlying, Contents);
  //     assert MapFromStorage(newUnderlying.Storage[..]) == Contents;
  //     assert newUnderlying.Count as nat < newUnderlying.Storage.Length - 2;

  //     assert fresh(newUnderlying);
  //     assert fresh(newUnderlying.Storage);

  //     // -- mutation --
  //     Underlying := newUnderlying;
  //     // --------------

  //     assert fresh(Underlying);
  //     assert fresh(Underlying.Storage);
  //     Repr := { this, Underlying } + Underlying.Repr;
  //     assert Underlying.Repr == { Underlying, Underlying.Storage };
  //     assert Repr == { this, Underlying, Underlying.Storage };
  //     assert forall r :: r in Repr ==> r in old(Repr) || fresh(r);

  //     assert Underlying.Count as nat < Underlying.Storage.Length - 2;
  //     assert Contents == old(Contents);
  //     assert Count == old(Count);
  //     assert Count <= Underlying.Count;
  //     assert Inv();
  //   }

  //   method Insert(key: uint64, value: V) returns (replaced: Option<V>)
  //     requires Inv()
  //     requires Count as nat < 0x10000000000000000 / 8
  //     ensures Inv()
  //     ensures Contents == old(Contents[key := value])
  //     ensures Count as nat == old(Count as nat) + (if replaced.Some? then 0 else 1)
  //     ensures forall r :: r in Repr ==> r in old(Repr) || fresh(r)
  //     modifies Repr
  //   {
  //     // print "Insert ", key, "\n";

  //     // -- mutation --
  //     if Underlying.Storage.Length as uint64 / 2 <= Underlying.Count {
  //       Realloc();
  //     }
  //     // --------------

  //     assert MapFromStorage(Underlying.Storage[..]) == Contents;
  //     assert Underlying.Count as nat < Underlying.Storage.Length - 2;

  //     // -- mutation --
  //     replaced := Underlying.Insert(key, value);
  //     Contents := Contents[key := value];
  //     // --------------

  //     if replaced.None? {
  //       assert old(key !in Contents);
  //       Count := Count + 1;
  //     } else {
  //       assert old(key in Contents);
  //     }

  //     assert Underlying.Count as nat < Underlying.Storage.Length - 1;

  //     UnderlyingInvImpliesMapFromStorageMatchesContents(Underlying, Contents);
  //     assert MapFromStorage(Underlying.Storage[..]) == Contents;
  //     assert UnderlyingInv(Underlying);
  //     assert Inv();
  //   }

  //   method Remove(key: uint64) returns (removed: Option<V>)
  //     requires Inv()
  //     ensures Inv()
  //     ensures Contents == if key in old(Contents)
  //         then map k | old(k in Contents) && k != key :: old(Contents[k])
  //         else old(Contents)
  //     ensures removed == if old(key in Contents)
  //         then Some(old(Contents)[key])
  //         else None
  //     ensures Count as nat == old(Count as nat) - (if removed.Some? then 1 else 0)
  //     ensures Repr == old(Repr)
  //     modifies Repr
  //   {
  //     // -- mutation --
  //     removed := Underlying.Remove(key);
  //     assert Contents == old(Contents);
  //     Contents := map k | k in Contents && k != key :: Contents[k];
  //     if removed.Some? {
  //       Count := Count - 1;
  //       assert old(key in Contents);
  //       assert Contents.Keys <= old(Contents.Keys);
  //       assert old(|Contents|) == Count as nat + 1;
  //       assert old(|Contents.Keys|) == Count as nat + 1;
  //       assert old(|Contents.Keys - {key}|) == old(|Contents.Keys| - |{key}|);
  //       assert old(Contents.Keys - {key}) == Contents.Keys;
  //       assert |Contents| == old(|Contents|) - 1;
  //       assert |Contents| == Count as nat;
  //     } else {
  //       assert old(key !in Contents);
  //       assert Contents == old(Contents);
  //       assert |Contents| == Count as nat;
  //     }
  //     // --------------

  //     assert UnderlyingContentsMatchesContents(Underlying, Contents);
  //     UnderlyingInvImpliesMapFromStorageMatchesContents(Underlying, Contents);
  //     assert MapFromStorage(Underlying.Storage[..]) == Contents;
  //     assert |Contents| == Count as nat;
  //   }

  //   method Get(key: uint64) returns (found: Option<V>)
  //     requires Inv()
  //     ensures Inv()
  //     ensures Count == old(Count)
  //     ensures Repr == old(Repr)
  //     ensures if key in Contents then found == Some(Contents[key]) else found.None?
  //     ensures found.Some? <==> key in Contents
  //   {
  //     found := Underlying.Get(key);
  //   }
  //   
  //   method Clone() returns (cloned: ResizingHashMap<V>)
  //     requires Inv()
  //     ensures Inv()
  //     ensures Count == old(Count)
  //     ensures Repr == old(Repr)
  //     ensures cloned.Contents == old(Contents)
  //     ensures cloned.Count == old(Count)
  //     ensures fresh(cloned.Repr)
  //     ensures cloned.Inv()
  //     ensures cloned.Repr !! Repr
  //   {
  //     var clonedUnderlying := Underlying.Clone();
  //     cloned := new ResizingHashMap.FromUnderlying(clonedUnderlying, Count);
  //     cloned.Contents := Contents;
  //   }
  }
}
