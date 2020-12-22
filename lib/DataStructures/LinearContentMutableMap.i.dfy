include "../Lang/LinearSequence.s.dfy"
include "../Lang/LinearSequence.i.dfy"
include "../Base/LinearOption.i.dfy"
include "../Lang/Inout.i.dfy"

include "../Lang/NativeTypes.s.dfy"
include "../Base/Option.s.dfy"
include "../Base/sequences.i.dfy"
include "../Base/Sets.i.dfy"
include "../Base/Maps.i.dfy"
include "LinearMutableMapBase.i.dfy"

//
// Immutable (functional) model to support MutableMapImpl.  API provides an
// iterator interface with a deterministic order for parsing/marshaling.
// (That's why the API is/ more than just a Dafny map.)
//
// TODO(jonh): Here and elsewhere, Model files seem to be both
// API (because callers use some of the definitions as 'public' ways
// to reason about the behavior of the modeled Impl) and internal
// proof (the logic half of the behavior of the Impl). It would be
// nice to cleanly separate these concerns.
//

module LinearContentMutableMap {
  import opened NativeTypes
  import opened Options
  import opened LinearOption
  import opened Sequences
  import opened Sets
  import opened Maps

  import opened LinearSequence_i
  import opened LinearSequence_s
  import opened Inout
  import opened Base = LinearMutableMapBase

  linear datatype lItem<V> = Empty | Entry(key: uint64, linear value: V) | Tombstone(key: uint64)
  {
    linear method FreeNonEntry()
    requires !this.Entry? 
    {
      linear match this {
        case Empty() => 
        case Tombstone(key) =>
      }
    }

    function toItem(): Item<V>
    {
      match this {
        case Empty() => Base.Empty()
        case Entry(key, value) => Base.Entry(key, value)
        case Tombstone(key) => Base.Tombstone(key)
      }
    }
  }

  function toItems<V>(litems: lseq<lItem<V>>): (items: seq<Item<V>>)
  ensures |items| == |litems|
  {
    var elements := lseqs(litems);
    seq (|elements|, i requires 0 <= i < |elements| => elements[i].toItem())
  }

  linear datatype FixedSizeLinearHashMap<V> = FixedSizeLinearHashMap(
    linear storage: lseq<lItem<V>>,
    count: uint64,
    ghost contents: map<uint64, Option<V>>)

  function method Uint64SlotForKey<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64): (result: uint64)
  requires 0 < |self.storage| < 0x1_0000_0000_0000_0000
  ensures ValidSlot(|self.storage|, Slot(result as nat))
  ensures Slot(result as nat) == SlotForKey(|self.storage|, key)
  {
    var h := hash64(key);
    var storageLength := lseq_length_as_uint64(self.storage);
    h % (storageLength as uint64)
  }

  predicate FixedSizeInv<V>(self: FixedSizeLinearHashMap<V>)
  {
    && 128 <= |self.storage| < 0x1_0000_0000_0000_0000
    && (self.count as nat) < 0x1_0000_0000_0000_0000
    && self.count as nat < |self.storage|

    && |self.contents| == (self.count as nat)
    && lseq_has_all(self.storage)
    && SeqMatchesContentKeys(toItems(self.storage), self.contents)
    && EntriesMatchContentValue(toItems(self.storage), self.contents)
    && TombstonesMatchContentValue(toItems(self.storage), self.contents)
  }

  predicate IsConstructorFromSize<V>(size: nat, self: FixedSizeLinearHashMap<V>)  
  {
    && |self.storage| == size
    && self.count == 0
    && self.contents == map[]
    && (forall slot :: ValidSlot(|self.storage|, slot) ==> SlotIsEmpty(toItems(self.storage), slot))
    && FixedSizeInv(self)
  }

  method ConstructorFromSize<V>(size: uint64) returns (linear self: FixedSizeLinearHashMap<V>)
  requires 128 <= size
  ensures IsConstructorFromSize(size as nat, self)
  {
    linear var storage := lseq_alloc(size);

    var i := 0 as uint64;
    while i < size
      invariant i <= size
      invariant size as nat == |storage|
      invariant forall j | 0 <= j < i as nat :: lseq_has(storage)[j]
      invariant forall j | i as nat <= j < size as nat :: !lseq_has(storage)[j]
      invariant forall slot :: ValidSlot(|storage|, slot) && 0 <= slot.slot < i as nat 
          ==> SlotIsEmpty(toItems(storage), slot)
    {
      linear var item := lItem.Empty();
      lseq_give_inout(inout storage, i, item);
      i := i + 1;
    }

    self := FixedSizeLinearHashMap(
     /* storage := */ storage,
     /* count := */ 0,
     /* contents := */ map[]);
  }

  lemma allNonEmptyImpliesCountEqStorageSize<V>(self: FixedSizeLinearHashMap<V>)
  requires FixedSizeInv(self)
  ensures (forall j | 0 <= j < |self.storage| :: !self.storage[j].Empty?)
      ==> self.count as int == |self.storage|
  {
    var elements := self.storage;
    if forall j | 0 <= j < |elements| :: !elements[j].Empty? {
      var elementIndices := set i | 0 <= i < |elements|;
      assert IndexSetThrough(toItems(elements), |elements|) == elementIndices; // trigger
      CardinalityOfSetsOfSequenceIndices(toItems(elements), elementIndices);
      IndexSetMatchesContents(toItems(elements), self.contents);
    }
  }

  function {:opaque} getEmptyWitness<V>(self: FixedSizeLinearHashMap<V>, i: uint64) : (res : uint64)
  requires FixedSizeInv(self)
  requires 0 <= i as int <= |self.storage|
  requires forall j | 0 <= j < i as int :: !self.storage[j].Empty?
  requires self.count as int < |self.storage|
  decreases |self.storage| - i as int
  ensures 0 <= res as int < |self.storage|
  ensures self.storage[res as int].Empty?
  {
    allNonEmptyImpliesCountEqStorageSize(self);

    if self.storage[i as int].Empty? then
      i
    else
      getEmptyWitness(self, i+1)
  }

  function method ProbeIterate<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64, slotIdx: uint64)
      : (foundSlotIdx: uint64)
  requires FixedSizeInv(self)
  requires 0 <= slotIdx as int < |self.storage|

  // We use the emptyWitness to prove termination.
  // We will necessarily terminate when we reach this index,
  // if not earlier.
  decreases var wit := getEmptyWitness(self, 0);
    if slotIdx > wit
      then wit as int - slotIdx as int + |self.storage|
      else wit as int - slotIdx as int

  ensures 0 <= foundSlotIdx as int < |self.storage|
  {
    shared var item := lseq_peek(self.storage, slotIdx);
    if item.Empty? || item.key == key then
      slotIdx
    else (
      ProbeIterate(self, key, Uint64SlotSuccessorUint64(lseq_length_as_uint64(self.storage), slotIdx))
    )
  }

  function method {:opaque} Probe<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64): (foundSlotIdx: uint64)
  requires FixedSizeInv(self)
  requires self.count as int < |self.storage|
  ensures 0 <= foundSlotIdx as int < |self.storage|
  {
    ProbeIterate(self, key, Uint64SlotForKey(self, key))
  }

  datatype ProbeResult<V> = ProbeResult(
      slotIdx: uint64,
      ghost startSlotIdx: uint64,
      ghost ghostSkips: uint64)

  lemma LemmaProbeResult<V>(self: FixedSizeLinearHashMap<V>, key: uint64)
  returns (result : ProbeResult<V>)
  requires FixedSizeInv(self)
  ensures result.slotIdx == Probe(self, key)
  ensures ValidSlot(|self.storage|, Slot(result.slotIdx as nat))
  ensures ValidSlot(|self.storage|, Slot(result.startSlotIdx as nat))
  ensures Slot(result.startSlotIdx as nat) == SlotForKey(|self.storage|, key)
  ensures 0 <= result.ghostSkips
  ensures result.slotIdx as nat == KthSlotSuccessor(|self.storage|, Slot(result.startSlotIdx as nat), result.ghostSkips as nat).slot
  ensures key in self.contents ==> SlotExplainsKey(toItems(self.storage), result.ghostSkips as nat, key)
  ensures key !in self.contents ==> FilledWithOtherKeys(toItems(self.storage), Slot(result.startSlotIdx as nat), result.ghostSkips as nat, key) 
    && (self.storage[result.slotIdx as nat].Empty? || (self.storage[result.slotIdx as nat].Tombstone? && self.storage[result.slotIdx as nat].key == key))
  ensures self.storage[result.slotIdx as nat].Entry? ==> key in self.contents && key == self.storage[result.slotIdx as nat].key
  ensures self.storage[result.slotIdx as nat].Empty? ==> key !in self.contents
  {
    reveal_Probe();

    var slotIdx := Uint64SlotForKey(self, key);
    var startSlotIdx := slotIdx;
    ghost var startSlot := Slot(startSlotIdx as nat);

    ghost var viewFromStartSlot := View(toItems(self.storage), startSlotIdx as nat);
    ViewsHaveConsistentCounts(toItems(self.storage), viewFromStartSlot, startSlotIdx as nat);
    CountFilledMatchesIndexSet(toItems(self.storage));
    IndexSetMatchesContents(toItems(self.storage), self.contents);

    forall dist: nat | dist < |self.storage|
    ensures viewFromStartSlot[dist] ==
      self.storage[KthSlotSuccessor(|self.storage|, startSlot, dist).slot].toItem()
    {
      KthSlotSuccessorWrapsAround(|self.storage|, startSlot, dist); // observe
    }

    var skips := 0;
    while true
      invariant skips < (|self.storage| as uint64)
      invariant slotIdx < (|self.storage| as uint64)
      invariant |self.storage| == |viewFromStartSlot|
      invariant toItems(self.storage)[startSlotIdx..] 
        + toItems(self.storage)[..startSlotIdx] == viewFromStartSlot
      invariant slotIdx as nat ==
        KthSlotSuccessor(|self.storage|, startSlot, skips as nat).slot
      invariant skips < (|self.storage| as uint64) ==> 
        toItems(self.storage)[slotIdx] == viewFromStartSlot[skips]
      invariant ValidSlot(|self.storage|, KthSlotSuccessor(|self.storage|, startSlot, skips as nat))
      invariant FilledWithOtherKeys(toItems(self.storage), startSlot, skips as nat, key)
      invariant CountFilled(viewFromStartSlot[..skips]) == skips as nat

      invariant Probe(self, key) == ProbeIterate(self, key, slotIdx)

      decreases var wit := getEmptyWitness(self, 0);
        if slotIdx > wit
          then wit as int - slotIdx as int + |self.storage|
          else wit as int - slotIdx as int
    {
      if self.storage[slotIdx as nat].Empty? 
        || (self.storage[slotIdx as nat].Tombstone? 
        && self.storage[slotIdx as nat].key == key) {
        result := ProbeResult(slotIdx, startSlotIdx, skips);
        return;
      } else if self.storage[slotIdx as nat].key == key {
        assert EntryInSlotMatchesContents(toItems(self.storage), Slot(slotIdx as nat), self.contents); // observe
        result := ProbeResult(slotIdx, startSlotIdx, skips);
        return;
      }

      ghost var skipsBefore := skips;

      // -- increment --
      slotIdx := Uint64SlotSuccessor(|self.storage|, slotIdx);
      skips := skips + 1;
      // ---------------

      assert viewFromStartSlot[..skips] == viewFromStartSlot[..skipsBefore] + [viewFromStartSlot[skipsBefore]]; // observe
      CountFilledAdditive(viewFromStartSlot[..skipsBefore], [viewFromStartSlot[skipsBefore]]);

      assert Probe(self, key) == ProbeIterate(self, key, slotIdx);

      if skips == |self.storage| as uint64 {
        forall ensures false
        {
          calc {
            |self.storage|;
            skips as nat;
            CountFilled(viewFromStartSlot[..skips]);
              { assert viewFromStartSlot[..skips] == viewFromStartSlot; } // observe
            CountFilled(viewFromStartSlot);
            |self.contents|;
            self.count as nat;
            < |self.storage|;
          }
        }
      }
    }
  }
  
  predicate {:opaque} IsFixedSizeInsert<V> (self: FixedSizeLinearHashMap, key: uint64, value: V, 
    self': FixedSizeLinearHashMap, replaced: lOption<V>)
  requires FixedSizeInv(self)
  requires self.count as nat < |self.storage| - 1
  {
    && var slotIdx := Probe(self, key);
    && self'.contents == self.contents[key := Some(value)]
    && toItems(self'.storage) == toItems(self.storage)[slotIdx as nat := Base.Entry(key, value)]
    && match self.storage[slotIdx as nat] {
        case Empty => (
          && replaced == lNone
          && self'.count == self.count + 1
        )
        case Tombstone(_) => (
          && replaced == lNone
          && self'.count == self.count
        )
        case Entry(_, value) => (
          && replaced == lSome(value)
          && self'.count == self.count
        )
      }
    && lseq_has_all(self'.storage)
  }

  method FixedSizeInsert<V>(linear inout self: FixedSizeLinearHashMap, key: uint64, linear value: V)
  returns (linear replaced: lOption<V>)
  requires FixedSizeInv(old_self)
  requires old_self.count as nat < |old_self.storage| - 1
  ensures FixedSizeInv(self)
  ensures self.contents == old_self.contents[key := Some(value)]
  ensures key !in old_self.contents ==> replaced.lNone?
  ensures key in old_self.contents ==> replaced.Option() == old_self.contents[key]
  ensures replaced.lSome? ==> key in old_self.contents
  ensures |self.storage| == |old_self.storage|
  {
    linear var entry := lItem.Entry(key, value);
    replaced := FixedSizeInsertEntry(inout self, entry);
  }

  method FixedSizeInsertEntry<V>(linear inout self: FixedSizeLinearHashMap, linear entry: lItem<V>)
  returns (linear replaced: lOption<V>)
  requires entry.Entry?
  requires FixedSizeInv(old_self)
  requires old_self.count as nat < |old_self.storage| - 1
  ensures FixedSizeInv(self)
  ensures self.contents == old_self.contents[entry.key := Some(entry.value)]
  ensures entry.key !in old_self.contents ==> replaced.lNone?
  ensures entry.key in old_self.contents ==> replaced.Option() == old_self.contents[entry.key]
  ensures replaced.lSome? ==> entry.key in old_self.contents
  ensures |self.storage| == |old_self.storage|
  {
    reveal_IsFixedSizeInsert();
    var slotIdx := Probe(self, entry.key);

    ghost var contents := old_self.contents[entry.key := Some(entry.value)];
    inout ghost self.contents := contents;
    
    linear var olditem := lseq_take_inout(inout self.storage, slotIdx);
    lseq_give_inout(inout self.storage, slotIdx, entry);

    if olditem.Empty? {
      olditem.FreeNonEntry();
      inout self.count := self.count + 1;
      replaced := lNone;
   } else if olditem.Tombstone? {
      olditem.FreeNonEntry();
      replaced := lNone;
    } else {
      linear var Entry(_, value) := olditem;
      replaced := lSome(value);
    }
    LemmaFixedSizeInsert(old_self, entry.key, entry.value, self, replaced);
  }

  lemma LemmaFixedSizeInsert<V>(self: FixedSizeLinearHashMap, key: uint64, value: V, 
    self': FixedSizeLinearHashMap, replaced: lOption<V>)
  requires IsFixedSizeInsert.requires(self, key, value, self', replaced)
  requires IsFixedSizeInsert(self, key, value, self', replaced)
  ensures FixedSizeInv(self')
  ensures self'.contents == self.contents[key := Some(value)]
  ensures key !in self.contents ==> replaced.lNone?
  ensures key in self.contents ==> replaced.Option() == self.contents[key]
  ensures replaced.lSome? ==> key in self.contents
  ensures |self'.storage| == |self.storage|
  {
    reveal_IsFixedSizeInsert();

    var probeRes := LemmaProbeResult(self, key);
    var slotIdx := probeRes.slotIdx;
    var probeStartSlotIdx := probeRes.startSlotIdx;
    var probeSkips := probeRes.ghostSkips;

    forall explainedKey | explainedKey in self'.contents
    ensures exists skips :: SlotExplainsKey(toItems(self'.storage), skips, explainedKey)
    {
      if key == explainedKey {
        assert SlotExplainsKey(toItems(self'.storage), probeSkips as nat, key); // observe
      } else {
        var oldSkips :| SlotExplainsKey(toItems(self.storage), oldSkips, explainedKey);
        assert SlotExplainsKey(toItems(self'.storage), oldSkips, explainedKey); // observe
      }
    }
  
    forall slot | ValidSlot(|self'.storage|, slot) && toItems(self'.storage)[slot.slot].Entry?
    ensures && var item := toItems(self'.storage)[slot.slot];
            && self'.contents[item.key] == Some(item.value)
    {
      var item := toItems(self'.storage)[slot.slot];
      if slot != Slot(slotIdx as nat) {
        if item.key == key {
          assert TwoNonEmptyValidSlotsWithSameKey(toItems(self'.storage), slot, Slot(slotIdx as nat)); // observe
          assert SameSlot(|self'.storage|, slot, Slot(slotIdx as nat)); // observe
          assert false;
        }
      }
    }
    forall slot | ValidSlot(|self'.storage|, slot) && toItems(self'.storage)[slot.slot].Tombstone?
    ensures && var item := self'.storage[slot.slot];
            && self'.contents[item.key].None?
    {
      var item := self'.storage[slot.slot];
      if slot != Slot(slotIdx as nat) {
        if item.key == key {
          assert TwoNonEmptyValidSlotsWithSameKey(toItems(self'.storage), slot, Slot(slotIdx as nat)); // observe
          assert SameSlot(|self'.storage|, slot, Slot(slotIdx as nat)); // observe
          assert false;
        }
      }
    }
  }

  predicate IsFixedSizeUpdateBySlot<V>(self: FixedSizeLinearHashMap<V>, slotIdx: uint64, value: V,
    self': FixedSizeLinearHashMap<V>, replaced: V)
  requires FixedSizeInv(self)
  requires 0 <= slotIdx as int < |self.storage|
  requires self.storage[slotIdx as nat].Entry?
  {
    && var key := self.storage[slotIdx as nat].key;
    && self'.count == self.count
    && |self'.contents| == |self.contents|
    && self'.contents == self.contents[key := Some(value)]
    && replaced == self.storage[slotIdx as nat].value
    && lseq_has_all(self'.storage)
    && toItems(self'.storage) == toItems(self.storage)[slotIdx as nat := Base.Entry(key, value)]
  }

  method FixedSizeUpdateBySlot<V>(linear inout self: FixedSizeLinearHashMap<V>, slotIdx: uint64, linear value: V)
  returns (linear replaced: V)
  requires FixedSizeInv(old_self)
  requires 0 <= slotIdx as int < |old_self.storage|
  requires old_self.storage[slotIdx as nat].Entry?
  ensures IsFixedSizeUpdateBySlot(old_self, slotIdx, value, self, replaced)
  ensures FixedSizeInv(self)
  {
    linear var entry: lItem<V> := lseq_take_inout(inout self.storage, slotIdx);
    linear var Entry(key, oldvalue) := entry;
    lseq_give_inout(inout self.storage, slotIdx, lItem.Entry(key, value));
    replaced := oldvalue;

    inout ghost self.contents := self.contents[key := Some(value)];
    assert EntryInSlotMatchesContents(toItems(old_self.storage), Slot(slotIdx as int), old_self.contents);
    LemmaFixedSizeUpdateBySlot(old_self, slotIdx, value, self, replaced);
  }

  lemma LemmaFixedSizeUpdateBySlot<V>(self: FixedSizeLinearHashMap<V>, slotIdx: uint64, value: V,
    self': FixedSizeLinearHashMap<V>, replaced: V)
  requires IsFixedSizeUpdateBySlot.requires(self, slotIdx, value, self', replaced)
  requires IsFixedSizeUpdateBySlot(self, slotIdx, value, self', replaced)
  ensures FixedSizeInv(self')
  {
    var key := self.storage[slotIdx as nat].key;

    forall explainedKey | explainedKey in self'.contents
    ensures exists skips :: SlotExplainsKey(toItems(self'.storage), skips, explainedKey)
    {
      var oldSkips :| SlotExplainsKey(toItems(self.storage), oldSkips, explainedKey);
      assert SlotExplainsKey(toItems(self'.storage), oldSkips, explainedKey); // observe
    }
  
    forall slot | ValidSlot(|self'.storage|, slot)
        && SlotIsEntry(toItems(self'.storage), slot)
    ensures EntryInSlotMatchesContents(toItems(self'.storage), slot, self'.contents)
    {
      assert EntryInSlotMatchesContents(toItems(self.storage), slot, self.contents);
      if self.storage[slot.slot].key == key {
        assert TwoNonEmptyValidSlotsWithSameKey(toItems(self.storage), slot, Slot(slotIdx as int));
      }
    }

    forall slot | ValidSlot(|self'.storage|, slot)
        && toItems(self'.storage)[slot.slot].Tombstone?
    ensures TombstoneInSlotMatchesContents(toItems(self'.storage), slot, self'.contents)
    {
      if slot.slot != slotIdx as nat && self.storage[slot.slot].key == key {
        assert TwoNonEmptyValidSlotsWithSameKey(toItems(self'.storage), slot, Slot(slotIdx as nat)); // observe
        assert SameSlot(|self'.storage|, slot, Slot(slotIdx as nat)); // observe
        assert false;
      }
    }
  }

  function method IsEntry<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64) : (b: bool)
  requires FixedSizeInv(self)
  ensures b == (key in self.contents && self.contents[key].Some?)
  {
    var slotIdx := Probe(self, key);
    var b := lseq_peek(self.storage, slotIdx).Entry?;
    assert b == (key in self.contents && self.contents[key].Some?) by {
      var _ := LemmaProbeResult(self, key);
    }
    b
  }

  function method {:opaque} FixedSizeGet<V>(shared self: FixedSizeLinearHashMap<V>, key: uint64)
    : (shared found: V)
  requires FixedSizeInv(self)
  requires IsEntry(self, key)
  ensures key in self.contents && self.contents[key].Some?
  {
    var slotIdx := Probe(self, key);
    lseq_peek(self.storage, slotIdx).value
    // TODO(Jialin): update to return shared lOption<V>
  }

  lemma LemmaFixedSizeGet<V>(self: FixedSizeLinearHashMap<V>, key: uint64)
  requires FixedSizeGet.requires(self, key)
  requires key in self.contents && self.contents[key].Some?
  ensures FixedSizeGet(self, key) == self.contents[key].value
  {
    reveal_FixedSizeGet();
    var _ := LemmaProbeResult(self, key);
  }

  predicate IsFixedSizeRemove<V>(self: FixedSizeLinearHashMap<V>, key: uint64, 
    self': FixedSizeLinearHashMap<V>, removed: lOption<V>)
  requires FixedSizeInv(self)
  {
    && var slotIdx := Probe(self, key);
    && (!self.storage[slotIdx as nat].Entry? ==> self' == self && removed == lNone)
    && (self.storage[slotIdx as nat].Entry? ==> 
      && self'.count == self.count
      && self'.contents == self.contents[key := None]
      && |self'.contents| == |self.contents|
      && lseq_has_all(self'.storage)
      && toItems(self'.storage) == toItems(self.storage)[slotIdx as nat := Base.Tombstone(key)]
      && removed == lSome(self.storage[slotIdx as nat].value)
    )
    && (removed.lSome? <==> (key in self.contents && self.contents[key].Some?)) // leave this here for now
  }
  
  method FixedSizeRemove<V>(linear inout self: FixedSizeLinearHashMap<V>, key: uint64)
  returns (linear removed: lOption<V>)
  requires FixedSizeInv(old_self)
  ensures IsFixedSizeRemove(old_self, key, self, removed)
  ensures FixedSizeInv(self)
  {
    var slotIdx := Probe(self, key);
    var _ := LemmaProbeResult(self, key);

    if lseq_peek(self.storage, slotIdx).Entry? {
      linear var item: lItem<V> := lseq_take_inout(inout self.storage, slotIdx);
      lseq_give_inout(inout self.storage, slotIdx, lItem.Tombstone(key));
      linear var Entry(_, value) := item;
      removed := lSome(value);

      inout ghost self.contents := self.contents[key := None];
      assert EntryInSlotMatchesContents(toItems(old_self.storage), Slot(slotIdx as int), old_self.contents);
    } else {
      removed := lNone;
    }
    LemmaFixedSizeRemove(old_self, key, self, removed);
  }

  lemma LemmaFixedSizeRemove<V>(self: FixedSizeLinearHashMap<V>, key: uint64, 
    self': FixedSizeLinearHashMap<V>, removed: lOption<V>)
  requires IsFixedSizeRemove.requires(self, key, self', removed)
  requires IsFixedSizeRemove(self, key, self', removed)
  ensures FixedSizeInv(self')
  {
    var probeRes := LemmaProbeResult(self, key);
    var slotIdx := probeRes.slotIdx;
    var probeStartSlotIdx := probeRes.startSlotIdx;
    var probeSkips := probeRes.ghostSkips;

    if self.storage[slotIdx as nat].Entry? {
      forall explainedKey | explainedKey in self'.contents
      ensures exists skips :: SlotExplainsKey(toItems(self'.storage), skips, explainedKey)
      {
        if key == explainedKey {
          assert SlotExplainsKey(toItems(self'.storage), probeSkips as nat, key);
        } else {
          var oldSkips :| SlotExplainsKey(toItems(self.storage), oldSkips, explainedKey);
          assert SlotExplainsKey(toItems(self'.storage), oldSkips, explainedKey);
        }
      }

      forall slot | ValidSlot(|self'.storage|, slot) && toItems(self'.storage)[slot.slot].Entry?
      ensures && var item := self'.storage[slot.slot];
              && self'.contents[item.key] == Some(item.value)
      {
        var item := self'.storage[slot.slot];
        if slot != Slot(slotIdx as nat) && item.key == key {
          assert CantEquivocateStorageKey(toItems(self'.storage));
          assert TwoNonEmptyValidSlotsWithSameKey(toItems(self'.storage), slot, Slot(slotIdx as nat));
          assert false;
        }
      }
    }
  }

  //////// Resizing Hash Map

  linear datatype LinearHashMap<V> = LinearHashMap(
    linear underlying: FixedSizeLinearHashMap<V>,
    count: uint64,
    ghost contents: map<uint64, V>)
  {
    predicate Inv() {Inv0(this)} // HACK Inv0: is there a better way to refer to the outer Inv(...) from inside Inv()?
  }

  lemma CantEquivocateMapFromStorageKey<V>(underlying: FixedSizeLinearHashMap<V>)
  requires FixedSizeInv(underlying)
  ensures CantEquivocate(toItems(underlying.storage))
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
      assert CantEquivocateStorageKey(toItems(underlying.storage));
      if underlying.storage[slot1.slot].Entry? && underlying.storage[slot2.slot].Entry? &&
        underlying.storage[slot1.slot].key == underlying.storage[slot2.slot].key {

        assert TwoNonEmptyValidSlotsWithSameKey(toItems(underlying.storage), slot1, slot2);
        if slot1 != slot2 {
          assert false;
        }
        assert slot1 == slot2;
      } else {
        assert slot1 == slot2;
      }
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
    && MapFromStorage(toItems(underlying.storage)) == self.contents
  }

  lemma UnderlyingInvImpliesMapFromStorageMatchesContents<V>(underlying: FixedSizeLinearHashMap<V>, contents: map<uint64, V>)
  requires UnderlyingContentsMatchesContents(underlying, contents)
  requires FixedSizeInv(underlying)
  ensures MapFromStorage(toItems(underlying.storage)) == contents
  {
    var mapFromStorage := MapFromStorage(toItems(underlying.storage));
    CantEquivocateMapFromStorageKey(underlying);
    MapFromStorageProperties(toItems(underlying.storage), mapFromStorage);
    assert MapFromStorage(toItems(underlying.storage)) == contents;
  }

  predicate Inv0<V>(self: LinearHashMap<V>) { Inv(self) }

  protected predicate Inv<V>(self: LinearHashMap<V>)
  ensures Inv(self) ==> |self.contents| == self.count as nat
  ensures Inv(self) ==> UnderlyingInv(self, self.underlying)
  {
    && UnderlyingInv(self, self.underlying)
    && MapFromStorage(toItems(self.underlying.storage)) == self.contents
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
      && MapFromStorage(toItems(self.underlying.storage)) == self.contents
      && |self.contents| == self.count as nat)
  {
  }

  predicate IsConstructor<V>(self: LinearHashMap<V>, size: uint64)
  requires 128 <= size
  {
    && Inv(self)
    && self.contents == map[]
  }

  method Constructor<V>(size: uint64) returns (linear self: LinearHashMap<V>)
  requires 128 <= size
  ensures IsConstructor(self, size)
  {
    linear var fixed := ConstructorFromSize(size);
    self := LinearHashMap(fixed, 0, map[]);

    assert forall slot :: ValidSlot(|self.underlying.storage|, slot) ==> !self.underlying.storage[slot.slot].Entry?;
    UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents);
    assert MapFromStorage(toItems(self.underlying.storage)) == self.contents;
  }

  lemma LemmaEntryKeyInContents<V>(self: LinearHashMap<V>, i: uint64)
  requires Inv(self)
  requires 0 <= i as int < |self.underlying.storage|
  requires self.underlying.storage[i as nat].Entry?
  ensures self.underlying.storage[i as nat].key in self.contents
  {
    assert EntryInSlotMatchesContents(toItems(self.underlying.storage), Slot(i as nat), self.underlying.contents); // trigger
  }

  predicate IsRealloc<V>(self: LinearHashMap<V>, self': LinearHashMap<V>)
  requires Inv(self)
  requires self.count as nat < 0x1_0000_0000_0000_0000 / 8
  {
    && self'.contents == self.contents
    && self'.underlying.count as nat < |self'.underlying.storage| - 2
    && Inv(self')
  }

  method Realloc<V>(linear inout self: LinearHashMap<V>)
  requires Inv(old_self)
  requires old_self.count as nat < 0x1_0000_0000_0000_0000 / 8
  ensures IsRealloc(old_self, self)
  {
    var newSize: uint64 := (128 + self.count) * 4;
    linear var newUnderlying := ConstructorFromSize(newSize);

    ghost var transferredContents := map[];
    ghost var transfers := toItems(self.underlying.storage);
    CantEquivocateMapFromStorageKey(self.underlying);

    var i := 0 as uint64;
    var size := lseq_length_as_uint64(self.underlying.storage);

    while i < size
      invariant i <= size
      invariant size as nat == |self.underlying.storage|
      invariant self.count as nat == |self.contents|
      invariant |newUnderlying.storage| == newSize as nat

      invariant transferredContents.Keys <= self.contents.Keys
      invariant newUnderlying.count as nat == |transferredContents|
      invariant newUnderlying.count as nat < |newUnderlying.storage| - 2
      invariant (forall key :: key in newUnderlying.contents ==> 
        EntryExistsInElements(transfers, i, key))

      invariant FixedSizeInv(newUnderlying)
      invariant UnderlyingContentsMatchesContents(newUnderlying, transferredContents)
      invariant toItems(self.underlying.storage)[i..] == transfers[i..]
      invariant MapFromStorage(transfers[..i]) == transferredContents
      invariant MapFromStorage(transfers) == self.contents

      invariant (forall j | i as nat <= j < size as nat :: lseq_has(self.underlying.storage)[j])
      invariant (forall j | 0 <= j < i as nat :: !lseq_has(self.underlying.storage)[j])
    {
      assert i < size;
      assert Last(transfers[..i+1]) == transfers[i];
      assert transfers[..i] == DropLast(transfers[..i+1]);

      linear var item := lseq_take_inout(inout self.underlying.storage, i);
      if item.Entry? {
        ElementsEntryInMap(transfers, item.toItem());
        if item.key in newUnderlying.contents {
          var j:uint64 :| (
              && 0 <= j < i
              && ValidSlot(|transfers|, Slot(j as int))
              && transfers[Slot(j as int).slot].Entry?
              && transfers[Slot(j as int).slot].key == item.key);
          assert ValidSlot(|transfers|, Slot(i as nat));
          assert false;
        }
        assert item.key !in newUnderlying.contents;

        assert transferredContents.Keys <= self.contents.Keys;
        SetInclusionImpliesSmallerCardinality(transferredContents.Keys, self.contents.Keys);
        assert |transferredContents.Keys| <= |self.contents.Keys|;
        assert |transferredContents| <= |self.contents|;
        assert newUnderlying.count as nat < |newUnderlying.storage| - 1;

        // ------ Mutation ------
        transferredContents := transferredContents[item.key := item.value];
        linear var replaced := FixedSizeInsertEntry(inout newUnderlying, item);
        // ----------------------
        linear match replaced { case lNone() => }
        assert ValidSlot(|transfers|, Slot(i as nat));
        assert FixedSizeInv(newUnderlying);
      } else {
        item.FreeNonEntry();
      }
      assert newUnderlying.count as nat < |newUnderlying.storage| - 2;
      i := i + 1;
    }

    assert transfers[..i] == transfers;
    assert UnderlyingContentsMatchesContents(newUnderlying, transferredContents);
    assert UnderlyingContentsMatchesContents(newUnderlying, self.contents);
    UnderlyingInvImpliesMapFromStorageMatchesContents(newUnderlying, self.contents);

    linear var oldUnderlying := Replace(inout self.underlying, newUnderlying);
    linear var FixedSizeLinearHashMap(oldstorage, _, _) := oldUnderlying;
    lseq_free(oldstorage);
  }

  method Insert<V>(linear inout self: LinearHashMap, key: uint64, linear value: V) 
  returns (linear replaced: lOption<V>)
  requires Inv(old_self)
  requires old_self.count as nat < 0x1_0000_0000_0000_0000 / 8
  ensures
    && Inv(self)
    && self.contents == old_self.contents[key := value]
    && self.count as nat == old_self.count as nat + (if replaced.lSome? then 0 else 1)
    && (replaced.lSome? ==> MapsTo(old_self.contents, key, replaced.value))
    && (replaced.lNone? ==> key !in old_self.contents)
  {
    var len := lseq_length_as_uint64(self.underlying.storage);
    if len / 2 <= self.underlying.count {
      Realloc(inout self);
    }
    // --------------

    // -- mutation --
    replaced := FixedSizeInsert(inout self.underlying, key, value);
    inout ghost self.contents := self.contents[key := value];
    if replaced.lNone? {
      inout self.count := self.count + 1;
    }
    // --------------

    UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents);
  }

  method Remove<V>(linear inout self: LinearHashMap, key: uint64) 
  returns (linear removed: lOption<V>)
  requires Inv(old_self)
  ensures Inv(self)
  ensures removed.lSome? ==>
      key in old_self.contents && old_self.contents[key] == removed.value
  ensures removed.lNone? ==> key !in old_self.contents
  ensures (self.contents == if key in old_self.contents
      then map k | k in old_self.contents && k != key :: old_self.contents[k]
      else old_self.contents)
  {
    // -- mutation --
    removed := FixedSizeRemove(inout self.underlying, key);
    inout ghost self.contents := map k | k in self.contents && k != key :: self.contents[k];
    if removed.lSome? {
      inout self.count := self.count - 1;
    }
    // -------------- 

    UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents); 
    assert self.count as nat == |self.contents| by {
      if removed.lSome? {
        assert key in old_self.contents;
        assert self.contents.Keys <= old_self.contents.Keys;
        assert |old_self.contents| == self.count as nat + 1;
        assert |old_self.contents.Keys| == self.count as nat + 1;
        assert |old_self.contents.Keys - {key}| == |old_self.contents.Keys| - |{key}|;
        assert old_self.contents.Keys - {key} == self.contents.Keys;
        assert |self.contents| == |old_self.contents| - 1;
        assert |self.contents| == self.count as nat;
      } else {
        assert key !in old_self.contents;
        assert self.contents == old_self.contents;
        assert |self.contents| == self.count as nat;
      }
    }
  }

  method Get<V>(shared self: LinearHashMap, key: uint64) returns (shared result: V)
  requires Inv(self)
  requires IsEntry(self.underlying, key)
  ensures key in self.contents && result == self.contents[key]
  {
    result := FixedSizeGet(self.underlying, key);
    LemmaFixedSizeGet(self.underlying, key);
  }

  //////// Iterator

  // We have two types of iterators.
  //
  // Iterator is usually more convenient as it has the IteratorOutput
  // built-in.
  //
  // SimpleIterator doesn't (you have to call SimpleIteratorOutput)
  // but has the advantage that the WFSimpleIter condition doesn't
  // depend on the key/value being correct. Thus the well-formedness
  // of a SimpleIterator can be preserved across (some) modifications
  // of the hash map.
  //
  // TODO fix the duplicated code that results.

  datatype IteratorOutput<V> = Next(key: uint64) | Done

  datatype Iterator<V> = Iterator(
    i: uint64, // index in hash table item list
    ghost s: set<uint64>,   // set of values returned so far
    ghost decreaser: ORDINAL,
    next: IteratorOutput)

  datatype SimpleIterator = SimpleIterator(
    i: uint64, // index in hash table item list
    ghost s: set<uint64>,   // set of values returned so far
    ghost decreaser: ORDINAL)

  predicate NextExplainedByI<V>(self: LinearHashMap<V>, i : uint64, output:IteratorOutput)
  {
    && (output.Next? ==>
      && i as int < |self.underlying.storage|
      && self.underlying.storage[i as nat].Entry?
      && self.underlying.storage[i as nat].key == output.key)
    && (output.Done? ==> i as int == |self.underlying.storage|)
  }

  predicate ValidI<V>(self: LinearHashMap<V>, it: Iterator<V>)
  {
    && 0 <= it.i as int <= |self.underlying.storage|
  }

  predicate EachReturnedKeyExplainedByPassedIndex<V>(self: LinearHashMap<V>, s: set<uint64>, i: uint64)
  requires 0 <= i as int <= |self.underlying.storage|
  {
    forall key | key in s ::
        exists j | 0 <= j < i as int ::
        && self.underlying.storage[j].Entry?
        && key == self.underlying.storage[j].key
  }

  protected predicate WFIter<V>(self: LinearHashMap<V>, it: Iterator<V>)
  ensures WFIter(self, it) ==> (it.next.Done? ==> it.s == self.contents.Keys)
  ensures WFIter(self, it) ==> (it.next.Next? ==> it.next.key in self.contents)
  ensures WFIter(self, it) ==> (it.next.Next? ==> it.next.key !in it.s)
  ensures WFIter(self, it) ==> it.s <= self.contents.Keys
  {
    && ValidI(self, it)
    && NextExplainedByI(self, it.i, it.next)
    // Done justified by exhausting i
    && (it.next.Done? ==> (it.s == self.contents.Keys))
    // Each passed index appears in s
    && (forall j | 0 <= j < it.i as int ::
        self.underlying.storage[j].Entry? ==> self.underlying.storage[j].key in it.s)
    && EachReturnedKeyExplainedByPassedIndex(self, it.s, it.i)
    && it.decreaser == (|self.underlying.storage| - it.i as int) as ORDINAL
    && (it.next.Next? ==> it.next.key in self.contents)
    && (it.next.Next? ==> it.next.key !in it.s)
    && it.s <= self.contents.Keys
  }

  protected predicate WFSimpleIter<V>(self: LinearHashMap<V>, it: SimpleIterator)
  ensures WFSimpleIter(self, it) ==> it.s <= self.contents.Keys
  {
    && 0 <= it.i as int <= |self.underlying.storage| < Uint64UpperBound()
    && (it.i as int == |self.underlying.storage| ==> (it.s == self.contents.Keys))
    && (it.i as int < |self.underlying.storage| ==> self.underlying.storage[it.i as nat].Entry?)
    // Each passed index appears in s
    && (forall j | 0 <= j < it.i as int ::
        self.underlying.storage[j].Entry? ==> self.underlying.storage[j].key in it.s)
    && EachReturnedKeyExplainedByPassedIndex(self, it.s, it.i)
    && it.decreaser == (|self.underlying.storage| - it.i as int) as ORDINAL
    && (it.i as int < |self.underlying.storage| ==> (
      && self.underlying.storage[it.i as nat].key in self.contents
      && self.underlying.storage[it.i as nat].key !in it.s
    ))
    && it.s <= self.contents.Keys
  }

  function method indexOutput<V>(shared self: LinearHashMap<V>, i: uint64) : (next: IteratorOutput<V>)
  requires Inv(self)
  requires 0 <= i as int <= |self.underlying.storage| < Uint64UpperBound()
  requires i as int < |self.underlying.storage| ==> self.underlying.storage[i as nat].Entry?
  {
    if i == lseq_length_as_uint64(self.underlying.storage) then (
      Done
    ) else (
      Next(lseq_peek(self.underlying.storage, i).key)
    )
  }

  protected function method SimpleIterOutput<V>(shared self: LinearHashMap<V>, it: SimpleIterator) : (next: IteratorOutput<V>)
  requires Inv(self)
  requires WFSimpleIter(self, it)
  ensures (next.Done? ==> it.s == self.contents.Keys)
  ensures (next.Next? ==> next.key in self.contents)
  ensures (next.Next? ==> next.key !in it.s)
  {
    indexOutput(self, it.i)
  }

  lemma LemmaWFIterImpliesILt<V>(self: LinearHashMap<V>, it: Iterator<V>)
  requires WFIter(self, it)
  ensures it.next.Next? ==> it.i as int < |self.underlying.storage|
  {
  }

  lemma LemmaWFSimpleIterImpliesEntry<V>(self: LinearHashMap<V>, it: SimpleIterator)
  requires Inv(self)
  requires WFSimpleIter(self, it)
  ensures
    && 0 <= it.i as int <= |self.underlying.storage|
    && (SimpleIterOutput(self, it).Next? ==> it.i as int < |self.underlying.storage|)
    && (it.i as int < |self.underlying.storage| ==>
      && self.underlying.storage[it.i as nat].Entry?
    )
  {
  }

  lemma LemmaIterNextNotInS<V>(self: LinearHashMap<V>, it: Iterator<V>)
  requires 0 <= it.i as int <= |self.underlying.storage|
  requires ValidElements(toItems(self.underlying.storage))
  requires CantEquivocateStorageKey(toItems(self.underlying.storage))
  requires NextExplainedByI(self, it.i, it.next)
  requires EachReturnedKeyExplainedByPassedIndex(self, it.s, it.i)
  ensures (it.next.Next? ==> it.next.key !in it.s)
  {
    if it.next.Next? {
      if it.next.key in it.s {
        var j :| 0 <= j < it.i as int
          && self.underlying.storage[j].Entry?
          && it.next.key == self.underlying.storage[j].key;
        assert TwoNonEmptyValidSlotsWithSameKey<V>(toItems(self.underlying.storage), Slot(it.i as int), Slot(j));  // trigger
        assert false; // proof by contradiction
      }
    }
  }

  function method iterToNext<V>(shared self: LinearHashMap<V>, i: uint64) : (res: (uint64, IteratorOutput))
  requires Inv(self)
  requires 0 <= i as int <= |self.underlying.storage|
  ensures NextExplainedByI(self, res.0, res.1)
  ensures forall j | i <= j < res.0 :: !self.underlying.storage[j as nat].Entry?
  ensures i <= res.0
  decreases |self.underlying.storage| - i as int
  {
    if i == lseq_length_as_uint64(self.underlying.storage) then (
      (i, Done)
    ) else if lseq_peek(self.underlying.storage, i).Entry? then (
      (i, Next(lseq_peek(self.underlying.storage, i).key))
    ) else (
      iterToNext(self, i+1)
    )
  }

  function method simpleIterToNext<V>(shared self: LinearHashMap<V>, i: uint64) : (i': uint64)
  requires Inv(self)
  requires 0 <= i as int <= |self.underlying.storage|
  ensures 0 <= i' as int <= |self.underlying.storage|
  ensures forall j | i <= j < i' :: !self.underlying.storage[j as nat].Entry?
  ensures i' as int < |self.underlying.storage| ==>
      self.underlying.storage[i' as nat].Entry?
  ensures i <= i'
  decreases |self.underlying.storage| - i as int
  {
    if i == lseq_length_as_uint64(self.underlying.storage) then (
      i
    ) else if lseq_peek(self.underlying.storage, i).Entry? then (
      i
    ) else (
      simpleIterToNext(self, i+1)
    )
  }

  lemma lemmaIterToNextValidKey<V>(self: LinearHashMap<V>, i: uint64)
  requires Inv(self)
  requires 0 <= i as int <= |self.underlying.storage|
  ensures iterToNext(self, i).1.Next? ==> iterToNext(self, i).1.key in self.contents
  {
    var j := iterToNext(self, i).0;
    var next := iterToNext(self, i).1;
    if next.Next? {
      UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents);
      CantEquivocateMapFromStorageKey(self.underlying);
      MapFromStorageProperties(toItems(self.underlying.storage), self.contents);
      assert self.underlying.storage[Slot(j as int).slot].key == next.key; // trigger
    }
  }

  function method {:opaque} IterStart<V>(shared self: LinearHashMap<V>) : (it' : Iterator<V>)
  requires Inv(self)
  ensures WFIter(self, it')
  ensures it'.s == {}
  {
    lemmaIterToNextValidKey(self, 0);

    var (i, next) := iterToNext(self, 0);
    var it' := Iterator(i, {}, (|self.underlying.storage| - i as int) as ORDINAL, next);

    LemmaIterNextNotInS(self, it');

    it'
  }

  function method {:opaque} SimpleIterStart<V>(shared self: LinearHashMap<V>) : (it' : SimpleIterator)
  requires Inv(self)
  ensures WFSimpleIter(self, it')
  ensures it'.s == {}
  {
    lemmaIterToNextValidKey(self, 0);

    var i := simpleIterToNext(self, 0);
    var it' := SimpleIterator(i, {}, (|self.underlying.storage| - i as int) as ORDINAL);

    LemmaIterNextNotInS(self,
      Iterator(it'.i, it'.s, it'.decreaser, indexOutput(self, it'.i)));

    it'
  }

  function method {:opaque} IterInc<V>(shared self: LinearHashMap<V>, it: Iterator) : (it' : Iterator)
  requires Inv(self)
  requires WFIter(self, it)
  requires it.next.Next?
  ensures WFIter(self, it')
  ensures it'.s == it.s + {it.next.key}
  ensures it'.next.Done? ==> it'.s == self.contents.Keys
  ensures it'.decreaser < it.decreaser
  {
    lemmaIterToNextValidKey(self, it.i + 1);

    var (i, next) := iterToNext(self, it.i + 1);
    var it' := Iterator(i, it.s + {it.next.key}, (|self.underlying.storage| - i as int) as ORDINAL, next);

    assert (forall key | key in it'.s ::
        exists j | 0 <= j < it'.i as int ::
        && self.underlying.storage[j].Entry?
        && key == self.underlying.storage[j].key);
    assert (it'.next.Done? ==> it'.s == self.contents.Keys);

    LemmaIterNextNotInS(self, it');

    it'
  }

  function method {:opaque} SimpleIterInc<V>(shared self: LinearHashMap<V>, it: SimpleIterator) : (it' : SimpleIterator)
  requires Inv(self)
  requires WFSimpleIter(self, it)
  requires SimpleIterOutput(self, it).Next?
  ensures WFSimpleIter(self, it')
  ensures it'.s == it.s + {SimpleIterOutput(self, it).key}
  ensures it'.decreaser < it.decreaser
  {
    lemmaIterToNextValidKey(self, it.i + 1);

    var i := simpleIterToNext(self, it.i + 1);
    var it' := SimpleIterator(i, it.s + {SimpleIterOutput(self, it).key}, (|self.underlying.storage| - i as int) as ORDINAL);

    assert (forall key | key in it'.s ::
        exists j | 0 <= j < it'.i as int ::
        && self.underlying.storage[j].Entry?
        && key == self.underlying.storage[j].key);

    LemmaIterNextNotInS(self,
      Iterator(it'.i, it'.s, it'.decreaser, indexOutput(self, it'.i)));

    it'
  }

  lemma LemmaIterIndexLtCount<V>(self: LinearHashMap<V>, it: Iterator<V>)
  requires Inv(self)
  requires WFIter(self, it)
  ensures it.next.Next? ==> |it.s| < self.count as int
  {
    if it.next.Next? {
      ProperSubsetImpliesSmallerCardinality(it.s, self.contents.Keys);
    }
  }

  function method MaxKeyIterate<V>(shared self: LinearHashMap<V>, it: Iterator<V>, m: uint64) : (res : uint64)
  requires Inv(self)
  requires WFIter(self, it)
  requires forall key | key in it.s :: key <= m
  ensures forall key | key in self.contents :: key <= res
  decreases it.decreaser
  {
    if it.next.Done? then (
      m
    ) else (
      var key := it.next.key;
      MaxKeyIterate(self, IterInc(self, it), if m < key then key else m)
    )
  }

  function method {:opaque} MaxKey<V>(shared self: LinearHashMap<V>) : (res : uint64)
  requires Inv(self)
  ensures forall key | key in self.contents :: key <= res
  {
    MaxKeyIterate(self, IterStart(self), 0)    
  }

  predicate IsUpdateByIter<V>(self: LinearHashMap<V>, it: SimpleIterator, value: V, 
    self': LinearHashMap<V>, replaced: V)
  requires Inv(self)
  requires WFSimpleIter(self, it)
  requires SimpleIterOutput(self, it).Next?
  {
    && self.count == self'.count
    && self'.contents == self.contents[SimpleIterOutput(self, it).key := value]
    && IsFixedSizeUpdateBySlot(self.underlying, it.i, value, self'.underlying, replaced)
  }

  method UpdateByIter<V>(linear inout self: LinearHashMap<V>, it: SimpleIterator, linear value: V) 
  returns (linear replaced: V)
  requires Inv(old_self)
  requires WFSimpleIter(old_self, it)
  requires SimpleIterOutput(old_self, it).Next?
  ensures Inv(self)
  ensures self.contents == old_self.contents[SimpleIterOutput(old_self, it).key := value]
  ensures self.count == old_self.count
  ensures IsUpdateByIter(old_self, it, value, self, replaced)
  {
    inout ghost self.contents := self.contents[SimpleIterOutput(self, it).key := value];
    replaced := FixedSizeUpdateBySlot(inout self.underlying, it.i, value);

    UnderlyingInvImpliesMapFromStorageMatchesContents(self.underlying, self.contents);
  }

  function setUpTo<V>(self: LinearHashMap<V>, i: int) : set<uint64>
  requires 0 <= i <= |self.underlying.storage|
  {
    set j | 0 <= j < i && self.underlying.storage[j].Entry?
        :: self.underlying.storage[j].key
  }

  lemma setUpToLeContents<V>(self: LinearHashMap<V>, i: int)
  requires Inv(self)
  requires 0 <= i <= |self.underlying.storage|
  ensures setUpTo(self, i) <= self.contents.Keys
  {
    forall j | 0 <= j < i && self.underlying.storage[j].Entry?
    ensures self.underlying.storage[j].key in self.contents
    {
      var key := self.underlying.storage[j].key;
      var slot := Slot(j);
      assert ValidSlot(|self.underlying.storage|, slot);
      CantEquivocateMapFromStorageKey(self.underlying);
      MapFromStorageProperties(toItems(self.underlying.storage), self.contents);
    }
  }

  function method {:opaque} FindSimpleIter<V>(shared self: LinearHashMap<V>, key: uint64)
    : (it : SimpleIterator)
  requires Inv(self)
  ensures WFSimpleIter(self, it)
  ensures key in self.contents ==> SimpleIterOutput(self, it) == Next(key)
  ensures key !in self.contents ==> SimpleIterOutput(self, it) == Done
  {
    var idx := Probe(self.underlying, key);

    var i := if lseq_peek(self.underlying.storage, idx).Entry? then idx
      else lseq_length_as_uint64(self.underlying.storage) as uint64;
    var it := SimpleIterator(i, setUpTo(self, i as int), (|self.underlying.storage| - i as int) as ORDINAL);

    assert WFSimpleIter(self, it)
      && (key in self.contents ==>
        SimpleIterOutput(self, it) == Next(key))
      && (key !in self.contents ==>
        SimpleIterOutput(self, it) == Done)
    by {
      var result := LemmaProbeResult(self.underlying, key);
      if it.i as int < |self.underlying.storage| {
        if self.underlying.storage[it.i as nat].key in it.s {
          var j :| 0 <= j < it.i && self.underlying.storage[j as nat].Entry?
              && self.underlying.storage[j as nat].key == key;
          assert TwoNonEmptyValidSlotsWithSameKey(
              toItems(self.underlying.storage), Slot(j as int), Slot(it.i as int));
        }
      }
      setUpToLeContents(self, i as int);
    }
  
    it
  }
}
