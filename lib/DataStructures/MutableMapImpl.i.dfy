include "../Base/NativeTypes.s.dfy"
include "../Base/NativeArrays.s.dfy"
include "../Base/Option.s.dfy"
include "../Base/sequences.i.dfy"
include "../Base/Sets.i.dfy"
include "../Base/SetBijectivity.i.dfy"
include "MutableMapModel.i.dfy"
//
// A map implemented as a fast, mutable hash table.
//

module MutableMap {
  import opened NativeTypes
  import opened Options
  import opened Sequences
  import opened Sets
  import opened SetBijectivity
  import NativeArrays
  import opened MutableMapModel

  // TODO having a separate FixedSizeHashMap isn't really necessary;
  // things might be clearer if we just combine them.

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
      Storage := NativeArrays.newArrayFill(size, Empty);
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
      var h := MutableMapModel.hash64(key);
      result := h % (Storage.Length as uint64);
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
      this.Storage[slotIdx] := Entry(key, value);

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
      var newStorage := NativeArrays.newArrayClone(this.Storage);
      cloned := new FixedSizeHashMap.FromStorage(newStorage, Count);
      cloned.Contents := Contents;
      /* (doc) assert cloned.Repr !! Repr; */
      assert Storage[..] == cloned.Storage[..]; // observe
    }

    method UpdateBySlot(slotIdx: uint64, v: V)
      requires WF()
      requires Inv()
      requires 0 <= slotIdx as int < this.Storage.Length
      requires this.Storage[slotIdx].Entry?
      modifies Repr
      ensures WF()
      ensures Inv()
      ensures Repr == old(Repr)
      ensures ModelI(this) == FixedSizeUpdateBySlot(old(ModelI(this)), slotIdx, v)
    {
      FixedSizeUpdateBySlotResult(ModelI(this), slotIdx, v);

      Contents := Contents[Storage[slotIdx].key := Some(v)];
      Storage[slotIdx] := Entry(Storage[slotIdx].key, v);
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

    protected static function ModelI(self: ResizingHashMap<V>): (model: LinearHashMap<V>)
    requires self.ReprInv()
    ensures model.contents == self.Contents
    reads self, self.Repr
    {
      MutableMapModel.LinearHashMap(
          FixedSizeHashMap.ModelI(self.Underlying), self.Count, self.Contents)
    }

    protected predicate Inv()
      ensures Inv() ==> this in this.Repr
      ensures Inv() ==> |Contents| == Count as nat
      reads this, this.Repr
    {
      && ReprInv()

      && Underlying.WF()
      && Underlying.Inv()
      && MutableMapModel.Inv(ModelI(this))
    }

    protected function I() : MutableMapModel.LinearHashMap<V>
      reads this, this.Repr
      requires Inv()
      ensures MutableMapModel.Inv(I())
      ensures this.I().count == Count

      // TODO users of this class should just use I().contents,
      // which would make this unnecessary
      ensures this.I().contents == Contents
    {
      ModelI(this)
    }

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

    constructor FromUnderlying(underlying: FixedSizeHashMap<V>, count: uint64)
      requires 128 <= underlying.Storage.Length
      requires underlying.WF()
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

    method Realloc()
      requires Count as nat < 0x10000000000000000 / 8
      requires Inv()
      ensures Inv()
      ensures Contents == old(Contents)
      ensures Underlying.Count as nat < Underlying.Storage.Length - 2
      ensures fresh(Underlying)
      ensures fresh(Underlying.Storage)
      ensures forall r :: r in Repr ==> r in old(Repr) || fresh(r)
      ensures I() == MutableMapModel.Realloc(old(I()))
      modifies this
    {
      MutableMapModel.reveal_ReallocInternal();    
      var newSize: uint64 := (128 + Count) * 4;

      var newUnderlying := new FixedSizeHashMap(newSize);
      var i: uint64 := 0;

      while i < Underlying.Storage.Length as uint64
      invariant newUnderlying.WF();
      invariant newUnderlying.Inv();
      invariant 0 <= i as int <= Underlying.Storage.Length
      invariant Count as int < newUnderlying.Storage.Length - 1
      invariant newUnderlying.Contents.Keys <= Contents.Keys
      invariant Inv()
      invariant I() == old(I())
      invariant this.Repr == old(this.Repr)
      invariant fresh(newUnderlying)
      invariant fresh(newUnderlying.Storage)
      invariant MutableMapModel.ReallocIterate(I(), FixedSizeHashMap.ModelI(newUnderlying), i)
             == MutableMapModel.ReallocIterate(I(), MutableMapModel.ConstructorFromSize(newSize), 0)
      {
        var item := Underlying.Storage[i];
        if item.Entry? {
          SetInclusionImpliesSmallerCardinality(newUnderlying.Contents.Keys, Contents.Keys);
          MutableMapModel.LemmaFixedSizeInsertResult(FixedSizeHashMap.ModelI(newUnderlying), item.key, item.value);
          MutableMapModel.LemmaEntryKeyInContents(I(), i);

          var _ := newUnderlying.Insert(item.key, item.value);
        }
        i := i + 1;
      }

      this.Underlying := newUnderlying;

      this.Repr := { this, Underlying } + Underlying.Repr;

      MutableMapModel.LemmaReallocResult(old(I()));
    }

    method InsertAndGetOld(key: uint64, value: V) returns (replaced: Option<V>)
      requires Inv()
      requires Count as nat < 0x10000000000000000 / 8
      ensures Inv()
      ensures (I(), replaced) == MutableMapModel.InsertAndGetOld(old(I()), key, value)
      ensures forall r :: r in Repr ==> r in old(Repr) || fresh(r)
      modifies Repr
    {
      MutableMapModel.reveal_InsertAndGetOld();

      if Underlying.Storage.Length as uint64 / 2 <= Underlying.Count {
        Realloc();
      }

      replaced := Underlying.Insert(key, value);
      Contents := Contents[key := value];

      if replaced.None? {
        Count := Count + 1;
      }

      this.Repr := { this, this.Underlying } + this.Underlying.Repr;
      ghost var _ := MutableMapModel.InsertAndGetOld(old(I()), key, value);
    }

    method Insert(key: uint64, value: V)
      requires Inv()
      requires Count as nat < 0x1_0000_0000_0000_0000 / 8
      ensures Inv()
      ensures I() == MutableMapModel.Insert(old(I()), key, value)
      ensures forall r :: r in Repr ==> r in old(Repr) || fresh(r)
      modifies Repr
    {
      MutableMapModel.reveal_Insert();
      var _ := InsertAndGetOld(key, value);
    }

    method RemoveAndGet(key: uint64) returns (removed: Option<V>)
      requires Inv()
      ensures Inv()
      ensures (I(), removed) == MutableMapModel.RemoveAndGet(old(I()), key)
      ensures Repr == old(Repr)
      modifies Repr
    {
      // -- mutation --
      removed := Underlying.Remove(key);
      // assert Contents == old(Contents);
      Contents := map k | k in Contents && k != key :: Contents[k];

      if removed.Some? {
        RevealProtectedInv(old(I()));
        LemmaFixedSizeRemoveResult(old(I().underlying), key);
        Count := Count - 1;
      }
      // --------------

      ghost var _ := MutableMapModel.RemoveAndGet(old(I()), key);
    }

    method Remove(key: uint64)
      requires Inv()
      ensures Inv()
      ensures I() == MutableMapModel.Remove(old(I()), key)
      ensures Repr == old(Repr)
      modifies Repr
    {
      // -- mutation --
      var _ := RemoveAndGet(key);
      // --------------
    }

    method Get(key: uint64) returns (found: Option<V>)
      requires Inv()
      ensures Inv()
      ensures found == MutableMapModel.Get(old(I()), key)
    {
      found := Underlying.Get(key);
    }
    
    method Clone() returns (cloned: ResizingHashMap<V>)
      requires Inv()
      ensures cloned.Inv()
      ensures cloned.I() == old(I())
      ensures fresh(cloned.Repr)
    {
      var clonedUnderlying := Underlying.Clone();
      cloned := new ResizingHashMap.FromUnderlying(clonedUnderlying, Count);
      cloned.Contents := Contents;
    }

    method IterStart() returns (it' : Iterator<V>)
    requires Inv()
    ensures it' == MutableMapModel.IterStart(I())
    {
      ghost var self := I();
      reveal_IterStart();

      var i: uint64 := 0;
      while i < Underlying.Storage.Length as uint64
      invariant 0 <= i as int <= |self.underlying.storage|
      invariant iterToNext(self, 0) == iterToNext(self, i)
      {
        if Underlying.Storage[i].Entry? {
          var next := Next(Underlying.Storage[i].key, Underlying.Storage[i].value);
          it' := Iterator(i, {}, (|self.underlying.storage| - i as int) as ORDINAL, next);
          return;
        }
        i := i + 1;
      }

      var next := Done;
      it' := Iterator(i, {}, (|self.underlying.storage| - i as int) as ORDINAL, next);
    }

    method IterInc(it: Iterator<V>) returns (it' : Iterator<V>)
    requires Inv()
    requires it.next.Next?
    requires WFIter(I(), it)
    ensures it' == MutableMapModel.IterInc(I(), it)
    {
      ghost var self := I();
      reveal_IterInc();

      LemmaWFIterImpliesILt(self, it);

      var i: uint64 := it.i + 1;
      while i < Underlying.Storage.Length as uint64
      invariant 0 <= i as int <= |self.underlying.storage|
      invariant iterToNext(self, it.i + 1) == iterToNext(self, i)
      {
        if Underlying.Storage[i].Entry? {
          var next := Next(Underlying.Storage[i].key, Underlying.Storage[i].value);
          it' := Iterator(i, it.s + {it.next.key}, (|self.underlying.storage| - i as int) as ORDINAL, next);
          return;
        }
        i := i + 1;
      }

      var next := Done;
      it' := Iterator(i, it.s + {it.next.key}, (|self.underlying.storage| - i as int) as ORDINAL, next);
    }

    method MaxKey() returns (res : uint64)
    requires Inv()
    ensures res == MutableMapModel.MaxKey(I())
    {
      MutableMapModel.reveal_MaxKey();
      var it := IterStart();
      var m: uint64 := 0;
      while it.next.Next?
      invariant Inv()
      invariant MutableMapModel.WFIter(I(), it)
      invariant forall key | key in it.s :: key <= m
      invariant MutableMapModel.MaxKeyIterate(I(), it, m) == MutableMapModel.MaxKey(I())
      decreases it.decreaser
      {
        var key := it.next.key;
        if key > m {
          m := key;
        }
        it := IterInc(it);
      }
      return m;
    }

    method SimpleIterOutput(it: SimpleIterator)
    returns (next: IteratorOutput<V>)
    requires Inv()
    requires WFSimpleIter(I(), it)
    ensures next == MutableMapModel.SimpleIterOutput(I(), it)
    {
      LemmaWFSimpleIterImpliesEntry(I(), it);
      LemmaSimpleIterOutputReveal(I(), it);
      if it.i == this.Underlying.Storage.Length as uint64 {
        return Done;
      } else {
        return Next(
            this.Underlying.Storage[it.i].key,
            this.Underlying.Storage[it.i].value);
      }
    }

    method wtf()
    {
    }

    method SimpleIterStart() returns (it' : SimpleIterator)
    requires Inv()
    ensures it' == MutableMapModel.SimpleIterStart(I())
    {
      ghost var self := I();
      reveal_SimpleIterStart();

      var i: uint64 := 0;
      while i < Underlying.Storage.Length as uint64
      invariant 0 <= i as int <= |self.underlying.storage|
      invariant simpleIterToNext(self, 0) == simpleIterToNext(self, i)
      {
        if Underlying.Storage[i].Entry? {
          it' := SimpleIterator(i, {}, (|self.underlying.storage| - i as int) as ORDINAL);
          return;
        }
        i := i + 1;
      }

      it' := SimpleIterator(i, {}, (|self.underlying.storage| - i as int) as ORDINAL);
    }

    method SimpleIterInc(it: SimpleIterator) returns (it' : SimpleIterator)
    requires Inv()
    requires WFSimpleIter(I(), it)
    requires MutableMapModel.SimpleIterOutput(I(), it).Next?
    ensures it' == MutableMapModel.SimpleIterInc(I(), it)
    {
      ghost var self := I();
      reveal_SimpleIterInc();

      LemmaWFSimpleIterImpliesEntry(self, it);

      var i: uint64 := it.i + 1;
      while i < Underlying.Storage.Length as uint64
      invariant 0 <= i as int <= |self.underlying.storage|
      invariant simpleIterToNext(self, it.i + 1) == simpleIterToNext(self, i)
      {
        if Underlying.Storage[i].Entry? {
          it' := SimpleIterator(i, it.s + {MutableMapModel.SimpleIterOutput(old(I()), it).key}, (|self.underlying.storage| - i as int) as ORDINAL);
          return;
        }
        i := i + 1;
      }

      it' := SimpleIterator(i, it.s + {MutableMapModel.SimpleIterOutput(old(I()), it).key}, (|self.underlying.storage| - i as int) as ORDINAL);
    }

    method UpdateByIter(it: SimpleIterator, value: V)
    requires Inv()
    requires WFSimpleIter(I(), it)
    requires MutableMapModel.SimpleIterOutput(I(), it).Next?
    modifies Repr
    ensures Inv()
    ensures Repr == old(Repr)
    ensures I() == MutableMapModel.UpdateByIter(old(I()), it, value);
    {
      LemmaWFSimpleIterImpliesEntry(I(), it);
      MutableMapModel.reveal_UpdateByIter();
      FixedSizeUpdateBySlotResult(I().underlying, it.i, value);

      this.Underlying.UpdateBySlot(it.i, value);
      this.Contents := this.Contents[MutableMapModel.SimpleIterOutput(old(I()), it).key := value];

      assert ModelI(this)
        == MutableMapModel.UpdateByIter(old(I()), it, value);
    }

    method FindSimpleIter(key: uint64) returns (it : SimpleIterator)
    requires Inv()
    ensures it == MutableMapModel.FindSimpleIter(I(), key)
    {
      MutableMapModel.reveal_FindSimpleIter();
      var idx := this.Underlying.Probe(key);
      var i := if this.Underlying.Storage[idx].Entry?
        then idx
        else this.Underlying.Storage.Length as uint64;

      ghost var s := MutableMapModel.setUpTo(I(), i as int);

      return SimpleIterator(i, s, (|I().underlying.storage| - i as int) as ORDINAL);
    }
  }
}
