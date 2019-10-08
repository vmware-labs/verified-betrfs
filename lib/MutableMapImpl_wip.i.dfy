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
