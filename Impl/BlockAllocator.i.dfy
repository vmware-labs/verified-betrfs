include "../lib/DataStructures/Bitmap.i.dfy"
include "../treemodel/Bounds.i.dfy"
//
// A BlockAllocator tracks which blocks are allocated, to safely allocate
// blocks unused by any view.
//

// TODO these modules need better names. And we should probably do the
// one-module-per-file thing.

module ImplModelBlockAllocator {
  import Bitmap
  import opened Bounds
  import opened Options

  datatype BlockAllocatorModel = BlockAllocatorModel(
        ephemeral: Bitmap.BitmapModel,
        frozen: Option<Bitmap.BitmapModel>,
        persistent: Bitmap.BitmapModel,
        outstanding: Bitmap.BitmapModel,
        full: Bitmap.BitmapModel
      )

  predicate Inv(bam: BlockAllocatorModel) {
    && Bitmap.Len(bam.ephemeral) == NumBlocks()
    && (bam.frozen.Some? ==> Bitmap.Len(bam.frozen.value) == NumBlocks())
    && Bitmap.Len(bam.persistent) == NumBlocks()
    && Bitmap.Len(bam.outstanding) == NumBlocks()

    && Bitmap.Len(bam.full) == NumBlocks()
    && (forall i | 0 <= i < NumBlocks() ::
        Bitmap.IsSet(bam.full, i) == (
          || Bitmap.IsSet(bam.ephemeral, i)
          || (bam.frozen.Some? && Bitmap.IsSet(bam.frozen.value, i))
          || Bitmap.IsSet(bam.persistent, i)
          || Bitmap.IsSet(bam.full, i)
        ))
  }

  function Alloc(bam: BlockAllocatorModel) : (res: Option<int>)
  {
    Bitmap.BitAlloc(bam.full)
  }

  function MarkUsedEphemeral(bam: BlockAllocatorModel, i: int) : (bam': BlockAllocatorModel)
  requires Inv(bam)
  requires 0 <= i < NumBlocks()
  ensures Inv(bam')
  {
    var bam' := bam
      .(ephemeral := Bitmap.BitSet(bam.ephemeral, i))
      .(full := Bitmap.BitSet(bam.full, i));

    Bitmap.reveal_BitSet();
    Bitmap.reveal_IsSet();
    assert forall j | 0 <= j < |bam.ephemeral| :: j != i ==> Bitmap.IsSet(bam'.ephemeral, j) == Bitmap.IsSet(bam.ephemeral, j);

    bam'
  }

  function MarkUsedFrozen(bam: BlockAllocatorModel, i: int) : (bam': BlockAllocatorModel)
  requires Inv(bam)
  requires bam.frozen.Some?
  requires 0 <= i < NumBlocks()
  ensures Inv(bam')
  {
    var bam' := bam
      .(frozen := Some(Bitmap.BitSet(bam.frozen.value, i)))
      .(full := Bitmap.BitSet(bam.full, i));

    Bitmap.reveal_BitSet();
    Bitmap.reveal_IsSet();
    assert forall j | 0 <= j < |bam.ephemeral| :: j != i ==> Bitmap.IsSet(bam'.ephemeral, j) == Bitmap.IsSet(bam.ephemeral, j);

    bam'
  }

  function MarkUsedOutstanding(bam: BlockAllocatorModel, i: int) : (bam': BlockAllocatorModel)
  requires Inv(bam)
  requires 0 <= i < NumBlocks()
  ensures Inv(bam')
  {
    var bam' := bam
      .(outstanding := Bitmap.BitSet(bam.outstanding, i))
      .(full := Bitmap.BitSet(bam.full, i));

    Bitmap.reveal_BitSet();
    Bitmap.reveal_IsSet();
    assert forall j | 0 <= j < |bam.ephemeral| :: j != i ==> Bitmap.IsSet(bam'.ephemeral, j) == Bitmap.IsSet(bam.ephemeral, j);

    bam'
  }

  function InitBlockAllocator(bm: Bitmap.BitmapModel) : BlockAllocatorModel
  {
    var empty := Bitmap.EmptyBitmap(NumBlocks());
    BlockAllocatorModel(bm, None, bm, empty, bm)
  }

  function MarkFreeOutstanding(bam: BlockAllocatorModel, i: int) : (bam': BlockAllocatorModel)
  requires Inv(bam)
  requires 0 <= i < NumBlocks()
  {
    bam.(outstanding := Bitmap.BitUnset(bam.outstanding, i))
       .(full :=
        if
          && !Bitmap.IsSet(bam.ephemeral, i)
          && !Bitmap.IsSet(bam.persistent, i)
          && (bam.frozen.None? || !Bitmap.IsSet(bam.frozen.value, i))
        then
          Bitmap.BitUnset(bam.full, i)
        else
          bam.full)
  }

  function MarkFreeEphemeral(bam: BlockAllocatorModel, i: int) : (bam': BlockAllocatorModel)
  requires Inv(bam)
  requires 0 <= i < NumBlocks()
  {
    bam.(ephemeral := Bitmap.BitUnset(bam.ephemeral, i))
       .(full :=
        if
          && !Bitmap.IsSet(bam.outstanding, i)
          && !Bitmap.IsSet(bam.persistent, i)
          && (bam.frozen.None? || !Bitmap.IsSet(bam.frozen.value, i))
        then
          Bitmap.BitUnset(bam.full, i)
        else
          bam.full)
  }

  function MoveFrozenToPersistent(bam: BlockAllocatorModel) : (bam': BlockAllocatorModel)
  requires Inv(bam)
  requires bam.frozen.Some?
  {
    BlockAllocatorModel(
      bam.ephemeral,
      None,
      bam.frozen.value,
      bam.outstanding,
      Bitmap.BitUnion(bam.ephemeral, bam.frozen.value)
    )
  }

  function CopyEphemeralToFrozen(bam: BlockAllocatorModel) : (bam': BlockAllocatorModel)
  requires Inv(bam)
  {
    BlockAllocatorModel(
      bam.ephemeral,
      Some(bam.ephemeral),
      bam.persistent,
      bam.outstanding,
      bam.full
    )
  }

  // Lemmas

  lemma LemmaAllocResult(bam: BlockAllocatorModel)
  requires Inv(bam)
  ensures var res := Alloc(bam);
    && (res.Some? ==> !Bitmap.IsSet(bam.ephemeral, res.value))
    && (res.Some? && bam.frozen.Some? ==> !Bitmap.IsSet(bam.frozen.value, res.value))
    && (res.Some? ==> !Bitmap.IsSet(bam.persistent, res.value))
    && (res.Some? ==> !Bitmap.IsSet(bam.outstanding, res.value))
}

module ImplBlockAllocator {
  import Bitmap
  import opened Bounds
  import opened Options
  import ImplModelBlockAllocator
  import opened NativeTypes

  class BlockAllocator {
    var ephemeral: Bitmap.Bitmap;
    var frozen: Bitmap.Bitmap?;
    var persistent: Bitmap.Bitmap;
    var outstanding: Bitmap.Bitmap;
    var full: Bitmap.Bitmap;

    ghost var Repr: set<object>

    protected predicate Inv()
    reads this, Repr
    ensures Inv() ==> this in Repr
    {
      && this in Repr
      && ephemeral in Repr
      && (frozen != null ==> frozen in Repr)
      && persistent in Repr
      && outstanding in Repr
      && full in Repr
      && Repr == {this} + ephemeral.Repr + (if frozen == null then {} else frozen.Repr) + persistent.Repr + outstanding.Repr + full.Repr
      && {this} !! ephemeral.Repr !! (if frozen == null then {} else frozen.Repr) !! persistent.Repr !! outstanding.Repr !! full.Repr

      && ephemeral.Inv()
      && (frozen != null ==> frozen.Inv())
      && persistent.Inv()
      && outstanding.Inv()
      && full.Inv()
      && Bitmap.Len(ephemeral.I()) == NumBlocks()
      && (frozen != null ==> Bitmap.Len(frozen.I()) == NumBlocks())
      && Bitmap.Len(persistent.I()) == NumBlocks()
      && Bitmap.Len(outstanding.I()) == NumBlocks()
      && Bitmap.Len(full.I()) == NumBlocks()
    }

    protected function I() : ImplModelBlockAllocator.BlockAllocatorModel
    reads this, Repr
    requires Inv()
    {
      ImplModelBlockAllocator.BlockAllocatorModel(ephemeral.I(),
          (if frozen == null then None else Some(frozen.I())),
          persistent.I(),
          outstanding.I(),
          full.I())
    }

    constructor(bm: Bitmap.Bitmap)
    requires bm.Inv()
    requires Bitmap.Len(bm.I()) == NumBlocks()
    ensures Inv()
    ensures forall o | o in Repr :: fresh(o) || o in bm.Repr
    ensures I() == ImplModelBlockAllocator.InitBlockAllocator(bm.I())
    {
      ephemeral := bm;
      frozen := null;
      persistent := new Bitmap.Bitmap.Clone(bm);
      outstanding := new Bitmap.Bitmap(NumBlocksUint64());
      full := new Bitmap.Bitmap.Clone(bm);

      new;

      Repr := {this} + ephemeral.Repr + (if frozen == null then {} else frozen.Repr) + persistent.Repr + outstanding.Repr + full.Repr;
    }

    method Alloc() returns (res : Option<uint64>)
    requires Inv()
    ensures res.Some? <==> ImplModelBlockAllocator.Alloc(I()).Some?
    ensures res.Some? ==> res.value as int == ImplModelBlockAllocator.Alloc(I()).value
    {
      res := full.Alloc();
    }

    method MarkUsedEphemeral(i: uint64)
    requires Inv()
    requires ImplModelBlockAllocator.Inv(I())
    requires i as int < NumBlocks()
    modifies Repr
    ensures Inv()
    ensures Repr == old(Repr)
    ensures I() == ImplModelBlockAllocator.MarkUsedEphemeral(old(I()), i as int)
    {
      ephemeral.Set(i);
      full.Set(i);
    }

    method MarkUsedFrozen(i: uint64)
    requires Inv()
    requires ImplModelBlockAllocator.Inv(I())
    requires i as int < NumBlocks()
    requires I().frozen.Some?
    modifies Repr
    ensures Inv()
    ensures Repr == old(Repr)
    ensures I() == ImplModelBlockAllocator.MarkUsedFrozen(old(I()), i as int)
    {
      frozen.Set(i);
      full.Set(i);
    }

    method MarkUsedOutstanding(i: uint64)
    requires Inv()
    requires ImplModelBlockAllocator.Inv(I())
    requires i as int < NumBlocks()
    modifies Repr
    ensures Inv()
    ensures Repr == old(Repr)
    ensures I() == ImplModelBlockAllocator.MarkUsedOutstanding(old(I()), i as int)
    {
      outstanding.Set(i);
      full.Set(i);
    }

    method MarkFreeOutstanding(i: uint64)
    requires Inv()
    requires ImplModelBlockAllocator.Inv(I())
    requires i as int < NumBlocks()
    modifies Repr
    ensures Inv()
    ensures Repr == old(Repr)
    ensures I() == ImplModelBlockAllocator.MarkFreeOutstanding(old(I()), i as int)
    {
      outstanding.Unset(i);

      var b0 := false;
      if frozen != null {
        b0 := frozen.GetIsSet(i);
      }
      if !b0 {
        var b1 := ephemeral.GetIsSet(i);
        if !b1 {
          var b2 := persistent.GetIsSet(i);
          if !b2 {
            full.Unset(i);
          }
        }
      }

      Bitmap.reveal_BitUnset();
      Bitmap.reveal_IsSet();

      assert Inv();
    }

    method MarkFreeEphemeral(i: uint64)
    requires Inv()
    requires ImplModelBlockAllocator.Inv(I())
    requires i as int < NumBlocks()
    modifies Repr
    ensures Inv()
    ensures Repr == old(Repr)
    ensures I() == ImplModelBlockAllocator.MarkFreeEphemeral(old(I()), i as int)
    {
      ephemeral.Unset(i);

      var b0 := false;
      if frozen != null {
        b0 := frozen.GetIsSet(i);
      }
      if !b0 {
        var b1 := outstanding.GetIsSet(i);
        if !b1 {
          var b2 := persistent.GetIsSet(i);
          if !b2 {
            full.Unset(i);
          }
        }
      }

      Bitmap.reveal_BitUnset();
      Bitmap.reveal_IsSet();

      assert forall j | 0 <= j < |ephemeral.I()| :: j != i as int ==> Bitmap.IsSet(ephemeral.I(), j) == Bitmap.IsSet(old(ephemeral.I()), j);

      assert Inv();
    }

    method MoveFrozenToPersistent()
    requires Inv()
    requires ImplModelBlockAllocator.Inv(I())
    requires I().frozen.Some?
    modifies Repr
    ensures Inv()
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    ensures I() == ImplModelBlockAllocator.MoveFrozenToPersistent(old(I()))
    {
      persistent := frozen;
      frozen := null;
      full := new Bitmap.Bitmap.Union(ephemeral, persistent);

      Repr := {this} + ephemeral.Repr + (if frozen == null then {} else frozen.Repr) + persistent.Repr + outstanding.Repr + full.Repr;
    }

    method CopyEphemeralToFrozen()
    requires Inv()
    requires ImplModelBlockAllocator.Inv(I())
    modifies Repr
    ensures Inv()
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    ensures I() == ImplModelBlockAllocator.CopyEphemeralToFrozen(old(I()))
    {
      frozen := new Bitmap.Bitmap.Clone(ephemeral);

      Repr := {this} + ephemeral.Repr + (if frozen == null then {} else frozen.Repr) + persistent.Repr + outstanding.Repr + full.Repr;
    }

  }
}
