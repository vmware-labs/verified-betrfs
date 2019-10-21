include "../lib/Bitmap.i.dfy"
include "Bounds.i.dfy"

module BlockAllocator {
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
  {
    bam
      .(ephemeral := Bitmap.BitSet(bam.ephemeral, i))
      .(full := Bitmap.BitSet(bam.full, i))
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
      Bitmap.Union(bam.ephemeral, bam.frozen.value)
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
