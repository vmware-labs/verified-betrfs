include "../lib/DataStructures/BitmapModel.i.dfy"
include "../PivotBetree/Bounds.i.dfy"
//
// A BlockAllocator tracks which blocks are allocated, to safely allocate
// blocks unused by any view.
//

module BlockAllocatorModel {
  import BitmapModel
  import opened Bounds
  import opened Options

  datatype BlockAllocatorModel = BlockAllocatorModel(
        ephemeral: BitmapModel.BitmapModelT,
        frozen: Option<BitmapModel.BitmapModelT>,
        persistent: BitmapModel.BitmapModelT,
        outstanding: BitmapModel.BitmapModelT,
        full: BitmapModel.BitmapModelT
      )

  predicate Inv(bam: BlockAllocatorModel) {
    && BitmapModel.Len(bam.ephemeral) == NumBlocks()
    && (bam.frozen.Some? ==> BitmapModel.Len(bam.frozen.value) == NumBlocks())
    && BitmapModel.Len(bam.persistent) == NumBlocks()
    && BitmapModel.Len(bam.outstanding) == NumBlocks()

    && BitmapModel.Len(bam.full) == NumBlocks()
    && (forall i | 0 <= i < NumBlocks() ::
        BitmapModel.IsSet(bam.full, i) == (
          || BitmapModel.IsSet(bam.ephemeral, i)
          || (bam.frozen.Some? && BitmapModel.IsSet(bam.frozen.value, i))
          || BitmapModel.IsSet(bam.persistent, i)
          || BitmapModel.IsSet(bam.outstanding, i)
        ))
  }

  function Alloc(bam: BlockAllocatorModel) : (res: Option<int>)
  {
    BitmapModel.BitAlloc(bam.full)
  }

  function MarkUsedEphemeral(bam: BlockAllocatorModel, i: int) : (bam': BlockAllocatorModel)
  requires Inv(bam)
  requires 0 <= i < NumBlocks()
  ensures Inv(bam')
  {
    var bam' := bam
      .(ephemeral := BitmapModel.BitSet(bam.ephemeral, i))
      .(full := BitmapModel.BitSet(bam.full, i));

    BitmapModel.reveal_BitSet();
    BitmapModel.reveal_IsSet();
    assert forall j | 0 <= j < |bam.ephemeral| :: j != i ==> BitmapModel.IsSet(bam'.ephemeral, j) == BitmapModel.IsSet(bam.ephemeral, j);

    bam'
  }

  function MarkUsedFrozen(bam: BlockAllocatorModel, i: int) : (bam': BlockAllocatorModel)
  requires Inv(bam)
  requires bam.frozen.Some?
  requires 0 <= i < NumBlocks()
  ensures Inv(bam')
  {
    var bam' := bam
      .(frozen := Some(BitmapModel.BitSet(bam.frozen.value, i)))
      .(full := BitmapModel.BitSet(bam.full, i));

    BitmapModel.reveal_BitSet();
    BitmapModel.reveal_IsSet();
    assert forall j | 0 <= j < |bam.ephemeral| :: j != i ==> BitmapModel.IsSet(bam'.ephemeral, j) == BitmapModel.IsSet(bam.ephemeral, j);

    bam'
  }

  function MarkUsedOutstanding(bam: BlockAllocatorModel, i: int) : (bam': BlockAllocatorModel)
  requires Inv(bam)
  requires 0 <= i < NumBlocks()
  ensures Inv(bam')
  {
    var bam' := bam
      .(outstanding := BitmapModel.BitSet(bam.outstanding, i))
      .(full := BitmapModel.BitSet(bam.full, i));

    BitmapModel.reveal_BitSet();
    BitmapModel.reveal_IsSet();
    assert forall j | 0 <= j < |bam.ephemeral| :: j != i ==> BitmapModel.IsSet(bam'.ephemeral, j) == BitmapModel.IsSet(bam.ephemeral, j);

    bam'
  }

  function InitBlockAllocator(bm: BitmapModel.BitmapModelT) : BlockAllocatorModel
  {
    var empty := BitmapModel.EmptyBitmap(NumBlocks());
    BlockAllocatorModel(bm, None, bm, empty, bm)
  }

  function MarkFreeOutstanding(bam: BlockAllocatorModel, i: int) : (bam': BlockAllocatorModel)
  requires Inv(bam)
  requires 0 <= i < NumBlocks()
  ensures Inv(bam')
  {
    BitmapModel.reveal_BitUnset();
    BitmapModel.reveal_IsSet();

    bam.(outstanding := BitmapModel.BitUnset(bam.outstanding, i))
       .(full :=
        if
          && !BitmapModel.IsSet(bam.ephemeral, i)
          && !BitmapModel.IsSet(bam.persistent, i)
          && (bam.frozen.None? || !BitmapModel.IsSet(bam.frozen.value, i))
        then
          BitmapModel.BitUnset(bam.full, i)
        else
          bam.full)
  }

  function MarkFreeEphemeral(bam: BlockAllocatorModel, i: int) : (bam': BlockAllocatorModel)
  requires Inv(bam)
  requires 0 <= i < NumBlocks()
  {
    bam.(ephemeral := BitmapModel.BitUnset(bam.ephemeral, i))
       .(full :=
        if
          && !BitmapModel.IsSet(bam.outstanding, i)
          && !BitmapModel.IsSet(bam.persistent, i)
          && (bam.frozen.None? || !BitmapModel.IsSet(bam.frozen.value, i))
        then
          BitmapModel.BitUnset(bam.full, i)
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
      BitmapModel.BitUnion(bam.ephemeral,
        BitmapModel.BitUnion(bam.frozen.value, bam.outstanding))
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
    && (res.Some? ==> !BitmapModel.IsSet(bam.ephemeral, res.value))
    && (res.Some? && bam.frozen.Some? ==> !BitmapModel.IsSet(bam.frozen.value, res.value))
    && (res.Some? ==> !BitmapModel.IsSet(bam.persistent, res.value))
    && (res.Some? ==> !BitmapModel.IsSet(bam.outstanding, res.value))
  {
    BitmapModel.LemmaBitAllocResult(bam.full);
    var res := Alloc(bam);
    if res.Some? {
      assert !BitmapModel.IsSet(bam.full, res.value);
    }
  }
}
