include "../lib/Base/DebugAccumulator.i.dfy"
include "BlockAllocatorModel.i.dfy"
include "../lib/DataStructures/BitmapImpl.i.dfy"
//
// A BlockAllocator tracks which blocks are allocated, to safely allocate
// blocks unused by any view.
//

module BlockAllocatorImpl {
  import DebugAccumulator
  import BitmapModel
  import BitmapImpl
  import opened Bounds
  import opened Options
  import BlockAllocatorModel
  import opened NativeTypes

  class BlockAllocator {
    var ephemeral: BitmapImpl.Bitmap;
    var frozen: BitmapImpl.Bitmap?;
    var persistent: BitmapImpl.Bitmap;
    var outstanding: BitmapImpl.Bitmap;
    var full: BitmapImpl.Bitmap;

    method DebugAccumulate()
    returns (acc:DebugAccumulator.DebugAccumulator)
    requires false
    {
      acc := DebugAccumulator.EmptyAccumulator();
      var r := ephemeral.DebugAccumulate();
      var a := new DebugAccumulator.AccRec.Index(r);
      acc := DebugAccumulator.AccPut(acc, "ephemeral", a);
      if frozen != null {
        r := frozen.DebugAccumulate();
      } else {
        r := DebugAccumulator.EmptyAccumulator();
      }
      a := new DebugAccumulator.AccRec.Index(r);
      acc := DebugAccumulator.AccPut(acc, "frozen", a);
      r := persistent.DebugAccumulate();
      a := new DebugAccumulator.AccRec.Index(r);
      acc := DebugAccumulator.AccPut(acc, "persistent", a);
      r := outstanding.DebugAccumulate();
      a := new DebugAccumulator.AccRec.Index(r);
      acc := DebugAccumulator.AccPut(acc, "outstanding", a);
      r := full.DebugAccumulate();
      a := new DebugAccumulator.AccRec.Index(r);
      acc := DebugAccumulator.AccPut(acc, "full", a);
    }

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
      && BitmapModel.Len(ephemeral.I()) == NumBlocks()
      && (frozen != null ==> BitmapModel.Len(frozen.I()) == NumBlocks())
      && BitmapModel.Len(persistent.I()) == NumBlocks()
      && BitmapModel.Len(outstanding.I()) == NumBlocks()
      && BitmapModel.Len(full.I()) == NumBlocks()
    }

    protected function I() : BlockAllocatorModel.BlockAllocatorModel
    reads this, Repr
    requires Inv()
    {
      BlockAllocatorModel.BlockAllocatorModel(ephemeral.I(),
          (if frozen == null then None else Some(frozen.I())),
          persistent.I(),
          outstanding.I(),
          full.I())
    }

    constructor(bm: BitmapImpl.Bitmap)
    requires bm.Inv()
    requires BitmapModel.Len(bm.I()) == NumBlocks()
    ensures Inv()
    ensures forall o | o in Repr :: fresh(o) || o in bm.Repr
    ensures I() == BlockAllocatorModel.InitBlockAllocator(bm.I())
    {
      ephemeral := bm;
      frozen := null;
      persistent := new BitmapImpl.Bitmap.Clone(bm);
      outstanding := new BitmapImpl.Bitmap(NumBlocksUint64());
      full := new BitmapImpl.Bitmap.Clone(bm);

      new;

      Repr := {this} + ephemeral.Repr + (if frozen == null then {} else frozen.Repr) + persistent.Repr + outstanding.Repr + full.Repr;
    }

    method Alloc() returns (res : Option<uint64>)
    requires Inv()
    ensures res.Some? <==> BlockAllocatorModel.Alloc(I()).Some?
    ensures res.Some? ==> res.value as int == BlockAllocatorModel.Alloc(I()).value
    {
      res := full.Alloc();
    }

    method MarkUsedEphemeral(i: uint64)
    requires Inv()
    requires BlockAllocatorModel.Inv(I())
    requires i as int < NumBlocks()
    modifies Repr
    ensures Inv()
    ensures Repr == old(Repr)
    ensures I() == BlockAllocatorModel.MarkUsedEphemeral(old(I()), i as int)
    {
      ephemeral.Set(i);
      full.Set(i);
    }

    method MarkUsedFrozen(i: uint64)
    requires Inv()
    requires BlockAllocatorModel.Inv(I())
    requires i as int < NumBlocks()
    requires I().frozen.Some?
    modifies Repr
    ensures Inv()
    ensures Repr == old(Repr)
    ensures I() == BlockAllocatorModel.MarkUsedFrozen(old(I()), i as int)
    {
      frozen.Set(i);
      full.Set(i);
    }

    method MarkUsedOutstanding(i: uint64)
    requires Inv()
    requires BlockAllocatorModel.Inv(I())
    requires i as int < NumBlocks()
    modifies Repr
    ensures Inv()
    ensures Repr == old(Repr)
    ensures I() == BlockAllocatorModel.MarkUsedOutstanding(old(I()), i as int)
    {
      outstanding.Set(i);
      full.Set(i);
    }

    method MarkFreeOutstanding(i: uint64)
    requires Inv()
    requires BlockAllocatorModel.Inv(I())
    requires i as int < NumBlocks()
    modifies Repr
    ensures Inv()
    ensures Repr == old(Repr)
    ensures I() == BlockAllocatorModel.MarkFreeOutstanding(old(I()), i as int)
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

      BitmapModel.reveal_BitUnset();
      BitmapModel.reveal_IsSet();

      assert Inv();
    }

    method MarkFreeEphemeral(i: uint64)
    requires Inv()
    requires BlockAllocatorModel.Inv(I())
    requires i as int < NumBlocks()
    modifies Repr
    ensures Inv()
    ensures Repr == old(Repr)
    ensures I() == BlockAllocatorModel.MarkFreeEphemeral(old(I()), i as int)
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

      BitmapModel.reveal_BitUnset();
      BitmapModel.reveal_IsSet();

      assert forall j | 0 <= j < |ephemeral.I()| :: j != i as int ==> BitmapModel.IsSet(ephemeral.I(), j) == BitmapModel.IsSet(old(ephemeral.I()), j);

      assert Inv();
    }

    method MoveFrozenToPersistent()
    requires Inv()
    requires BlockAllocatorModel.Inv(I())
    requires I().frozen.Some?
    modifies Repr
    ensures Inv()
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    ensures I() == BlockAllocatorModel.MoveFrozenToPersistent(old(I()))
    {
      var fo := new BitmapImpl.Bitmap.Union(frozen, outstanding);
      full := new BitmapImpl.Bitmap.Union(ephemeral, fo);
      persistent := frozen;
      frozen := null;

      Repr := {this} + ephemeral.Repr + (if frozen == null then {} else frozen.Repr) + persistent.Repr + outstanding.Repr + full.Repr;
    }

    method CopyEphemeralToFrozen()
    requires Inv()
    requires BlockAllocatorModel.Inv(I())
    modifies Repr
    ensures Inv()
    ensures forall o | o in Repr :: o in old(Repr) || fresh(o)
    ensures I() == BlockAllocatorModel.CopyEphemeralToFrozen(old(I()))
    {
      frozen := new BitmapImpl.Bitmap.Clone(ephemeral);

      Repr := {this} + ephemeral.Repr + (if frozen == null then {} else frozen.Repr) + persistent.Repr + outstanding.Repr + full.Repr;
    }

  }
}
