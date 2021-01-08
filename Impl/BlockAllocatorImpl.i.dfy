include "../lib/Base/DebugAccumulator.i.dfy"
include "BlockAllocatorModel.i.dfy"
include "../lib/DataStructures/BitmapImpl.i.dfy"
include "../lib/Base/LinearOption.i.dfy"
//
// A BlockAllocator tracks which blocks are allocated, to safely allocate
// blocks unused by any view.
//

module BlockAllocatorImpl {
  import DebugAccumulator
  import BitmapModel
  import BitmapImpl
  import opened Bounds
  import opened LinearOption
  import opened Options
  import BlockAllocatorModel
  import opened NativeTypes

  linear datatype BlockAllocator = BlockAllocator(
    linear ephemeral: BitmapImpl.Bitmap,
    linear frozen: lOption <BitmapImpl.Bitmap>,
    linear persistent: BitmapImpl.Bitmap,
    linear outstanding: BitmapImpl.Bitmap,
    linear full: BitmapImpl.Bitmap
  )

  { 
    shared method DebugAccumulate()
    returns (acc:DebugAccumulator.DebugAccumulator)
    requires false
    {
      acc := DebugAccumulator.EmptyAccumulator();
      var r := ephemeral.DebugAccumulate();
      var a := new DebugAccumulator.AccRec.Index(r);
      acc := DebugAccumulator.AccPut(acc, "ephemeral", a);
      if frozen.lSome?{
        r := frozen.value.DebugAccumulate();
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

    protected predicate Inv()
    {
      && ephemeral.Inv()
      && (frozen.lSome? ==> frozen.value.Inv())
      && persistent.Inv()
      && outstanding.Inv()
      && full.Inv()
      && BitmapModel.Len(ephemeral.I()) == NumBlocks()
      && (frozen.lSome? ==> BitmapModel.Len(frozen.value.I()) == NumBlocks())
      && BitmapModel.Len(persistent.I()) == NumBlocks()
      && BitmapModel.Len(outstanding.I()) == NumBlocks()
      && BitmapModel.Len(full.I()) == NumBlocks()
    }

    protected function I() : BlockAllocatorModel.BlockAllocatorModel
    requires Inv()
    {
      BlockAllocatorModel.BlockAllocatorModel(ephemeral.I(),
          (if frozen.lNone? then None else Some(frozen.value.I())),
          persistent.I(),
          outstanding.I(),
          full.I())
    }

    //TODO Review this, mainly the linear bm for the input?
    static method Constructor(linear bm: BitmapImpl.Bitmap) returns (linear ba: BlockAllocator)
    requires bm.Inv()
    requires BitmapModel.Len(bm.I()) == NumBlocks()
    ensures ba.Inv()
    ensures ba.I() == BlockAllocatorModel.InitBlockAllocator(bm.I())
    {
      linear var per := BitmapImpl.Bitmap.CloneConstructor(bm);
      linear var out := BitmapImpl.Bitmap.Constructor(NumBlocksUint64());
      linear var ful := BitmapImpl.Bitmap.CloneConstructor(bm);

      ba := BlockAllocator(
        bm,
        lNone,
        per,
        out,
        ful
      );
    }
    

    shared method Alloc() returns (res : Option<uint64>)
    requires Inv()
    ensures res.Some? <==> BlockAllocatorModel.Alloc(I()).Some?
    ensures res.Some? ==> res.value as int == BlockAllocatorModel.Alloc(I()).value
    {
      res := full.Alloc();
    }
  
    linear inout method MarkUsedEphemeral(i: uint64)
    requires old_self.Inv()
    requires BlockAllocatorModel.Inv(old_self.I())
    requires i as int < NumBlocks()
    ensures self.Inv()
    ensures self.I() == BlockAllocatorModel.MarkUsedEphemeral(old_self.I(), i as int)
    {
      inout self.ephemeral.Set(i);
      inout self.full.Set(i);
    }

    //TODO why is the requires for frozen a Option not loption
    //why was frozen.Set done originally?
    linear inout method MarkUsedFrozen(i: uint64)
    requires old_self.Inv()
    requires BlockAllocatorModel.Inv(old_self.I())
    requires i as int < NumBlocks()
    requires old_self.I().frozen.Some?
    ensures self.Inv()
    ensures self.I() == BlockAllocatorModel.MarkUsedFrozen(old_self.I(), i as int)
    {
      inout self.frozen.value.Set(i);
      inout self.full.Set(i);
    }

    linear inout method MarkUsedOutstanding(i: uint64)
    requires old_self.Inv()
    requires BlockAllocatorModel.Inv(old_self.I())
    requires i as int < NumBlocks()
    ensures self.Inv()
    ensures self.I() == BlockAllocatorModel.MarkUsedOutstanding(old_self.I(), i as int)
    {
      inout self.outstanding.Set(i);
      inout self.full.Set(i);
    }

    linear inout method MarkFreeOutstanding(i: uint64)
    requires old_self.Inv()
    requires BlockAllocatorModel.Inv(old_self.I())
    requires i as int < NumBlocks()
    ensures self.Inv()
    ensures self.I() == BlockAllocatorModel.MarkFreeOutstanding(old_self.I(), i as int)
    {
      inout self.outstanding.Unset(i);

      var b0 := false;
      if self.frozen.lSome?{
        b0 := self.frozen.value.GetIsSet(i);
      }
      if !b0 {
        var b1 := self.ephemeral.GetIsSet(i);
        if !b1 {
          var b2 := self.persistent.GetIsSet(i);
          if !b2 {
           inout self.full.Unset(i);
          }
        }
      }

      BitmapModel.reveal_BitUnset();
      BitmapModel.reveal_IsSet();

      assert self.Inv();
    }

    linear inout method MarkFreeEphemeral(i: uint64)
    requires old_self.Inv()
    requires BlockAllocatorModel.Inv(old_self.I())
    requires i as int < NumBlocks()
    ensures self.Inv()
    ensures self.I() == BlockAllocatorModel.MarkFreeEphemeral(old_self.I(), i as int)
    {
      inout self.ephemeral.Unset(i);

      var b0 := false;
      if self.frozen.lSome?{
        b0 := self.frozen.value.GetIsSet(i);
      }
      if !b0 {
        var b1 := self.outstanding.GetIsSet(i);
        if !b1 {
          var b2 := self.persistent.GetIsSet(i);
          if !b2 {
            inout self.full.Unset(i);
          }
        }
      }

      BitmapModel.reveal_BitUnset();
      BitmapModel.reveal_IsSet();

      assert forall j | 0 <= j < |self.ephemeral.I()| :: j != i as int 
      ==> BitmapModel.IsSet(self.ephemeral.I(), j) == BitmapModel.IsSet(old_self.ephemeral.I(), j);

      assert self.Inv();
    }

    linear method MoveFrozenToPersistent() returns (linear ba : BlockAllocator)
    requires this.Inv()
    requires BlockAllocatorModel.Inv(this.I())
    requires this.I().frozen.Some?
    ensures ba.Inv()
    ensures ba.I() == BlockAllocatorModel.MoveFrozenToPersistent(old(I()))
    {
      linear var BlockAllocator(eph, fro, pre, out, full) := this;

      linear var frozen_val := unwrap_value(fro);

      linear var fo := BitmapImpl.Bitmap.UnionConstructor(frozen_val, out);
      linear var fu := BitmapImpl.Bitmap.UnionConstructor(eph, fo);

      ba := BlockAllocator(
        eph, lNone, frozen_val, out, fu
      );

      pre.Free();
      full.Free();
      fo.Free();
    }
/*
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
*/
  }
}
