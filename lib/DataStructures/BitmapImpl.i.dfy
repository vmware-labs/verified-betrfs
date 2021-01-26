include "../Base/DebugAccumulator.i.dfy"
include "BitmapModel.i.dfy"
//
// Maintains a compact set of integers using a packed-uint64 bitmap
// representation.
//

module BitmapImpl {
  import DebugAccumulator
  import opened NativeTypes
  import opened Options
  import opened BitmapModel
  import NativeArrays
  import BitsetLemmas

  linear datatype Bitmap = Bitmap(
    bits: seq<uint64>
  )
  {
    shared method DebugAccumulate()
    returns (acc:DebugAccumulator.DebugAccumulator)
    requires false
    {
      acc := DebugAccumulator.EmptyAccumulator();
      var a := new DebugAccumulator.AccRec(|bits| as uint64, "uint64");
      acc := DebugAccumulator.AccPut(acc, "bits", a);
    }

    static predicate BitBSet(word: uint64, b: uint64)
    requires b < 64
    {
      BitsetLemmas.in_set_uint64(b, word)
    }

    lemma BitBSet0(b: uint64)
    requires b < 64
    ensures BitBSet(0, b) == false
    {
      BitsetLemmas.reveal_in_set_uint64();
      BitsetLemmas.reveal_in_set();
      BitsetLemmas.reveal_bit_and();
    }

    static predicate BitsSetAtIB(bitsSeq: seq<uint64>, i: nat, b: uint64)
    requires i < |bitsSeq|
    requires b < 64
    {
      && BitBSet(bitsSeq[i], b)
    }

    static predicate BitsSetAtC(bitsSeq: seq<uint64>, c: nat)
    requires c < 64 * |bitsSeq|
    {
      && BitsSetAtIB(bitsSeq, c / 64, (c % 64) as uint64)
    }

    static predicate ITimes64WithinUint64(i: nat)
    {
      && i * 64 < 0x1_0000_0000_0000_0000
    }

    protected predicate Inv()
    {
      && |bits| < 0x1_0000_0000_0000_0000 / 128
    }

    static function {:opaque} IPrefix(bits: seq<uint64>, i: int) : (res : BitmapModelT)
    requires 0 <= i <= 64 * |bits|
    ensures |res| == i
    ensures forall j | 0 <= j < i :: res[j] == BitsSetAtC(bits, j)
    {
      if i == 0 then [] else IPrefix(bits, i-1) + [BitsSetAtC(bits, i-1)]
    }

    protected function I() : BitmapModelT
    requires Inv()
    {
      IPrefix(bits, 64 * |bits|)
    }

    static method Constructor(len: uint64) returns (linear bm: Bitmap)
    requires len as int < 0x1_0000_0000_0000_0000 / 2
    requires len % 64 == 0
    ensures bm.Inv()
    ensures bm.I() == EmptyBitmap(len as int)
    {
      var bits := NativeArrays.newArrayFill(len / 64, 0);
      bm := Bitmap(bits[..]);

      ghost var ghosty := true;
      if ghosty {
        forall j | 0 <= j < len
        ensures bm.I()[j] == EmptyBitmap(len as int)[j];
        {
          bm.BitBSet0(j % 64);
          reveal_IsSet();
          //assert I()[j] == false;
          assert !IsSet(EmptyBitmap(len as int), j as int);
          //assert !EmptyBitmap(len as int)[j];
          //assert EmptyBitmap(len as int)[j] == false;
        }
      }
    }

    static function method SetBit(word: uint64, b: uint64) : uint64
    requires b < 64
    {
      BitsetLemmas.set_bit_to_1_uint64(word, b)
    }

    linear inout method Set(c: uint64)
    requires old_self.Inv()
    requires c as nat < Len(old_self.I())
    ensures self.Inv()
    ensures self.I() == BitSet(old_self.I(), c as int)
    {
      var i: uint64 := c / 64;
      var b: uint64 := c % 64;

      var word := SetBit(self.bits[i], b);
      inout self.bits := self.bits[i as int := word];

      ghost var ghosty := true;
      if ghosty {
        reveal_BitSet();
        reveal_IsSet();

        forall c' : int | 0 <= c' as int < 64 * |self.bits|
        ensures self.I()[c'] == BitSet(old_self.I(), c as int)[c']
        {
          var i' := c' / 64;
          var b' := c' % 64;
          if i' == i as nat {
            if b' == b as nat {
              BitsetLemmas.set_bit_to_1_self_uint64(old_self.bits[i], b);
              assert self.I()[c'] == BitSet(old_self.I(), c as int)[c'];
            } else {
              BitsetLemmas.set_bit_to_1_other_uint64(old_self.bits[i], b, b' as uint64);
              assert self.I()[c'] == BitSet(old_self.I(), c as int)[c'];
            }
          } else {
            assert self.I()[c'] == BitSet(old_self.I(), c as int)[c'];
          }
        }
      }
    }

    static function method UnsetBit(word: uint64, b: uint64) : uint64
    requires b < 64
    {
      BitsetLemmas.set_bit_to_0_uint64(word, b)
    }

    linear inout method Unset(c: uint64)
    requires old_self.Inv()
    requires c as nat < Len(old_self.I())
    ensures self.Inv()
    ensures self.I() == BitUnset(old_self.I(), c as int)
    {
      var i: uint64 := c / 64;
      var b: uint64 := c % 64;

      var word := UnsetBit(self.bits[i], b);
      inout self.bits := self.bits[i as int := word];

      ghost var ghosty := true;
      if ghosty {
        reveal_BitUnset();
        reveal_IsSet();

        forall c' : int | 0 <= c' as int < 64 * |self.bits|
        ensures self.I()[c'] == BitUnset(old_self.I(), c as int)[c']
        {
          var i' := c' / 64;
          var b' := c' % 64;
          if i' == i as nat {
            if b' == b as nat {
              BitsetLemmas.set_bit_to_0_self_uint64(old_self.bits[i], b);
              assert self.I()[c'] == BitUnset(old_self.I(), c as int)[c'];
            } else {
              BitsetLemmas.set_bit_to_0_other_uint64(old_self.bits[i], b, b' as uint64);
              assert self.I()[c'] == BitUnset(old_self.I(), c as int)[c'];
            }
          } else {
            assert self.I()[c'] == BitUnset(old_self.I(), c as int)[c'];
          }
        }
      }
    }

    shared function method GetIsSet(c: uint64) : (result: bool)
    requires Inv()
    requires c as nat < Len(I())
    ensures result == IsSet(I(), c as int)
    {
      var i: uint64 := c / 64;
      var b: uint64 := c % 64;

      reveal_IsSet();

      BitsetLemmas.in_set_uint64(b, this.bits[i])
    }

    lemma lemma_IsAllocNone()
    requires Inv()
    requires forall k | 0 <= k < |this.bits| ::
        this.bits[k] == 0xffff_ffff_ffff_ffff
    ensures BitAlloc(I()).None?
    {
      BitmapModel.reveal_IsSet();
      var bm := I();
      if BitAlloc(bm).Some? {
        var c := BitAlloc(bm).value as uint64;
        LemmaBitAllocResult(bm);
        var i: uint64 := c / 64;
        var b: uint64 := c % 64;

        assert this.bits[i] == 0xffff_ffff_ffff_ffff;
        BitsetLemmas.all1s_is_set_uint64(b);
      }
    }

    lemma lemma_IsAllocSome(i: uint64, b: uint64)
    requires Inv()
    requires 0 <= i as int < |this.bits|
    requires 0 <= b < 64
    requires forall k | 0 <= k < i as int ::
        this.bits[k] == 0xffff_ffff_ffff_ffff
    requires forall l | 0 <= l < b ::
        BitsetLemmas.in_set_uint64(l, this.bits[i])
    requires !BitsetLemmas.in_set_uint64(b, this.bits[i])
    ensures BitAlloc(I()) == Some(64 * i as int + b as int)
    {
      BitmapModel.reveal_IsSet();
      var bm := I();

      var c: uint64 := 64 * i + b;
      assert !bm[c];
      LemmaBitAllocResultStronger(bm);
      if (BitAlloc(bm).None?) {
        assert c as int < |bm|;
        assert IsSet(bm, c as int);
        assert false;
      }
      if (BitAlloc(bm).Some? && BitAlloc(bm).value > c as int) {
        assert IsSet(bm, c as int);
        assert false;
      }

      if (BitAlloc(bm).Some? && BitAlloc(bm).value < c as int) {
        var c0 := BitAlloc(bm).value as uint64;
        var i0 : uint64 := c0 / 64;
        var b0 : uint64 := c0 % 64;
        if i0 == i {
          assert b0 < b;
          assert false;
        } else {
          assert bits[i0] == 0xffff_ffff_ffff_ffff;
          BitsetLemmas.all1s_is_set_uint64(b0);
          assert false;
        }
      }
    }

    shared method Alloc() returns (res: Option<uint64>)
    requires Inv()
    ensures res.Some? <==> BitAlloc(I()).Some?
    ensures res.Some? ==> res.value as int == BitAlloc(I()).value
    {
      var i: uint64 := 0;
      while i < |this.bits| as uint64
      invariant 0 <= i as int <= |this.bits|
      invariant forall k | 0 <= k < i ::
          this.bits[k] == 0xffff_ffff_ffff_ffff
      {
        if this.bits[i] != 0xffff_ffff_ffff_ffff {
          // TODO this could be done faster:
          var j: uint64 := 0;
          while j < 64
          invariant 0 <= j <= 64
          invariant forall l | 0 <= l < j ::
              BitsetLemmas.in_set_uint64(l, this.bits[i])
          {
            if !BitsetLemmas.in_set_uint64(j, this.bits[i]) {
              lemma_IsAllocSome(i, j);
              res := Some(64 * i + j);
              return;
            }
            j := j + 1;
          }

          // Can't get here
          BitsetLemmas.all_in_set_implies_all1s_uint64(this.bits[i]);
          assert false;
        }
        i := i + 1;
      }

      res := None;
      lemma_IsAllocNone();
    }

    static method UnionConstructor(shared a: Bitmap, shared b: Bitmap) returns (linear bm: Bitmap)
    requires a.Inv()
    requires b.Inv()
    requires Len(a.I()) == Len(b.I())
    ensures bm.Inv()
    ensures bm.I() == BitUnion(a.I(), b.I())
    {
      var len := |a.bits| as uint64;
      var bits := new uint64[len];

      var i: uint64 := 0;
      while i < |a.bits| as uint64
      invariant 0 <= i as int <= |a.bits|;
      invariant fresh(bits);
      invariant a.I() == old(a.I())
      invariant b.I() == old(b.I())
      invariant |b.bits| == |a.bits|
      invariant forall j | 0 <= j < i as int ::
          bits[j] == BitsetLemmas.bit_or_uint64(a.bits[j], b.bits[j]);
      {
        bits[i] := BitsetLemmas.bit_or_uint64(a.bits[i], b.bits[i]);
        i := i + 1;
      }

      bm := Bitmap(bits[..]);

      ghost var x := bm.I();
      ghost var y := BitUnion(a.I(), b.I());
      assert |x| == |y|;
      forall c:uint64 | 0 <= c as int < |x| ensures x[c] == y[c]
      {
        reveal_IsSet();
        var i: uint64 := c / 64;
        var t: uint64 := c % 64;
        calc {
          x[c];
          BitBSet(bm.bits[i], t);
            { BitsetLemmas.bit_or_is_union_uint64(a.bits[i], b.bits[i], t); }
          (BitBSet(a.bits[i], t) || BitBSet(b.bits[i], t));
          IsSet(y, c as int);
          y[c];
        }
      }
    }

    static method CloneConstructor(shared a: Bitmap) returns (linear bm: Bitmap)
    requires a.Inv()
    ensures bm.Inv()
    ensures bm.I() == a.I()
    {
      bm := Bitmap(a.bits);
    }

    linear method Free()
    {
      linear var Bitmap(_) := this;
    }
  }
}
