// NOTE: requires /noNLarith

include "NativeTypes.s.dfy"
include "Option.s.dfy"
include "Marshalling/Native.s.dfy"
include "BitsetLemmas.i.dfy"

module Bitmap {
  import opened NativeTypes
  import opened Options
  import Native
  import BitsetLemmas

  type BitmapModel = seq<bool>

  function Len(bm: BitmapModel) : int
  {
    |bm|
  }

  function {:opaque} BitSet(bm: BitmapModel, i: int) : (bm' : BitmapModel)
  requires 0 <= i < Len(bm)
  ensures Len(bm') == Len(bm)
  {
    bm[i := true]
  }

  function {:opaque} BitUnset(bm: BitmapModel, i: int) : (bm' : BitmapModel)
  requires 0 <= i < Len(bm)
  ensures Len(bm') == Len(bm)
  {
    bm[i := false]
  }

  predicate {:opaque} IsSet(bm: BitmapModel, i: int)
  requires 0 <= i < Len(bm)
  {
    bm[i]
  }

  function {:opaque} EmptyBitmap(n: int) : (bm : BitmapModel)
  requires n >= 0
  ensures Len(bm) == n
  ensures forall i | 0 <= i < Len(bm) :: !IsSet(bm, i)
  {
    if n == 0 then [] else (
      var bm := EmptyBitmap(n-1) + [false];

      reveal_IsSet();
      assert forall i | 0 <= i < n - 1 :: !IsSet(EmptyBitmap(n-1), i);
      assert forall i | 0 <= i < n - 1 :: bm[i] == IsSet(bm, i);
      assert forall i | 0 <= i < n - 1 :: EmptyBitmap(n-1)[i] == IsSet(EmptyBitmap(n-1), i);
      assert forall i | 0 <= i < n - 1 :: bm[i] == EmptyBitmap(n-1)[i];
      assert forall i | 0 <= i < n - 1 :: !IsSet(bm, i);
      assert !IsSet(bm, n - 1);
      assert forall i | 0 <= i < n :: !IsSet(bm, i);

      bm
    )
  }

  function BitAllocIter(bm: BitmapModel, i: int) : (res: Option<int>)
  requires 0 <= i <= |bm|
  decreases |bm| - i
  ensures res.Some? ==> 0 <= res.value < |bm|
  {
    if i == |bm| then (
      (None)
    ) else if !bm[i] then (
      Some(i)
    ) else (
      BitAllocIter(bm, i+1)
    ) 
  }

  function {:opaque} BitAlloc(bm: BitmapModel) : (res: Option<int>)
  ensures res.Some? ==> 0 <= res.value < Len(bm)
  {
    BitAllocIter(bm, 0)
  }

  function {:opaque} Union(a: BitmapModel, b: BitmapModel) : (res: BitmapModel)
  requires Len(a) == Len(b)
  ensures Len(res) == Len(a)
  ensures forall i | 0 <= i < Len(res) :: IsSet(res, i) == (IsSet(a, i) || IsSet(b, i))
  {
    reveal_IsSet();
    if |a| == 0 then [] else (
      var res := Union(a[..|a|-1], b[..|b|-1]) + [a[|a|-1] || b[|b|-1]];
      assert IsSet(res, |a|-1) == (IsSet(a, |a|-1) || IsSet(b, |a|-1));
      assert forall i | 0 <= i < Len(res)-1 :: IsSet(a, i) == IsSet(a[..|a|-1], i);
      assert forall i | 0 <= i < Len(res)-1 :: IsSet(b, i) == IsSet(b[..|a|-1], i);
      assert forall i | 0 <= i < Len(res)-1 :: IsSet(res, i) == (IsSet(a, i) || IsSet(b, i));
      assert forall i | 0 <= i < Len(res) :: IsSet(res, i) == (IsSet(a, i) || IsSet(b, i));
      res
    )
  }

  lemma LemmaBitAllocResult(bm: BitmapModel)
  ensures var i := BitAlloc(bm);
    && (i.Some? ==> (!IsSet(bm, i.value)))

  class Bitmap {
    var bits: array<uint64>;

    ghost var Repr: set<object>;

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

    predicate ReprInv()
    reads this, this.Repr
    {
      && this.Repr == { this, this.bits }
    }

    protected predicate Inv()
    ensures Inv() ==> this in this.Repr
    reads this, this.Repr
    {
      && ReprInv()
    }

    static function {:opaque} IPrefix(bits: seq<uint64>, i: int) : (res : BitmapModel)
    requires 0 <= i <= 64 * |bits|
    ensures |res| == i
    ensures forall j | 0 <= j < i :: res[j] == BitsSetAtC(bits, j)
    {
      if i == 0 then [] else IPrefix(bits, i-1) + [BitsSetAtC(bits, i-1)]
    }

    protected function I() : BitmapModel
    reads this, this.Repr
    requires Inv()
    {
      IPrefix(bits[..], 64 * bits.Length)
    }

    constructor (len: uint64)
    requires len as int < 0x1_0000_0000_0000_0000 / 2
    requires len % 64 == 0
    ensures Inv()
    ensures I() == EmptyBitmap(len as int)
    {
      new;
      bits := Native.Arrays.newArrayFill(len / 64, 0);
      Repr := { this, this.bits };

      ghost var ghosty := true;
      if ghosty {
        forall j | 0 <= j < len
        ensures I()[j] == EmptyBitmap(len as int)[j];
        {
          BitBSet0(j % 64);
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

    method Set(c: uint64)
    requires Inv()
    requires c as nat < Len(I())
    ensures Inv()
    ensures I() == BitSet(old(I()), c as int)
    ensures this.Repr == old(this.Repr)
    modifies this, this.Repr
    {
      var i: uint64 := c / 64;
      var b: uint64 := c % 64;

      this.bits[i] := SetBit(this.bits[i], b);

      ghost var ghosty := true;
      if ghosty {
        reveal_BitSet();
        reveal_IsSet();

        forall c' : int | 0 <= c' as int < 64 * this.bits.Length
        ensures I()[c'] == BitSet(old(I()), c as int)[c']
        {
          var i' := c' / 64;
          var b' := c' % 64;
          if i' == i as nat {
            if b' == b as nat {
              BitsetLemmas.set_bit_to_1_self_uint64(old(this.bits[i]), b);
              assert I()[c'] == BitSet(old(I()), c as int)[c'];
            } else {
              BitsetLemmas.set_bit_to_1_other_uint64(old(this.bits[i]), b, b' as uint64);
              assert I()[c'] == BitSet(old(I()), c as int)[c'];
            }
          } else {
            assert I()[c'] == BitSet(old(I()), c as int)[c'];
          }
        }
      }
    }

    static function method UnsetBit(word: uint64, b: uint64) : uint64
    requires b < 64
    {
      BitsetLemmas.set_bit_to_0_uint64(word, b)
    }

    method Unset(c: uint64)
    requires Inv()
    requires c as nat < Len(I())
    ensures Inv()
    ensures I() == BitUnset(old(I()), c as int)
    ensures this.Repr == old(this.Repr)
    modifies this, this.Repr
    {
      var i: uint64 := c / 64;
      var b: uint64 := c % 64;

      this.bits[i] := UnsetBit(this.bits[i], b);

      ghost var ghosty := true;
      if ghosty {
        reveal_BitUnset();
        reveal_IsSet();

        forall c' : int | 0 <= c' as int < 64 * this.bits.Length
        ensures I()[c'] == BitUnset(old(I()), c as int)[c']
        {
          var i' := c' / 64;
          var b' := c' % 64;
          if i' == i as nat {
            if b' == b as nat {
              BitsetLemmas.set_bit_to_0_self_uint64(old(this.bits[i]), b);
              assert I()[c'] == BitUnset(old(I()), c as int)[c'];
            } else {
              BitsetLemmas.set_bit_to_0_other_uint64(old(this.bits[i]), b, b' as uint64);
              assert I()[c'] == BitUnset(old(I()), c as int)[c'];
            }
          } else {
            assert I()[c'] == BitUnset(old(I()), c as int)[c'];
          }
        }
      }
    }

    method GetIsSet(c: uint64) returns (result: bool)
    requires Inv()
    requires c as nat < Len(I())
    ensures result == IsSet(I(), c as int)
    {
      var i: uint64 := c / 64;
      var b: uint64 := c % 64;

      reveal_IsSet();

      result := BitsetLemmas.in_set_uint64(b, this.bits[i]);
    }
  }
}
