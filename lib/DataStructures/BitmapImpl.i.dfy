include "BitmapModel.i.dfy"
//
// Maintains a compact set of integers using a packed-uint64 bitmap
// representation.
//

module BitmapImpl {
  import opened NativeTypes
  import opened Options
  import opened BitmapModel
  import NativeArrays
  import BitsetLemmas

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

    static function {:opaque} IPrefix(bits: seq<uint64>, i: int) : (res : BitmapModelT)
    requires 0 <= i <= 64 * |bits|
    ensures |res| == i
    ensures forall j | 0 <= j < i :: res[j] == BitsSetAtC(bits, j)
    {
      if i == 0 then [] else IPrefix(bits, i-1) + [BitsSetAtC(bits, i-1)]
    }

    protected function I() : BitmapModelT
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
    ensures fresh(Repr)
    {
      new;
      bits := NativeArrays.newArrayFill(len / 64, 0);
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

    method Alloc() returns (res: Option<uint64>)
    requires Inv()
    ensures res.Some? <==> BitAlloc(I()).Some?
    ensures res.Some? ==> res.value as int == BitAlloc(I()).value
    {
      assume false;

      var i: uint64 := 0;
      while i < this.bits.Length as uint64
      {
        if this.bits[i] != 0xffff_ffff_ffff_ffff {
          // TODO this could be done faster:
          var j: uint64 := 0;
          while j < 64 {
            if !BitsetLemmas.in_set_uint64(j, this.bits[i]) {
              res := Some(64 * i + j);
              return;
            }
            j := j + 1;
          }
        }
        i := i + 1;
      }

      res := None;
    }

    constructor Union(a: Bitmap, b: Bitmap)
    requires a.Inv()
    requires b.Inv()
    requires Len(a.I()) == Len(b.I())
    ensures Inv()
    ensures I() == BitUnion(a.I(), b.I())
    ensures fresh(Repr)
    {
      assume false;

      bits := new uint64[a.bits.Length as uint64];
      new;

      var i: uint64 := 0;
      while i < a.bits.Length as uint64
      {
        bits[i] := BitsetLemmas.bit_or_uint64(a.bits[i], b.bits[i]);
        i := i + 1;
      }

      Repr := { this, this.bits };
    }

    constructor Clone(a: Bitmap)
    requires a.Inv()
    ensures Inv()
    ensures fresh(Repr)
    ensures I() == a.I()
    {
      new;
      bits := NativeArrays.newArrayClone(a.bits);

      Repr := { this, this.bits };
    }
  }
}
