
include "NativeTypes.s.dfy"

module Bitmap {
  import opened NativeTypes

  predicate {:opaque} BitsSetAtIB(bitsSeq: seq<bv64>, i: nat, b: nat)
  requires i < |bitsSeq|
  requires b < 64
  {
    && bitsSeq[i] & (1 << b) != 0
  }

  predicate {:opaque} BitsSetAtC(bitsSeq: seq<bv64>, c: nat)
  requires c / 64 < |bitsSeq|
  {
    && BitsSetAtIB(bitsSeq, c / 64, c % 64)
  }

  predicate ITimes64WithinUint64(i: nat)
  {
    && i * 64 < 0x1_0000_0000_0000_0000
  }

  predicate {:opaque} BitsMatchesContents(bitsSeq: seq<bv64>, contents: set<uint64>)
  {
    && (forall c: nat | c < 0x1_0000_0000_0000_0000 && (c as uint64) in contents && c / 64 < |bitsSeq| :: BitsSetAtC(bitsSeq, c))
  }

  predicate {:opaque} ContentsMatchesBits(bitsSeq: seq<bv64>, contents: set<uint64>)
  {
    && (forall i: nat, b: nat | i < |bitsSeq| && ITimes64WithinUint64(i) && b < 64 && BitsSetAtIB(bitsSeq, i, b) ::
        (((i * 64) + b) as uint64) in contents)
  }

  class Bitmap {
    var bits: array<bv64>;

    ghost var Contents: set<uint64>;
    ghost var Repr: set<object>;

    predicate ReprInv()
    reads this, this.Repr
    {
      && this.Repr == { this, this.bits }
    }


    protected predicate Inv()
    ensures Inv() ==> ReprInv()
    reads this, this.Repr
    {
      && ReprInv()

      && BitsMatchesContents(bits[..], Contents)

      && ContentsMatchesBits(bits[..], Contents)
    }

    constructor (max: uint64)
    requires max as nat < 0x1_0000_0000_0000_0000 / 2
    ensures Contents == {}
    ensures Inv()
    {
      assert ((max / 64) + 1) * 64 > max;
      bits := new [(max / 64) + 1] (_ => 0);

      new;

      Contents := {};
      Repr := { this, this.bits };

      assume false;

      // reveal_BitsMatchesContents();
      // reveal_ContentsMatchesBits();
    }

    method Set(c: uint64)
    requires c as nat / 64 < bits.Length
    requires Inv()
    ensures Inv()
    ensures Contents == old(Contents) + {c}
    ensures this.Repr == old(this.Repr)
    modifies this, this.Repr
    {
      this.bits[c / 64] := this.bits[c / 64] | (1 << (c % 64));

      Contents := Contents + {c};

      forall c: nat | c < 0x1_0000_0000_0000_0000 && (c as uint64) in Contents && c / 64 < bits.Length
      ensures BitsSetAtC(bits[..], c) {
        assume false;
      }
      forall i: nat, b: nat | i < bits.Length && ITimes64WithinUint64(i) && b < 64 && BitsSetAtIB(bits[..], i, b)
      ensures (((i * 64) + b) as uint64) in Contents
      {
        assume false;
      }
      // reveal_BitsMatchesContents();
      // reveal_ContentsMatchesBits();
      assert Inv();
    }

    method Clear(c: uint64)
    requires c as nat / 64 < bits.Length
    requires Inv()
    ensures Inv()
    ensures Contents == old(Contents) - {c}
    ensures this.Repr == old(this.Repr)
    modifies this, this.Repr
    {
      this.bits[c / 64] := this.bits[c / 64] & (-(1 << (c % 64)));

      Contents := Contents - {c};

      assume BitsMatchesContents(bits[..], Contents);
      assume ContentsMatchesBits(bits[..], Contents);
      assert Inv();
    }
  }
}
