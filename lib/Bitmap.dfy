// NOTE: requires /noNLarith

include "NativeTypes.s.dfy"

module Bitmap {
  import opened NativeTypes


  class Bitmap {
    var bits: array<uint64>;

    ghost var Contents: set<uint64>;
    ghost var Repr: set<object>;

    static predicate {:opaque} BitBSet(word: uint64, b: nat)
    requires b < 64
    {
      && (word as bv64) & (1 << b) != 0
    }

    static predicate BitsSetAtIB(bitsSeq: seq<uint64>, i: nat, b: nat)
    requires i < |bitsSeq|
    requires b < 64
    {
      && BitBSet(bitsSeq[i], b)
    }

    static predicate BitsSetAtC(bitsSeq: seq<uint64>, c: nat)
    requires c / 64 < |bitsSeq|
    {
      && BitsSetAtIB(bitsSeq, c / 64, c % 64)
    }

    static predicate ITimes64WithinUint64(i: nat)
    {
      && i * 64 < 0x1_0000_0000_0000_0000
    }

    static predicate {:opaque} BitsMatchesContents(bitsSeq: seq<uint64>, contents: set<uint64>)
    {
      && (forall c: nat | c < 0x1_0000_0000_0000_0000 && c / 64 < |bitsSeq| ::
          c as uint64 in contents <==> BitsSetAtC(bitsSeq, c))
    }

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

      reveal_BitsMatchesContents();
      reveal_BitBSet();
    }

    static function method {:opaque} SetBit(word: uint64, b: uint64) : uint64
    requires b < 64
    {
      (word as bv64 | (1 << b)) as uint64
    }

    // TODO ???
    static lemma SetBitProperties(before: uint64, after: uint64, b: uint64)
    requires b < 64
    requires after == SetBit(before, b)
    ensures BitBSet(after, b as nat)
    ensures forall b': nat | b' != b as nat && b' < 64 :: BitBSet(after, b') <==> BitBSet(before, b')
    {
      assume false;
    }

    //== SetBitProperties attempts ==
    //{
    //  var beforeBV := before as bv64;
    //  var afterBV := after as bv64;

    //  forall ensures afterBV & (1 << b) != 0
    //  {
    //    reveal_SetBit();
    //    assert before as nat < 0x1_0000_0000_0000_0000;
    //    assert after as nat < 0x1_0000_0000_0000_0000;
    //    assert after == (before as bv64 | (1 << b)) as uint64;
    //    // TODO ???
    //    assume afterBV == (beforeBV | (1 << b));
    //    assume afterBV & (1 << b) != 0;
    //  }
    //  reveal_BitBSet();
    //  assert BitBSet(after, b as nat);

    //  forall b': nat | b' != b as nat && b' < 64
    //  ensures BitBSet(after, b') <==> BitBSet(before, b')
    //  {
    //    assume false;
    //    // TODO ???
    //    if BitBSet(before, b') {
    //    } else {
    //    }
    //  }
    //}

    method Set(c: uint64)
    requires c as nat / 64 < bits.Length
    requires Inv()
    ensures Inv()
    ensures Contents == old(Contents) + {c}
    ensures this.Repr == old(this.Repr)
    modifies this, this.Repr
    {
      var i: uint64 := c / 64;
      var b: uint64 := c % 64;

      this.bits[i] := SetBit(this.bits[i], b);
      SetBitProperties(old(this.bits[i]), this.bits[i], b);

      Contents := Contents + {c};

      forall c': nat | c' < 0x1_0000_0000_0000_0000 && c' / 64 < bits.Length
      ensures c' as uint64 in Contents <==> BitsSetAtC(bits[..], c')
      {
        var i' := c' / 64;
        var b' := c' % 64;
        if i' == i as nat {
          if b' == b as nat {
          } else {
            reveal_BitsMatchesContents();
            assert old(c' as uint64 in Contents) <==> BitsSetAtC(old(bits[..]), c'); // observe
          }
        } else {
          reveal_BitsMatchesContents();
          assert old(c' as uint64 in Contents) <==> BitsSetAtC(old(bits[..]), c'); // observe
          /* (doc) assert this.bits[c' / 64] == old(this.bits[c' / 64]); */
        }
      }
      reveal_BitsMatchesContents();
    }

    static function method {:opaque} ClearBit(word: uint64, b: uint64) : uint64
    requires b < 64
    {
      (word as bv64 & (0xffff_ffff_ffff_ffff ^ (1 << b))) as uint64
    }

    static lemma ClearBitProperties(before: uint64, after: uint64, b: uint64)
    requires b < 64
    requires after == ClearBit(before, b)
    ensures !BitBSet(after, b as nat)
    ensures forall b': nat | b' != b as nat && b' < 64 :: BitBSet(after, b') <==> BitBSet(before, b')
    {
      assume false;
    }

    method Clear(c: uint64)
    requires c as nat / 64 < bits.Length
    requires Inv()
    ensures Inv()
    ensures Contents == old(Contents) - {c}
    ensures this.Repr == old(this.Repr)
    modifies this, this.Repr
    {
      var i: uint64 := c / 64;
      var b: uint64 := c % 64;

      this.bits[i] := ClearBit(this.bits[i], b);
      ClearBitProperties(old(this.bits[i]), this.bits[i], b);

      Contents := Contents - {c};

      forall c': nat | c' < 0x1_0000_0000_0000_0000 && c' / 64 < bits.Length
      ensures c' as uint64 in Contents <==> BitsSetAtC(bits[..], c') {
        var i' := c' / 64;
        var b' := c' % 64;
        if i' == i as nat {
          if b' == b as nat {
            assert c' == c as nat;
            assert c !in Contents;
          } else {
            reveal_BitsMatchesContents();
            assert old(c' as uint64 in Contents) <==> BitsSetAtC(old(bits[..]), c'); // observe
          }
        } else {
          reveal_BitsMatchesContents();
          assert old(c' as uint64 in Contents) <==> BitsSetAtC(old(bits[..]), c'); // observe
          /* (doc) assert this.bits[c' / 64] == old(this.bits[c' / 64]); */
        }
      }
      reveal_BitsMatchesContents();
    }

    method IsSet(c: uint64) returns (result: bool)
    requires c as nat / 64 < bits.Length
    requires Inv()
    ensures Inv()
    ensures result <==> old(c in Contents)
    {
      var i: uint64 := c / 64;
      var b: uint64 := c % 64;

      result := this.bits[i] as bv64 & (1 << b) != 0;

      if c in Contents {
        reveal_BitsMatchesContents();
        assert BitsSetAtC(this.bits[..], c as nat);
        reveal_BitBSet();
      } else {
        reveal_BitsMatchesContents();
        assert !BitsSetAtC(this.bits[..], c as nat);
        reveal_BitBSet();
      }
    }
  }
}
