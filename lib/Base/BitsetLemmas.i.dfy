include "NativeTypes.s.dfy"
include "MathAxioms.s.dfy"
//
// Some support math to support Bitmap module.
//

module BitsetLemmas {
  import opened NativeTypes
  import MathAxioms
  // These first two are slow, but they work:

  lemma bit_ne_expanded(i: uint64, j: uint64)
  requires i < 64
  requires j < 64
  requires i != j
  ensures (1 as bv64 << i) & (1 as bv64 << j) == 0
  {
  }

  lemma bit_comp_ne_expanded(i: uint64, j: uint64)
  requires i < 64
  requires j < 64
  requires i != j
  ensures (0xffff_ffff_ffff_ffff ^ (1 as bv64 << i)) & (1 as bv64 << j)
      == (1 as bv64 << j)
  {
  }

  function method {:opaque} bit(i: uint64) : bv64
  requires i < 64
  {
    1 as bv64 << i
  }

  function method {:opaque} bit_and(a: bv64, b: bv64) : bv64
  {
    a & b
  }

  function method {:opaque} bit_or(a: bv64, b: bv64) : bv64
  {
    a | b
  }

  function method {:opaque} bit_comp(a: bv64) : bv64
  {
    0xffff_ffff_ffff_ffff ^ a
  }

  lemma and_or_dist(a: bv64, b: bv64, c: bv64)
  ensures bit_and(bit_or(a, b), c)
      == bit_or(bit_and(a, c), bit_and(b, c))
  {
    reveal_bit_and();
    reveal_bit_or();
  }

  lemma or_and_dist(a: bv64, b: bv64, c: bv64)
  ensures bit_or(bit_and(a, b), c)
      == bit_and(bit_or(a, c), bit_or(b, c))
  {
    reveal_bit_and();
    reveal_bit_or();
  }

  lemma bit_and_self(a: bv64)
  ensures bit_and(a, a) == a;
  {
    reveal_bit_and();
  }

  lemma bit_or_self(a: bv64)
  ensures bit_or(a, a) == a;
  {
    reveal_bit_or();
  }

  lemma bit_or_0(a: bv64)
  ensures bit_or(a, 0) == a;
  {
    reveal_bit_or();
  }

  lemma bit_and_0(a: bv64)
  ensures bit_and(a, 0) == 0;
  {
    reveal_bit_and();
  }

  lemma bit_or_and_self(a: bv64, b: bv64)
  ensures bit_and(bit_or(a, b), b) == b
  {
    reveal_bit_and();
    reveal_bit_or();
  }

  lemma bit_or_result_0_implies_args_0(a: bv64, b: bv64)
  requires bit_or(a, b) == 0
  ensures a == 0
  ensures b == 0
  {
    reveal_bit_or();
  }

  lemma zero_or_zero_eq_zero()
  ensures bit_or(0, 0) == 0
  {
    reveal_bit_or();
  }


  lemma bit_ne(i: uint64, j: uint64)
  requires i != j
  requires i < 64
  requires j < 64
  ensures bit_and(bit(i), bit(j)) == 0
  {
    reveal_bit();
    reveal_bit_and();
    bit_ne_expanded(i, j);
  }

  lemma bit_comp_ne(i: uint64, j: uint64)
  requires i != j
  requires i < 64
  requires j < 64
  ensures bit_and(bit_comp(bit(i)), bit(j)) == bit(j)
  {
    reveal_bit();
    reveal_bit_and();
    reveal_bit_comp();
    bit_comp_ne_expanded(i, j);
  }

  lemma and_comp(a: bv64)
  ensures bit_and(bit_comp(a), a) == 0
  {
    reveal_bit_and();
    reveal_bit_comp();
  }

  lemma bit_ne_0(i: uint64)
  requires i < 64
  ensures bit(i) != 0
  {
    // This is, by far, the greatest dafny proof I have ever written.
    assert i == 0 || i == 1 || i == 2 || i == 3 || i == 4 || i == 5 || i == 6 || i == 7 || i == 8 || i == 9 || i == 10 || i == 11 || i == 12 || i == 13 || i == 14 || i == 15 || i == 16 || i == 17 || i == 18 || i == 19 || i == 20 || i == 21 || i == 22 || i == 23 || i == 24 || i == 25 || i == 26 || i == 27 || i == 28 || i == 29 || i == 30 || i == 31 || i == 32 || i == 33 || i == 34 || i == 35 || i == 36 || i == 37 || i == 38 || i == 39 || i == 40 || i == 41 || i == 42 || i == 43 || i == 44 || i == 45 || i == 46 || i == 47 || i == 48 || i == 49 || i == 50 || i == 51 || i == 52 || i == 53 || i == 54 || i == 55 || i == 56 || i == 57 || i == 58 || i == 59 || i == 60 || i == 61 || i == 62 || i == 63;
    reveal_bit();
  }

  predicate method {:opaque} in_set(i: uint64, a: bv64)
  requires i < 64
  {
    bit_and(a, bit(i)) != 0
  }

  function method {:opaque} set_bit_to_1(a: bv64, i: uint64) : bv64
  requires i < 64
  {
    bit_or(a, bit(i))
  }

  function method {:opaque} set_bit_to_0(a: bv64, i: uint64) : bv64
  requires i < 64
  {
    bit_and(a, bit_comp(bit(i)))
  }

  lemma bit_and_and_comp(a: bv64)
  ensures bit_comp(a) & a == 0
  {
    reveal_bit_comp();
  }

  lemma bit_and_assoc(a: bv64, b: bv64, c: bv64)
  ensures bit_and(a, bit_and(b, c)) == bit_and(bit_and(a, b), c)
  {
    reveal_bit_and();
  }

  lemma set_bit_to_1_self(a: bv64, i: uint64)
  requires i < 64
  ensures in_set(i, set_bit_to_1(a, i))
  {
    reveal_set_bit_to_1();
    reveal_in_set();

    calc {
      bit_and(set_bit_to_1(a, i), bit(i));
      bit_and(bit_or(a, bit(i)), bit(i));
        { bit_or_and_self(a, bit(i)); }
      bit(i);
    }
    bit_ne_0(i);
  }

  lemma set_bit_to_1_other(a: bv64, i: uint64, j: uint64)
  requires i < 64
  requires j < 64
  requires i != j
  ensures in_set(j, a) <==> in_set(j, set_bit_to_1(a, i))
  {
    reveal_set_bit_to_1();
    reveal_in_set();

    calc {
      bit_and(set_bit_to_1(a, i), bit(j));
      bit_and(bit_or(a, bit(i)), bit(j));
        { and_or_dist(a, bit(i), bit(j)); }
      bit_or(bit_and(a, bit(j)), bit_and(bit(i), bit(j)));
        { bit_ne(i, j); }
      bit_or(bit_and(a, bit(j)), 0);
        { bit_or_0(bit_and(a, bit(j))); }
      bit_and(a, bit(j));
    }
  }

  lemma set_bit_to_0_self(a: bv64, i: uint64)
  requires i < 64
  ensures !in_set(i, set_bit_to_0(a, i))
  {
    reveal_set_bit_to_0();
    reveal_in_set();

    calc {
      bit_and(set_bit_to_0(a, i), bit(i));
      bit_and(bit_and(a, bit_comp(bit(i))), bit(i));
        { bit_and_assoc(a, bit_comp(bit(i)), bit(i)); }
      bit_and(a, bit_and(bit_comp(bit(i)), bit(i)));
        { and_comp(bit(i)); }
      bit_and(a, 0);
        { bit_and_0(a); }
      0 as bv64;
    }
  }

  lemma set_bit_to_0_other(a: bv64, i: uint64, j: uint64)
  requires i < 64
  requires j < 64
  requires i != j
  ensures in_set(j, a) <==> in_set(j, set_bit_to_0(a, i))
  {
    reveal_set_bit_to_0();
    reveal_in_set();

    calc {
      bit_and(set_bit_to_0(a, i), bit(j));
      bit_and(bit_and(a, bit_comp(bit(i))), bit(j));
        { bit_and_assoc(a, bit_comp(bit(i)), bit(j)); }
      bit_and(a, bit_and(bit_comp(bit(i)), bit(j)));
        { bit_comp_ne(i, j); }
      bit_and(a, bit(j));
    }
  }

  lemma bit_or_is_union(a: bv64, b: bv64, i: uint64)
  requires i < 64
  ensures in_set(i, bit_or(a, b)) == (in_set(i, a) || in_set(i, b))
  {
    reveal_in_set();

    calc {
      bit_and(bit_or(a, b), bit(i));
        { and_or_dist(a, b, bit(i)); }
      bit_or(bit_and(a, bit(i)), bit_and(b, bit(i)));
    }

    if !in_set(i, bit_or(a, b)) {
      bit_or_result_0_implies_args_0(
          bit_and(a, bit(i)), bit_and(b, bit(i)));
    } else {
      zero_or_zero_eq_zero();
    }
  }

  lemma all1s_and_bit_eq(i: uint64)
  requires i < 64
  ensures bit_and(0xffff_ffff_ffff_ffff, bit(i)) == bit(i)
  {
    reveal_bit_and();
    reveal_bit();
  }

  lemma all1s_is_set(i: uint64)
  requires i < 64
  ensures in_set(i, 0xffff_ffff_ffff_ffff)
  {
    reveal_in_set();
    all1s_and_bit_eq(i);
    bit_ne_0(i);
  }

  lemma all_in_set_implies_all1s(a: bv64)
  requires forall i | 0 <= i < 64 :: in_set(i, a)
  ensures a == 0xffff_ffff_ffff_ffff
  {
    reveal_in_set();
    reveal_bit_and();
    reveal_bit();
    assert a & 1 == 1 by { assert in_set(0, a); }
    assert a & 2 == 2 by { assert in_set(1, a); }
    assert a & 4 == 4 by { assert in_set(2, a); }
    assert a & 8 == 8 by { assert in_set(3, a); }
    assert a & 16 == 16 by { assert in_set(4, a); }
    assert a & 32 == 32 by { assert in_set(5, a); }
    assert a & 64 == 64 by { assert in_set(6, a); }
    assert a & 128 == 128 by { assert in_set(7, a); }
    assert a & 256 == 256 by { assert in_set(8, a); }
    assert a & 512 == 512 by { assert in_set(9, a); }
    assert a & 1024 == 1024 by { assert in_set(10, a); }
    assert a & 2048 == 2048 by { assert in_set(11, a); }
    assert a & 4096 == 4096 by { assert in_set(12, a); }
    assert a & 8192 == 8192 by { assert in_set(13, a); }
    assert a & 16384 == 16384 by { assert in_set(14, a); }
    assert a & 32768 == 32768 by { assert in_set(15, a); }
    assert a & 65536 == 65536 by { assert in_set(16, a); }
    assert a & 131072 == 131072 by { assert in_set(17, a); }
    assert a & 262144 == 262144 by { assert in_set(18, a); }
    assert a & 524288 == 524288 by { assert in_set(19, a); }
    assert a & 1048576 == 1048576 by { assert in_set(20, a); }
    assert a & 2097152 == 2097152 by { assert in_set(21, a); }
    assert a & 4194304 == 4194304 by { assert in_set(22, a); }
    assert a & 8388608 == 8388608 by { assert in_set(23, a); }
    assert a & 16777216 == 16777216 by { assert in_set(24, a); }
    assert a & 33554432 == 33554432 by { assert in_set(25, a); }
    assert a & 67108864 == 67108864 by { assert in_set(26, a); }
    assert a & 134217728 == 134217728 by { assert in_set(27, a); }
    assert a & 268435456 == 268435456 by { assert in_set(28, a); }
    assert a & 536870912 == 536870912 by { assert in_set(29, a); }
    assert a & 1073741824 == 1073741824 by { assert in_set(30, a); }
    assert a & 2147483648 == 2147483648 by { assert in_set(31, a); }
    assert a & 4294967296 == 4294967296 by { assert in_set(32, a); }
    assert a & 8589934592 == 8589934592 by { assert in_set(33, a); }
    assert a & 17179869184 == 17179869184 by { assert in_set(34, a); }
    assert a & 34359738368 == 34359738368 by { assert in_set(35, a); }
    assert a & 68719476736 == 68719476736 by { assert in_set(36, a); }
    assert a & 137438953472 == 137438953472 by { assert in_set(37, a); }
    assert a & 274877906944 == 274877906944 by { assert in_set(38, a); }
    assert a & 549755813888 == 549755813888 by { assert in_set(39, a); }
    assert a & 1099511627776 == 1099511627776 by { assert in_set(40, a); }
    assert a & 2199023255552 == 2199023255552 by { assert in_set(41, a); }
    assert a & 4398046511104 == 4398046511104 by { assert in_set(42, a); }
    assert a & 8796093022208 == 8796093022208 by { assert in_set(43, a); }
    assert a & 17592186044416 == 17592186044416 by { assert in_set(44, a); }
    assert a & 35184372088832 == 35184372088832 by { assert in_set(45, a); }
    assert a & 70368744177664 == 70368744177664 by { assert in_set(46, a); }
    assert a & 140737488355328 == 140737488355328 by { assert in_set(47, a); }
    assert a & 281474976710656 == 281474976710656 by { assert in_set(48, a); }
    assert a & 562949953421312 == 562949953421312 by { assert in_set(49, a); }
    assert a & 1125899906842624 == 1125899906842624 by { assert in_set(50, a); }
    assert a & 2251799813685248 == 2251799813685248 by { assert in_set(51, a); }
    assert a & 4503599627370496 == 4503599627370496 by { assert in_set(52, a); }
    assert a & 9007199254740992 == 9007199254740992 by { assert in_set(53, a); }
    assert a & 18014398509481984 == 18014398509481984 by { assert in_set(54, a); }
    assert a & 36028797018963968 == 36028797018963968 by { assert in_set(55, a); }
    assert a & 72057594037927936 == 72057594037927936 by { assert in_set(56, a); }
    assert a & 144115188075855872 == 144115188075855872 by { assert in_set(57, a); }
    assert a & 288230376151711744 == 288230376151711744 by { assert in_set(58, a); }
    assert a & 576460752303423488 == 576460752303423488 by { assert in_set(59, a); }
    assert a & 1152921504606846976 == 1152921504606846976 by { assert in_set(60, a); }
    assert a & 2305843009213693952 == 2305843009213693952 by { assert in_set(61, a); }
    assert a & 4611686018427387904 == 4611686018427387904 by { assert in_set(62, a); }
    assert a & 9223372036854775808 == 9223372036854775808 by { assert in_set(63, a); }
  }

  // uint64

  function method {:opaque} bit_or_uint64(a: uint64, b: uint64) : uint64
  {
    bit_or(a as bv64, b as bv64) as uint64
  }

  predicate method {:opaque} in_set_uint64(i: uint64, a: uint64)
  requires i < 64
  {
    in_set(i, a as bv64)
  }

  function method {:opaque} set_bit_to_1_uint64(a: uint64, i: uint64) : uint64
  requires i < 64
  {
    set_bit_to_1(a as bv64, i) as uint64
  }

  function method {:opaque} set_bit_to_0_uint64(a: uint64, i: uint64) : uint64
  requires i < 64
  {
    set_bit_to_0(a as bv64, i) as uint64
  }

  lemma bv64cast(a: bv64)
  ensures (a as uint64) as bv64 == a
  {
    MathAxioms.as_int_as_bv64(a);
  }

  lemma set_bit_to_1_self_uint64(a: uint64, i: uint64)
  requires i < 64
  ensures in_set_uint64(i, set_bit_to_1_uint64(a, i))
  {
    set_bit_to_1_self(a as bv64, i);
    bv64cast(set_bit_to_1(a as bv64, i));
    reveal_in_set_uint64();
    reveal_set_bit_to_1_uint64();
  }

  lemma set_bit_to_1_other_uint64(a: uint64, i: uint64, j: uint64)
  requires i < 64
  requires j < 64
  requires i != j
  ensures in_set_uint64(j, a) <==> in_set_uint64(j, set_bit_to_1_uint64(a, i))
  {
    set_bit_to_1_other(a as bv64, i, j);
    bv64cast(set_bit_to_1(a as bv64, i));
    reveal_in_set_uint64();
    reveal_set_bit_to_1_uint64();
  }

  lemma set_bit_to_0_self_uint64(a: uint64, i: uint64)
  requires i < 64
  ensures !in_set_uint64(i, set_bit_to_0_uint64(a, i))
  {
    set_bit_to_0_self(a as bv64, i);
    bv64cast(set_bit_to_0(a as bv64, i));
    reveal_in_set_uint64();
    reveal_set_bit_to_0_uint64();
  }

  lemma set_bit_to_0_other_uint64(a: uint64, i: uint64, j: uint64)
  requires i < 64
  requires j < 64
  requires i != j
  ensures in_set_uint64(j, a) <==> in_set_uint64(j, set_bit_to_0_uint64(a, i))
  {
    set_bit_to_0_other(a as bv64, i, j);
    bv64cast(set_bit_to_0(a as bv64, i));
    reveal_in_set_uint64();
    reveal_set_bit_to_0_uint64();
  }

  lemma bit_or_is_union_uint64(a: uint64, b: uint64, i: uint64)
  requires i < 64
  ensures in_set_uint64(i, bit_or_uint64(a, b))
      == (in_set_uint64(i, a) || in_set_uint64(i, b))
  {
    bit_or_is_union(a as bv64, b as bv64, i);
    bv64cast(bit_or(a as bv64, b as bv64));
    reveal_bit_or_uint64();
    reveal_in_set_uint64();
  }

  lemma all1s_is_set_uint64(i: uint64)
  requires i < 64
  ensures in_set_uint64(i, 0xffff_ffff_ffff_ffff)
  {
    all1s_is_set(i);
    reveal_in_set_uint64();
  }

  lemma all_in_set_implies_all1s_uint64(a: uint64)
  requires forall i | 0 <= i < 64 :: in_set_uint64(i, a)
  ensures a == 0xffff_ffff_ffff_ffff
  {
    forall i | 0 <= i < 64 ensures in_set(i, a as bv64)
    {
      reveal_in_set_uint64();
      assert in_set_uint64(i, a);
    }
    reveal_in_set();
    all_in_set_implies_all1s(a as bv64);
  }
}
