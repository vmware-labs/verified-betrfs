module BitsetLemmas {
  import opened NativeTypes
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

  function {:opaque} bit(i: uint64) : bv64
  requires i < 64
  {
    1 as bv64 << i
  }

  function {:opaque} bit_and(a: bv64, b: bv64) : bv64
  {
    a & b
  }

  function {:opaque} bit_or(a: bv64, b: bv64) : bv64
  {
    a | b
  }

  function {:opaque} bit_comp(a: bv64) : bv64
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

  predicate {:opaque} in_set(i: uint64, a: bv64)
  requires i < 64
  {
    bit_and(a, bit(i)) != 0
  }

  function {:opaque} set_bit_to_1(a: bv64, i: uint64) : bv64
  requires i < 64
  {
    bit_or(a, bit(i))
  }

  function {:opaque} set_bit_to_0(a: bv64, i: uint64) : bv64
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
}
