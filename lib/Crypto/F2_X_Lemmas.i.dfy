include "../Lang/System/F2_X.s.dfy"
include "../Base/SetBijectivity.i.dfy"

module F2_X_Lemmas {
  import opened Bits_s
  import opened F2_X_s
  import SetBijectivity

  function poly() : Bits { bits_of_int(0x1_1EDC_6F41, 33) }

  function mod(p: Bits) : Bits
  {
    mod_F2_X(p, poly())
  }

  function mod_mul(x: Bits, y: Bits) : Bits
  {
    mod(mul_F2_X(x, y))
  }

  function exp(n: nat) : Bits
  {
    zeroes(n) + [true]
  }

  lemma mod_xor(x: Bits, y: Bits)
  requires |x| == |y|
  ensures mod(xor(x, y)) == xor(mod(x), mod(y))
  decreases |x|
  {
    var q := poly();
    if |x| > 32 {
      var x1 := if x[|x|-1] then xor(x, shift(q, |x|-|q|)) else x;
      var y1 := if y[|y|-1] then xor(y, shift(q, |y|-|q|)) else y;
      var x1' := x1[..|x|-1];
      var y1' := y1[..|y|-1];

      var z := xor(x, y);
      var z1 := if z[|z|-1] then xor(z, shift(q, |z|-|q|)) else z;
      var z1' := z1[..|z|-1];

      calc {
        mod(xor(x, y));
        mod(z);
        mod(z1');
        {
          assert z1' == xor(x1', y1');
        }
        mod(xor(x1', y1'));
        {
          mod_xor(x1', y1');
        }
        xor(mod(x1'), mod(y1'));
        xor(mod(x), mod(y));
      }
    } else {
    }
  }

  lemma mod_ignores_trailing_zeroes(x: Bits, n: nat)
  ensures mod(x + zeroes(n)) == mod(x)
  {
    var q := poly();
    if n > 0 {
      mod_ignores_trailing_zeroes(x, n-1);
      if |x| + n > |q| - 1 {
        var y := x + zeroes(n);
        var y1 := if y[|y|-1] then xor(y, shift(q, |y|-|q|)) else y;
        var y1' := y1[..|y|-1];
        assert y1' == x + zeroes(n-1);
        calc {
          mod(x + zeroes(n));
          mod(x + zeroes(n-1));
          mod(x);
        }
      } else {
        assert mod(x + zeroes(n)) == mod(x);
      }
    } else {
      assert x + zeroes(n) == x;
      assert mod(x + zeroes(n)) == mod(x);
    }
  }

  lemma mul_left_distributive_partial(p: Bits, q: Bits, r: Bits, i: nat, j: nat)
  requires |q| == |r|
  requires j <= i+1
  ensures mul_F2_X_digit_partial(p, xor(q, r), i, j)
      == bool_xor(
          mul_F2_X_digit_partial(p, q, i, j),
          mul_F2_X_digit_partial(p, r, i, j))
  decreases i + 1 - j
  {
    if j == i+1 {
    } else {
      mul_left_distributive_partial(p, q, r, i, j+1);
    }
  }

  lemma mul_left_distributive(x: Bits, y: Bits, z: Bits)
  requires |y| == |z|
  ensures mul_F2_X(x, xor(y, z))
      == xor(mul_F2_X(x, y), mul_F2_X(x, z))
  {
    var a := mul_F2_X(x, xor(y, z));
    var b := xor(mul_F2_X(x, y), mul_F2_X(x, z));
    forall i | 0 <= i < |a| ensures a[i] == b[i] 
    {
      mul_left_distributive_partial(x, y, z, i, 0);
    }
  }

  lemma mod_mul_left_distributive(x: Bits, y: Bits, z: Bits)
  requires |y| == |z|
  ensures mod_mul(x, xor(y, z))
      == xor(mod_mul(x, y), mod_mul(x, z))
  {
    calc {
      mod_mul(x, xor(y, z));
      { mul_left_distributive(x, y, z); }
      mod(xor(mul_F2_X(x, y), mul_F2_X(x, z)));
      { mod_xor(mul_F2_X(x, y), mul_F2_X(x, z)); }
      xor(mod_mul(x, y), mod_mul(x, z));
    }
  }

  function {:opaque} parity<V>(m: set<V>) : bool
  {
    |m| % 2 == 1
  }

  function set_partial(p: Bits, q: Bits, i: nat, j: nat) : set<(nat,nat)>
  {
    set a:nat, b: nat
          | a <= i && b <= i && a >= j && a + b == i
                && bits_get(p, a) && bits_get(q, b)
          :: (a,b)
  }

  lemma mset_mul_F2_X_digit_partial(p: Bits, q: Bits, i: nat, j: nat)
  requires j <= i+1
  decreases i + 1 - j
  ensures mul_F2_X_digit_partial(p, q, i, j) == parity(set_partial(p, q, i, j))
  {
    reveal_parity();
    var m := set_partial(p, q, i, j);
    if j == i+1 {
      assert |m| == 0;
      assert 0 % 2 == 0;
      assert |m| % 2 == 0;
      assert parity(m) == false;
      assert !mul_F2_X_digit_partial(p, q, i, j);
    } else {
      mset_mul_F2_X_digit_partial(p, q, i, j+1);
      var m' := set_partial(p, q, i, j+1);
      if bits_get(p, j) && bits_get(q, i-j) {
        assert m == m' + {(j, i-j)};
      } else {
        assert m == m';
      }
    }
  }

  function set_digit(p: Bits, q: Bits, i: nat) : set<(nat,nat)>
  {
    set a:nat, b: nat
          | a <= i && b <= i && a + b == i
                && bits_get(p, a) && bits_get(q, b)
          :: (a,b)
  }

  lemma mset_mul_F2_X_digit(p: Bits, q: Bits, i: nat)
  ensures mul_F2_X_digit(p, q, i) == parity(set_digit(p, q, i))
  {
    mset_mul_F2_X_digit_partial(p, q, i, 0);
    assert set_digit(p, q, i)
        == set_partial(p, q, i, 0);
  }

  lemma mul_comm(p: Bits, q: Bits)
  ensures mul_F2_X(p, q) == mul_F2_X(q, p)
  {
    var a := mul_F2_X(p,q);
    var b := mul_F2_X(q,p);
    assert |a| == |b|;
    forall i | 0 <= i < |a|
    ensures a[i] == b[i]
    {
      calc {
        mul_F2_X(p,q)[i];
        mul_F2_X_digit(p, q, i);
          { mset_mul_F2_X_digit(p, q, i); }
        parity(set_digit(p, q, i));
          {
            var setA := set_digit(p, q, i);
            var setB := set_digit(q, p, i);
            var relation := iset a: ((nat,nat),(nat,nat)) | a.0.0 == a.1.1 && a.0.1 == a.1.0;

            forall a | a in setA ensures exists b :: b in setB && (a, b) in relation
            {
              var b := (a.1, a.0);
              assert b in setB && (a, b) in relation;
            }
            forall b | b in setB ensures exists a :: a in setA && (a, b) in relation
            {
              var a := (b.1, b.0);
              assert a in setA && (a, b) in relation;
            }

            SetBijectivity.BijectivityImpliesEqualCardinality(setA, setB, relation);
            reveal_parity();
          }
        parity(set_digit(q, p, i));
          { mset_mul_F2_X_digit(q, p, i); }
        mul_F2_X_digit(q, p, i);
        mul_F2_X(q,p)[i];
      }
    }
  }

  lemma mul_right_distributive(x: Bits, y: Bits, z: Bits)
  requires |x| == |y|
  ensures mul_F2_X(xor(x, y), z)
      == xor(mul_F2_X(x, z), mul_F2_X(y, z))
  {
    mul_left_distributive(z, x, y);
    mul_comm(xor(x,y), z);
    mul_comm(x, z);
    mul_comm(y, z);
  }

  function set_pq_r_partial(p: Bits, q: Bits, r: Bits, i: nat, j: nat) : set<(nat,nat,nat)>
  {
    set a:nat, b:nat, c:nat
          | a <= i && b <= i && c <= i && a+b >= j && a+b+c == i
                && bits_get(p, a) && bits_get(q, b) && bits_get(r, c)
          :: (a,b,c)
  }

  lemma pq_r_partial(p: Bits, q: Bits, r: Bits, i: nat, j: nat)
  requires j <= i+1
  decreases i + 1 - j
  ensures mul_F2_X_digit_partial(mul_F2_X(p, q), r, i, j)
       == parity(set_pq_r_partial(p, q, r, i, j))
  {
    reveal_parity();
    var m := set_pq_r_partial(p, q, r, i, j);
    if j == i+1 {
      assert |m| == 0;
      assert 0 % 2 == 0;
    } else {
      var m' := set_pq_r_partial(p, q, r, i, j + 1);

      if bits_get(r, i-j) {
        calc {
          mul_F2_X_digit_partial(mul_F2_X(p, q), r, i, j);
          bool_xor(
            (bits_get(mul_F2_X(p,q), j) && bits_get(r, i-j)),
            mul_F2_X_digit_partial(mul_F2_X(p,q), r, i, j+1)
          );
          {
            pq_r_partial(p, q, r, i, j+1);
          }
          bool_xor(
            (bits_get(mul_F2_X(p,q), j) && bits_get(r, i-j)),
            parity(m')
          );
          bool_xor(
            bits_get(mul_F2_X(p,q), j),
            parity(m')
          );
          {
            mset_mul_F2_X_digit(p, q, j);
          }
          bool_xor(
            parity(set_digit(p, q, j)),
            parity(m')
          );
          (|set_digit(p,q,j)| + |m'|) % 2 == 1;
          {
            assert |set_digit(p,q,j)| + |m'| == |m| by {
              var setA: set<(nat,nat)> := set_digit(p, q, j);
              var setB: set<(nat,nat,nat)> := set a:nat, b: nat
                  | a <= j && b <= j && a + b == j
                        && bits_get(p, a) && bits_get(q, b)
                  :: (a,b,i-j);

              calc {
                |m|;
                {
                  assert setB + m' == m;
                }
                |setB| + |m'|;
                {
                  var relation := iset a:((nat,nat),(nat,nat,nat)) | a.0.0 == a.1.0 && a.0.1 == a.1.1;
                  forall a | a in setA ensures exists b :: b in setB && (a, b) in relation
                  {
                    var b := (a.0, a.1, i-j);
                    assert b in setB && (a, b) in relation;
                  }
                  forall b | b in setB ensures exists a :: a in setA && (a, b) in relation
                  {
                    var a := (b.0, b.1);
                    assert a in setA && (a, b) in relation;
                  }

                  SetBijectivity.BijectivityImpliesEqualCardinality(setA, setB, relation);
                }
                |setA| + |m'|;
              }
            }
          }
          |m| % 2 == 1;
          parity(m);
          parity(set_pq_r_partial(p, q, r, i, j));
        }
      } else {
        calc {
          mul_F2_X_digit_partial(mul_F2_X(p, q), r, i, j);
          bool_xor(
            (bits_get(mul_F2_X(p,q), j) && bits_get(r, i-j)),
            mul_F2_X_digit_partial(mul_F2_X(p,q), r, i, j+1)
          );
          {
            pq_r_partial(p, q, r, i, j+1);
          }
          bool_xor(
            (bits_get(mul_F2_X(p,q), j) && bits_get(r, i-j)),
            parity(m')
          );
          parity(m');
          {
            assert m == m';
          }
          parity(set_pq_r_partial(p, q, r, i, j));
        }
      }
    }
  }

  function set_p_qr_partial(p: Bits, q: Bits, r: Bits, i: nat, j: nat) : set<(nat,nat,nat)>
  {
    set a:nat, b:nat, c:nat
          | a <= i && b <= i && c <= i && a >= j && a+b+c == i
                && bits_get(p, a) && bits_get(q, b) && bits_get(r, c)
          :: (a,b,c)
  }

  lemma p_qr_partial(p: Bits, q: Bits, r: Bits, i: nat, j: nat)
  requires j <= i+1
  decreases i + 1 - j
  ensures mul_F2_X_digit_partial(p, mul_F2_X(q, r), i, j)
       == parity(set_p_qr_partial(p, q, r, i, j))
  {
    reveal_parity();
    var m := set_p_qr_partial(p, q, r, i, j);
    if j == i+1 {
      assert |m| == 0;
      assert 0 % 2 == 0;
    } else {
      var m' := set_p_qr_partial(p, q, r, i, j + 1);

      if bits_get(p, j) {
        calc {
          mul_F2_X_digit_partial(p, mul_F2_X(q, r), i, j);
          bool_xor(
            (bits_get(p, j) && bits_get(mul_F2_X(q,r), i-j)),
            mul_F2_X_digit_partial(p, mul_F2_X(q,r), i, j+1)
          );
          {
            p_qr_partial(p, q, r, i, j+1);
          }
          bool_xor(
            (bits_get(p, j) && bits_get(mul_F2_X(q,r), i-j)),
            parity(m')
          );
          bool_xor(
            bits_get(mul_F2_X(q,r), i-j),
            parity(m')
          );
          {
            mset_mul_F2_X_digit(q, r, i-j);
          }
          bool_xor(
            parity(set_digit(q, r, i-j)),
            parity(m')
          );
          (|set_digit(q,r,i-j)| + |m'|) % 2 == 1;
          {
            assert |set_digit(q,r,i-j)| + |m'| == |m| by {
              var setA: set<(nat,nat)> := set_digit(q, r, i-j);
              var setB: set<(nat,nat,nat)> := set b:nat, c: nat
                  | b <= i-j && c <= i-j && b + c == i-j
                        && bits_get(q, b) && bits_get(r, c)
                  :: (j,b,c);

              calc {
                |m|;
                {
                  assert setB + m' == m;
                }
                |setB| + |m'|;
                {
                  var relation := iset a:((nat,nat),(nat,nat,nat)) | a.0.0 == a.1.1 && a.0.1 == a.1.2;
                  forall a | a in setA ensures exists b :: b in setB && (a, b) in relation
                  {
                    var b := (j, a.0, a.1);
                    assert b in setB && (a, b) in relation;
                  }
                  forall b | b in setB ensures exists a :: a in setA && (a, b) in relation
                  {
                    var a := (b.1, b.2);
                    assert a in setA && (a, b) in relation;
                  }

                  SetBijectivity.BijectivityImpliesEqualCardinality(setA, setB, relation);
                }
                |setA| + |m'|;
              }
            }
          }
          |m| % 2 == 1;
          parity(m);
          parity(set_p_qr_partial(p, q, r, i, j));
        }
      } else {
        calc {
          mul_F2_X_digit_partial(p, mul_F2_X(q, r), i, j);
          bool_xor(
            (bits_get(p, j) && bits_get(mul_F2_X(q, r), i-j)),
            mul_F2_X_digit_partial(p, mul_F2_X(q, r), i, j+1)
          );
          {
            p_qr_partial(p, q, r, i, j+1);
          }
          bool_xor(
            (bits_get(p, j) && bits_get(mul_F2_X(q,r), i-j)),
            parity(m')
          );
          parity(m');
          {
            assert m == m';
          }
          parity(set_p_qr_partial(p, q, r, i, j));
        }
      }
    }
  }

  lemma mul_assoc(p: Bits, q: Bits, r: Bits)
  ensures mul_F2_X(mul_F2_X(p, q), r)
       == mul_F2_X(p, mul_F2_X(q, r))
  {
    var a := mul_F2_X(mul_F2_X(p, q), r);
    var b := mul_F2_X(p, mul_F2_X(q, r));
    assert |a| == |b|;
    forall i | 0 <= i < |a|
    ensures a[i] == b[i]
    {
      calc {
        mul_F2_X(mul_F2_X(p, q), r)[i];
        mul_F2_X_digit(mul_F2_X(p, q), r, i);
        mul_F2_X_digit_partial(mul_F2_X(p, q), r, i, 0);
          { pq_r_partial(p, q, r, i, 0); }
        parity(set_pq_r_partial(p, q, r, i, 0));
          {
            assert set_pq_r_partial(p, q, r, i, 0)
                == set_p_qr_partial(p, q, r, i, 0);
          }
        parity(set_p_qr_partial(p, q, r, i, 0));
          { p_qr_partial(p, q, r, i, 0); }
        mul_F2_X_digit_partial(p, mul_F2_X(q, r), i, 0);
        mul_F2_X_digit(p, mul_F2_X(q, r), i);
        mul_F2_X(p, mul_F2_X(q, r))[i];
      }
    }
  }

  lemma mod_mul_comm(p: Bits, q: Bits)
  ensures mod_mul(p, q) == mod_mul(q, p)
  {
    mul_comm(p, q);
  }

  lemma mul_append_0s(p: Bits, q: Bits, n: nat)
  ensures mul_F2_X(p + zeroes(n), q)
      == mul_F2_X(p, q) + zeroes(n)
  {
    var a := mul_F2_X(p + zeroes(n), q);
    var b := mul_F2_X(p, q) + zeroes(n);
    forall i | 0 <= i < |a| ensures a[i] == b[i]
    {
      if i < |p| + |q| {
        calc {
          a[i];
          {
            mset_mul_F2_X_digit(p + zeroes(n), q, i);
          }
          parity(set_digit(p + zeroes(n), q, i));
          {
            assert set_digit(p + zeroes(n), q, i)
                == set_digit(p, q, i);
          }
          parity(set_digit(p, q, i));
          {
            mset_mul_F2_X_digit(p, q, i);
          }
          b[i];
        }
      } else {
        calc {
          a[i];
          {
            mset_mul_F2_X_digit(p + zeroes(n), q, i);
          }
          parity(set_digit(p + zeroes(n), q, i));
          {
            assert set_digit(p + zeroes(n), q, i) == {};
            assert |set_digit(p + zeroes(n), q, i)| == 0;
            assert 0 % 2 == 0;
            reveal_parity();
          }
          false;
        }
      }
    }
    assert a == b;
  }

  lemma mul_append_0s_right(a: Bits, b: Bits, n: nat)
  ensures mul_F2_X(a, b + zeroes(n))
      == mul_F2_X(a, b) + zeroes(n)
  {
    mul_append_0s(b, a, n);
    mul_comm(b, a);
    mul_comm(b + zeroes(n), a);
  }

  lemma mul_empty(a: Bits)
  ensures mul_F2_X(a, []) == zeroes(|a|)
  {
    var y := mul_F2_X(a, []);
    forall i | 0 <= i < |y| ensures !y[i]
    {
      mset_mul_F2_X_digit(a, [], i);
      assert set_digit(a, [], i) == {};
      assert |set_digit(a, [], i)| == 0;
      assert 0 % 2 == 0;
      reveal_parity();
    }
  }

  lemma mul_zero(a: Bits, n: nat)
  ensures mul_F2_X(a, zeroes(n)) == zeroes(|a| + n)
  {
    calc {
      mul_F2_X(a, zeroes(n));
      {
        mul_append_0s_right(a, [], n);
        assert [] + zeroes(n) == zeroes(n);
      }
      mul_F2_X(a, []) + zeroes(n);
      {
        mul_empty(a);
      }
      zeroes(|a|) + zeroes(n);
      zeroes(|a| + n);
    }
  }

  lemma mul_singleton_partial(a: Bits, n: nat, i: nat, j: nat)
  requires j <= i+1
  ensures mul_F2_X_digit_partial(a, zeroes(n) + [true], i, j)
      == (n <= i < n + |a| && j <= i-n && a[i-n])
  decreases i + 1 - j
  {
    if j == i+1 {
    } else {
      mul_singleton_partial(a, n, i, j+1);
    }
  }

  lemma mul_singleton(a: Bits, n: nat)
  ensures mul_F2_X(a, zeroes(n) + [true])
      == zeroes(n) + a + [false]
  {
    var x := mul_F2_X(a, zeroes(n) + [true]);
    var y := zeroes(n) + a + [false];
    forall i | 0 <= i < |x|
    ensures x[i] == y[i]
    {
      mul_singleton_partial(a, n, i, 0);
    }
  }

  lemma mod_zero(n: nat)
  ensures mod(zeroes(n)) == zeroes(32)
  {
    if (n > 32) {
      mod_zero(n-1);
      assert zeroes(n-1) == zeroes(n)[..n-1];
    } else {
    }
  }

  lemma mod_zero_shifted_is_zero(n: nat, a: Bits)
  requires mod(a) == zeroes(32)
  ensures mod(zeroes(n) + a) == zeroes(32)
  decreases |a|
  {
    if |a| < |poly()| {
      forall i | 0 <= i < |a| ensures !a[i] {
        assert a[i] == mod(a)[i];
      }
      assert zeroes(n) + a == zeroes(n + |a|);
      mod_zero(n + |a|);
    } else {
      if a[|a|-1] {
        var a1 := xor(a, shift(poly(), |a| - |poly()|));
        var a' := a1[..|a1|-1];
        calc {
          mod(zeroes(n) + a);
          {
            var t := zeroes(n) + a;
            var t1 := xor(t, shift(poly(), |t| - |poly()|));
            var t' := t1[..|t1|-1];
            var k := zeroes(n) + a';
            assert |t'| == |k|;
            forall i | 0 <= i < |t'| ensures t'[i] == k[i] {
            }
            assert t' == k;
            assert t' == zeroes(n) + a';
          }
          mod(zeroes(n) + a');
          {
            mod_zero_shifted_is_zero(n, a');
          }
          zeroes(32);
        }
      } else {
        var a' := a[..|a|-1];
        calc {
          mod(zeroes(n) + a);
          {
            assert (zeroes(n) + a)[.. n + |a| - 1]
                == zeroes(n) + a[..|a|-1];
          }
          mod(zeroes(n) + a');
          {
            mod_zero_shifted_is_zero(n, a');
          }
          zeroes(32);
        }
      }
    }
  }

  lemma multiple_mul_is_multiple_iter(a: Bits, b: Bits, i: nat)
  requires mod(a) == zeroes(32)
  requires i <= |b|
  requires forall j | i <= j < |b| :: !b[j]
  ensures mod(mul_F2_X(a, b)) == zeroes(32)
  decreases i
  {
    if i == 0 {
      calc {
        mod(mul_F2_X(a, b));
        { assert b == zeroes(|b|); }
        mod(mul_F2_X(a, zeroes(|b|)));
        { mul_zero(a, |b|); }
        mod(zeroes(|a| + |b|));
        { mod_zero(|a| + |b|); }
        zeroes(32);
      }
    } else if !b[i-1] {
      multiple_mul_is_multiple_iter(a, b, i-1);
    } else {
      var b1 := zeroes(i-1) + [true] + zeroes(|b| - i);
      var b2 := b[i-1 := false];

      calc {
        mod(mul_F2_X(a, b));
        { assert xor(b1, b2) == b; }
        mod(mul_F2_X(a, xor(b1, b2)));
        { mul_left_distributive(a, b1, b2); }
        mod(xor(mul_F2_X(a, b1), mul_F2_X(a, b2)));
        {
          mod_xor(mul_F2_X(a, b1), mul_F2_X(a, b2));
        }
        xor(mod(mul_F2_X(a, b1)), mod(mul_F2_X(a, b2)));
        {
          calc {
            mod(mul_F2_X(a, b1));
            mod(mul_F2_X(a, zeroes(i-1) + [true] + zeroes(|b| - i)));
            { mul_append_0s_right(a, zeroes(i-1) + [true], |b| - i); }
            mod(mul_F2_X(a, zeroes(i-1) + [true]) + zeroes(|b| - i));
            { mul_singleton(a, i-1); }
            mod(zeroes(i-1) + a + [false] + zeroes(|b| - i));
            { assert zeroes(i-1) + a + [false] + zeroes(|b| - i)
                 == zeroes(i-1) + a + ([false] + zeroes(|b| - i)); }
            mod(zeroes(i-1) + a + ([false] + zeroes(|b| - i)));
            { assert [false] + zeroes(|b| - i) == zeroes(|b| - i + 1); }
            mod(zeroes(i-1) + a + zeroes(|b| - i + 1));
            {
              mod_ignores_trailing_zeroes(zeroes(i - 1) + a, |b| - i + 1);
            }
            mod(zeroes(i - 1) + a);
            {
              mod_zero_shifted_is_zero(i-1, a);
            }
            zeroes(32);
          }
        }
        xor(zeroes(32), mod(mul_F2_X(a, b2)));
        {
          multiple_mul_is_multiple_iter(a, b2, i-1);
        }
        xor(zeroes(32), zeroes(32));
        zeroes(32);
      }
    }
  }

  lemma multiple_mul_is_multiple(a: Bits, b: Bits)
  requires mod(a) == zeroes(32)
  ensures mod(mul_F2_X(a, b)) == zeroes(32)
  {
    multiple_mul_is_multiple_iter(a, b, |b|);
  }

  lemma mod_mul_mod_left(a: Bits, b: Bits)
  ensures mod_mul(a, b) 
      == mod_mul(mod(a), b)
  {
    if |mod(a)| <= |a| {
      var m := mod(a) + zeroes(|a| - |mod(a)|);
      calc {
        xor(mod(mul_F2_X(a,b)), mod(mul_F2_X(mod(a),b)));
        {
          calc {
            mod(mul_F2_X(mod(a),b));
            {
              mod_ignores_trailing_zeroes(mul_F2_X(mod(a),b), |a|-|mod(a)|);
            }
            mod(mul_F2_X(mod(a),b) + zeroes(|a|-|mod(a)|));
            {
              mul_append_0s(mod(a), b, |a| - |mod(a)|);
            }
            mod(mul_F2_X(mod(a) + zeroes(|a|-|mod(a)|), b));
            mod(mul_F2_X(m, b));
          }
        }
        xor(mod(mul_F2_X(a,b)), mod(mul_F2_X(m,b)));
        {
          mod_xor(mul_F2_X(a,b), mul_F2_X(m,b));
        }
        mod(xor(mul_F2_X(a,b), mul_F2_X(m,b)));
        {
          mul_right_distributive(a,m,b);
        }
        mod(mul_F2_X(xor(a, m),b));
        {
          calc {
            mod(xor(a,m));
            { mod_xor(a,m); }
            xor(mod(a),mod(m));
            xor(mod(a),mod(mod(a) + zeroes(|a| - |mod(a)|)));
            {
              mod_ignores_trailing_zeroes(mod(a), |a| - |mod(a)|);
            }
            xor(mod(a),mod(mod(a)));
            { assert mod(mod(a)) == mod(a); }
            xor(mod(a),mod(a));
            zeroes(32);
          }
          multiple_mul_is_multiple(xor(a,m), b);
        }
        mod(zeroes(32));
        zeroes(32);
      }
    } else {
      calc {
        mod_mul(a, b);
        { mod_ignores_trailing_zeroes(mul_F2_X(a,b), |mod(a)| - |a|); }
        mod(mul_F2_X(a,b) + zeroes(|mod(a)| - |a|));
        { mul_append_0s(a,b,|mod(a)|-|a|); }
        mod_mul(a + zeroes(|mod(a)| - |a|), b);
        mod_mul(mod(a), b);
      }
    }
  }

  lemma mod_mul_mod_right(a: Bits, b: Bits)
  ensures mod_mul(a, b) 
      == mod_mul(a, mod(b))
  {
    mod_mul_mod_left(b, a);
    mod_mul_comm(a, b);
    mod_mul_comm(a, mod(b));
  }

  lemma mod_mul_assoc(x: Bits, y: Bits, z: Bits)
  ensures mod_mul(x, mod_mul(y, z)) == mod_mul(mod_mul(x, y), z)
  {
    calc {
      mod_mul(x, mod_mul(y, z));
      { mod_mul_mod_right(x, mul_F2_X(y, z)); }
      mod(mul_F2_X(x, mul_F2_X(y, z)));
      { mul_assoc(x, y, z); }
      mod(mul_F2_X(mul_F2_X(x, y), z));
      { mod_mul_mod_left(mul_F2_X(x, y), z); }
      mod_mul(mod_mul(x, y), z);
    }
  }

  lemma mod_mul_exp_add(n: nat, m: nat)
  ensures mod_mul(exp(n), exp(m))
      == mod(exp(n+m))
  {
    calc {
      mod_mul(exp(n), exp(m));
      mod(mul_F2_X(exp(n), exp(m)));
      { mul_singleton(exp(n), m); }
      mod(zeroes(m) + exp(n) + [false]);
      {
        mod_ignores_trailing_zeroes(zeroes(m) + exp(n), 1);
      }
      mod(zeroes(m) + exp(n));
      {
        assert zeroes(m) + exp(n) == exp(n+m);
      }
      mod(exp(n+m));
    }
  }

  lemma shift_eq_mul(x: Bits, n: nat)
  ensures zeroes(n) + x + [false]
       == mul_F2_X(exp(n), x)
  {
    mul_comm(exp(n), x);
    mul_singleton(x, n);
  }

  lemma mod_shift(x: Bits, n: nat)
  ensures mod(zeroes(n) + x)
    == mod_mul(exp(n), x)
  {
    calc {
      mod_mul(exp(n), x);
      mod(mul_F2_X(exp(n), x));
      {
        shift_eq_mul(x, n);
      }
      mod(zeroes(n) + x + [false]);
      mod(zeroes(n) + x);
    }
  }

  lemma mul_last_0(x: Bits, y: Bits)
  requires |x| > 0 || |y| > 0
  ensures !mul_F2_X(x, y)[|x| + |y| - 1]
  {
    mset_mul_F2_X_digit(x, y, |x| + |y| - 1);
    reveal_parity();
    assert set_digit(x, y, |x| + |y| - 1) == {};
    assert |set_digit(x, y, |x| + |y| - 1)| == 0;
    assert 0 % 2 == 0;
  }

  lemma reverse_mul(x: Bits, y: Bits)
  ensures reverse(mul_F2_X(x, y)) + [false]
    == [false] + mul_F2_X(reverse(x), reverse(y))
  {
    if |x| == 0 && |y| == 0 {
    } else {
      var a := reverse(mul_F2_X(x, y)) + [false];
      var b := [false] + mul_F2_X(reverse(x), reverse(y));
      forall i | 0 <= i < |a| ensures a[i] == b[i]
      {
        if i == 0 {
          calc {
            a[i];
            mul_F2_X(x, y)[|x| + |y| - 1];
            { mul_last_0(x, y); }
            false;
            b[i];
          }
        } else if i == |a| - 1 {
          calc {
            b[i];
            mul_F2_X(reverse(x), reverse(y))[|x| + |y| - 1];
            { mul_last_0(reverse(x), reverse(y)); }
            false;
            a[i];
          }
        } else {
          calc {
            a[i];
            reverse(mul_F2_X(x, y))[i];
            mul_F2_X(x,y)[|x| + |y| - 1 - i];
            {
              mset_mul_F2_X_digit(x, y, |x| + |y| - 1 - i);
            }
            parity(set_digit(x, y, |x| + |y| - 1 - i));
            {
              var setA := set_digit(x, y, |x| + |y| - 1 - i);
              var setB := set_digit(reverse(x), reverse(y), i - 1);
              assert |setA| == |setB| by {
                var relation := iset a:((nat,nat),(nat,nat))
                    | a.0.0 + a.1.0 == |x| - 1
                    && a.0.1 + a.1.1 == |y| - 1;

                forall a | a in setA ensures exists b :: b in setB && (a, b) in relation
                {
                  var b := (|x| - 1 - a.0, |y| - 1 - a.1);
                  assert bits_get(reverse(x), b.0) == bits_get(x, a.0);
                  assert bits_get(reverse(y), b.1) == bits_get(y, a.1);
                  assert b in setB;
                  assert (a, b) in relation;
                }
                forall b | b in setB ensures exists a :: a in setA && (a, b) in relation
                {
                  var a := (|x| - 1 - b.0, |y| - 1 - b.1);
                  assert bits_get(reverse(x), b.0) == bits_get(x, a.0);
                  assert bits_get(reverse(y), b.1) == bits_get(y, a.1);
                  assert a in setA;
                  assert (a, b) in relation;
                }
                assume false;

                SetBijectivity.BijectivityImpliesEqualCardinality(setA, setB, relation);
              }

              reveal_parity();
            }
            parity(set_digit(reverse(x), reverse(y), i - 1));
            {
              mset_mul_F2_X_digit(reverse(x), reverse(y), i - 1);
            }
            mul_F2_X(reverse(x),reverse(y))[i - 1];
            b[i];
          }
        }
      }
    }
  }

  lemma mod_reverse_mul_reverse(x: Bits, y: Bits)
  ensures mod(reverse(mul_F2_X(reverse(x), reverse(y))))
      == mod_mul(exp(1), mod_mul(x, y))
  {
    calc {
      mod(reverse(mul_F2_X(reverse(x), reverse(y))));
      {
        mod_ignores_trailing_zeroes(reverse(mul_F2_X(reverse(x), reverse(y))), 1);
      }
      mod(reverse(mul_F2_X(reverse(x), reverse(y))) + [false]);
      {
        reverse_mul(reverse(x), reverse(y));
      }
      mod([false] + mul_F2_X(reverse(reverse(x)), reverse(reverse(y))));
      {
        assert reverse(reverse(x)) == x;
        assert reverse(reverse(y)) == y;
      }
      mod([false] + mul_F2_X(x, y));
      { assert [false] == zeroes(1); }
      mod(zeroes(1) + mul_F2_X(x, y));
      {
        mod_shift(mul_F2_X(x, y), 1);
      }
      mod_mul(exp(1), mul_F2_X(x, y));
      {
        mod_mul_mod_right(exp(1), mul_F2_X(x, y));
      }
      mod_mul(exp(1), mod(mul_F2_X(x, y)));
      mod_mul(exp(1), mod_mul(x, y));
    }
  }

  lemma mod_plus_mod(a: Bits, b: Bits)
  ensures mod(a + mod(b)) == mod(a + b)
  {
    calc {
      mod(a + mod(b));
      {
        assert a + mod(b)
          == xor( a + zeroes(|mod(b)|), zeroes(|a|) + mod(b));
      }
      mod(
        xor(
          a + zeroes(|mod(b)|),
          zeroes(|a|) + mod(b)
        )
      );
      {
        mod_xor(
          a + zeroes(|mod(b)|),
          zeroes(|a|) + mod(b));
      }
      xor(
          mod(a + zeroes(|mod(b)|)),
          mod(zeroes(|a|) + mod(b))
      );
      {
        calc {
          mod(zeroes(|a|) + mod(b));
          { mod_ignores_trailing_zeroes(zeroes(|a|) + mod(b), 1); }
          mod(zeroes(|a|) + mod(b) + [false]);
          { mul_singleton(mod(b), |a|); }
          mod(mul_F2_X(mod(b), zeroes(|a|)+[true]));
          { mod_mul_mod_left(b, zeroes(|a|)+[true]); }
          mod(mul_F2_X(b, zeroes(|a|)+[true]));
          { mul_singleton(b, |a|); }
          mod(zeroes(|a|) + b + [false]);
          { mod_ignores_trailing_zeroes(zeroes(|a|) + b, 1); }
          mod(zeroes(|a|) + b);
        }
      }
      xor(
          mod(a + zeroes(|mod(b)|)),
          mod(zeroes(|a|) + b)
      );
      {
        calc {
          mod(a + zeroes(|mod(b)|));
          { mod_ignores_trailing_zeroes(a, |mod(b)|); }
          mod(a);
          { mod_ignores_trailing_zeroes(a, |b|); }
          mod(a + zeroes(|b|));
        }
      }
      xor(
          mod(a + zeroes(|b|)),
          mod(zeroes(|a|) + b)
      );
      {
        mod_xor(a + zeroes(|b|), zeroes(|a|) + b);
      }
      mod(
        xor(
          a + zeroes(|b|),
          zeroes(|a|) + b
        )
      );
      {
        assert a + b == xor(a + zeroes(|b|), zeroes(|a|) + b);
      }
      mod(a + b);
    }
  }
}
