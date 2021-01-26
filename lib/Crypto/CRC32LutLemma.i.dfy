include "../Lang/System/F2_X.s.dfy"
include "F2_X_Lemmas.i.dfy"
include "../Marshalling/Math.i.dfy"
include "CRC32PowDef.i.dfy"

module CRC32_C_Lut_Lemma {
  import opened Bits_s
  import opened F2_X_s
  import opened NativeTypes
  import opened Math
  import opened F2_X_Lemmas
  import opened CRC32PowDef

  function pow_mod_crc(n: nat) : seq<bool>
  requires n >= 33
  {
    reverse(mod_F2_X(zeroes(n-33) + [true], bits_of_int(0x1_1EDC_6F41, 33)))
  }

  lemma shift1(a0: bool, a1: bool, a2: bool, a3: bool, a4: bool, a5: bool, a6: bool, a7: bool, a8: bool, a9: bool, a10: bool, a11: bool, a12: bool, a13: bool, a14: bool, a15: bool, a16: bool, a17: bool, a18: bool, a19: bool, a20: bool, a21: bool, a22: bool, a23: bool, a24: bool, a25: bool, a26: bool, a27: bool, a28: bool, a29: bool, a30: bool, a31: bool)
  requires a0 == false
  ensures [false] + [ a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, false ]
    == [ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31 ] + [false]
  {
    var x := [false] + [ a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, false ];
    var y := [ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31 ] + [false];
    assert |x| == |y|;
    forall i | 0 <= i < |x| ensures x[i] == y[i] {
      if i == 0 { assert x[0] == false; assert y[0] == false; }
      else if i == 1 { assert x[1] == a1; assert y[1] == a1; }
      else if i == 2 { assert x[2] == a2; assert y[2] == a2; }
      else if i == 3 { assert x[3] == a3; assert y[3] == a3; }
      else if i == 4 { assert x[4] == a4; assert y[4] == a4; }
      else if i == 5 { assert x[5] == a5; assert y[5] == a5; }
      else if i == 6 { assert x[6] == a6; assert y[6] == a6; }
      else if i == 7 { assert x[7] == a7; assert y[7] == a7; }
      else if i == 8 { assert x[8] == a8; assert y[8] == a8; }
      else if i == 9 { assert x[9] == a9; assert y[9] == a9; }
      else if i == 10 { assert x[10] == a10; assert y[10] == a10; }
      else if i == 11 { assert x[11] == a11; assert y[11] == a11; }
      else if i == 12 { assert x[12] == a12; assert y[12] == a12; }
      else if i == 13 { assert x[13] == a13; assert y[13] == a13; }
      else if i == 14 { assert x[14] == a14; assert y[14] == a14; }
      else if i == 15 { assert x[15] == a15; assert y[15] == a15; }
      else if i == 16 { assert x[16] == a16; assert y[16] == a16; }
      else if i == 17 { assert x[17] == a17; assert y[17] == a17; }
      else if i == 18 { assert x[18] == a18; assert y[18] == a18; }
      else if i == 19 { assert x[19] == a19; assert y[19] == a19; }
      else if i == 20 { assert x[20] == a20; assert y[20] == a20; }
      else if i == 21 { assert x[21] == a21; assert y[21] == a21; }
      else if i == 22 { assert x[22] == a22; assert y[22] == a22; }
      else if i == 23 { assert x[23] == a23; assert y[23] == a23; }
      else if i == 24 { assert x[24] == a24; assert y[24] == a24; }
      else if i == 25 { assert x[25] == a25; assert y[25] == a25; }
      else if i == 26 { assert x[26] == a26; assert y[26] == a26; }
      else if i == 27 { assert x[27] == a27; assert y[27] == a27; }
      else if i == 28 { assert x[28] == a28; assert y[28] == a28; }
      else if i == 29 { assert x[29] == a29; assert y[29] == a29; }
      else if i == 30 { assert x[30] == a30; assert y[30] == a30; }
      else if i == 31 { assert x[31] == a31; assert y[31] == a31; }
      else if i == 32 { assert x[32] == false; assert y[32] == false; }
    }
    seq_ext(x, y);
  }

  lemma shift2(a0: bool, a1: bool, a2: bool, a3: bool, a4: bool, a5: bool, a6: bool, a7: bool, a8: bool, a9: bool, a10: bool, a11: bool, a12: bool, a13: bool, a14: bool, a15: bool, a16: bool, a17: bool, a18: bool, a19: bool, a20: bool, a21: bool, a22: bool, a23: bool, a24: bool, a25: bool, a26: bool, a27: bool, a28: bool, a29: bool, a30: bool, a31: bool, x: seq<bool>, y: seq<bool>, y1: seq<bool>)
  requires a0 == true
  requires x == [ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31 ];
  requires y == [ a1, a2, a3, a4, a5, !a6, a7, !a8, !a9, !a10, !a11, a12, !a13, !a14, a15, a16, a17, !a18, !a19, !a20, a21, !a22, !a23, a24, !a25, !a26, !a27, !a28, a29, a30, a31, true ];
  requires y1 == [false] + y
  ensures xor(y1, poly())[..32] == x
  {
    var z := xor(y1, poly())[..32];
    assert |x| == |z|;
    forall i | 0 <= i < |x| ensures x[i] == z[i] {
      if i == 0 { assert x[0] == true; assert z[0] == true; }
      else if i == 1 { assert x[1] == a1; assert z[1] == a1; }
      else if i == 2 { assert x[2] == a2; assert z[2] == a2; }
      else if i == 3 { assert x[3] == a3; assert z[3] == a3; }
      else if i == 4 { assert x[4] == a4; assert z[4] == a4; }
      else if i == 5 { assert x[5] == a5; assert z[5] == a5; }
      else if i == 6 { assert x[6] == a6; assert z[6] == a6; }
      else if i == 7 { assert x[7] == a7; assert z[7] == a7; }
      else if i == 8 { assert x[8] == a8; assert z[8] == a8; }
      else if i == 9 { assert x[9] == a9; assert z[9] == a9; }
      else if i == 10 { assert x[10] == a10; assert z[10] == a10; }
      else if i == 11 { assert x[11] == a11; assert z[11] == a11; }
      else if i == 12 { assert x[12] == a12; assert z[12] == a12; }
      else if i == 13 { assert x[13] == a13; assert z[13] == a13; }
      else if i == 14 { assert x[14] == a14; assert z[14] == a14; }
      else if i == 15 { assert x[15] == a15; assert z[15] == a15; }
      else if i == 16 { assert x[16] == a16; assert z[16] == a16; }
      else if i == 17 { assert x[17] == a17; assert z[17] == a17; }
      else if i == 18 { assert x[18] == a18; assert z[18] == a18; }
      else if i == 19 { assert x[19] == a19; assert z[19] == a19; }
      else if i == 20 { assert x[20] == a20; assert z[20] == a20; }
      else if i == 21 { assert x[21] == a21; assert z[21] == a21; }
      else if i == 22 { assert x[22] == a22; assert z[22] == a22; }
      else if i == 23 { assert x[23] == a23; assert z[23] == a23; }
      else if i == 24 { assert x[24] == a24; assert z[24] == a24; }
      else if i == 25 { assert x[25] == a25; assert z[25] == a25; }
      else if i == 26 { assert x[26] == a26; assert z[26] == a26; }
      else if i == 27 { assert x[27] == a27; assert z[27] == a27; }
      else if i == 28 { assert x[28] == a28; assert z[28] == a28; }
      else if i == 29 { assert x[29] == a29; assert z[29] == a29; }
      else if i == 30 { assert x[30] == a30; assert z[30] == a30; }
      else if i == 31 { assert x[31] == a31; assert z[31] == a31; }
      else if i == 32 { assert x[32] == false; assert z[32] == false; }
    }
    seq_ext(x, z);
  }

  lemma of_pow1(n: nat,
      a0: bool, a1: bool, a2: bool, a3: bool, a4: bool, a5: bool, a6: bool, a7: bool, a8: bool, a9: bool, a10: bool, a11: bool, a12: bool, a13: bool, a14: bool, a15: bool, a16: bool, a17: bool, a18: bool, a19: bool, a20: bool, a21: bool, a22: bool, a23: bool, a24: bool, a25: bool, a26: bool, a27: bool, a28: bool, a29: bool, a30: bool, a31: bool)
  requires pow(n, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31)
  ensures mod_F2_X(zeroes(n) + [true], bits_of_int(0x1_1EDC_6F41, 33))
    == [
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
      a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31
     ]
  {
    assume false; // TODO
    var x := [ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31 ];
    if (n == 0) {
    } else {
      if !a0 {
        var y := [ a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, false ];
        calc {
          mod_F2_X(zeroes(n) + [true], bits_of_int(0x1_1EDC_6F41, 33));
          mod(zeroes(n) + [true]);
          { mod_mul_exp_add(n-1, 1); }
          mod(mul_F2_X(exp(n-1), exp(1)));
          { mod_mul_mod_left(exp(n-1), exp(1)); }
          mod(mul_F2_X(mod(exp(n-1)), exp(1)));
          {
            assert exp(n-1) == zeroes(n-1) + [true];
            assert exp(1) == [false, true];
          }
          mod(mul_F2_X(mod(zeroes(n-1) + [true]), [false, true]));
          mod(mul_F2_X(y, [false, true]));
          { assert [false, true] == zeroes(1) + [true]; }
          mod(mul_F2_X(y, zeroes(1) + [true]));
          { mul_singleton(y, 1); }
          mod(zeroes(1) + y + [false]);
          { assert zeroes(1) == [false]; }
          mod([false] + y + [false]);
          { mod_ignores_trailing_zeroes([false] + y, 1); }
          mod([false] + y);
          {
            shift1(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31);
          }
          mod(x + [false]);
          { mod_ignores_trailing_zeroes(x, 1); }
          mod(x);
          { assert |x| == 32; }
          x;
        }
      } else {
        var y := [ a1, a2, a3, a4, a5, !a6, a7, !a8, !a9, !a10, !a11, a12, !a13, !a14, a15, a16, a17, !a18, !a19, !a20, a21, !a22, !a23, a24, !a25, !a26, !a27, !a28, a29, a30, a31, true ];
        var y1 := [ false ] + y;
        calc {
          mod_F2_X(zeroes(n) + [true], bits_of_int(0x1_1EDC_6F41, 33));
          mod(zeroes(n) + [true]);
          { mod_mul_exp_add(n-1, 1); }
          mod(mul_F2_X(exp(n-1), exp(1)));
          { mod_mul_mod_left(exp(n-1), exp(1)); }
          mod(mul_F2_X(mod(exp(n-1)), exp(1)));
          {
            assert exp(n-1) == zeroes(n-1) + [true];
            assert exp(1) == [false, true];
          }
          mod(mul_F2_X(mod(zeroes(n-1) + [true]), [false, true]));
          mod(mul_F2_X(y, [false, true]));
          { assert [false, true] == zeroes(1) + [true]; }
          mod(mul_F2_X(y, zeroes(1) + [true]));
          { mul_singleton(y, 1); }
          mod(zeroes(1) + y + [false]);
          { assert zeroes(1) == [false]; }
          mod([false] + y + [false]);
          { mod_ignores_trailing_zeroes([false] + y, 1); }
          mod([false] + y);
          mod(y1);
          mod_F2_X(xor(y1, shift(poly(), 0))[..32], poly());
          xor(y1, shift(poly(), 0))[..32];
          { assert shift(poly(), 0) == poly(); }
          xor(y1, poly())[..32];
          {
            shift2(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, x, y, y1);
          }
          x;
        }
      }
    }
  }

  lemma seq_ext(x: seq<bool>, y: seq<bool>)
  requires |x| == |y|
  requires forall i | 0 <= i < |x| :: x[i] == y[i]
  ensures x == y
  {
  }

  lemma rev32(a0: bool, a1: bool, a2: bool, a3: bool, a4: bool, a5: bool, a6: bool, a7: bool, a8: bool, a9: bool, a10: bool, a11: bool, a12: bool, a13: bool, a14: bool, a15: bool, a16: bool, a17: bool, a18: bool, a19: bool, a20: bool, a21: bool, a22: bool, a23: bool, a24: bool, a25: bool, a26: bool, a27: bool, a28: bool, a29: bool, a30: bool, a31: bool)
  ensures reverse([
        a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
        a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31
       ]) == [
        a31, a30, a29, a28, a27, a26, a25, a24, a23, a22, a21, a20, a19, a18, a17, a16,
        a15, a14, a13, a12, a11, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, a0
      ]
  {
    assume false; // TODO
    var t := [ a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31 ];
    var x := reverse(t);
    var y := [ a31, a30, a29, a28, a27, a26, a25, a24, a23, a22, a21, a20, a19, a18, a17, a16, a15, a14, a13, a12, a11, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, a0 ];
    forall i | 0 <= i < |x| ensures x[i] == y[i] {
      if i == 0 { assert y[0] == a31; calc { x[0]; t[31]; a31; y[0]; } }
      else if i == 1 { assert y[1] == a30; calc { x[1]; t[30]; a30; y[1]; } }
      else if i == 2 { assert y[2] == a29; calc { x[2]; t[29]; a29; y[2]; } }
      else if i == 3 { assert y[3] == a28; calc { x[3]; t[28]; a28; y[3]; } }
      else if i == 4 { assert y[4] == a27; calc { x[4]; t[27]; a27; y[4]; } }
      else if i == 5 { assert y[5] == a26; calc { x[5]; t[26]; a26; y[5]; } }
      else if i == 6 { assert y[6] == a25; calc { x[6]; t[25]; a25; y[6]; } }
      else if i == 7 { assert y[7] == a24; calc { x[7]; t[24]; a24; y[7]; } }
      else if i == 8 { assert y[8] == a23; calc { x[8]; t[23]; a23; y[8]; } }
      else if i == 9 { assert y[9] == a22; calc { x[9]; t[22]; a22; y[9]; } }
      else if i == 10 { assert y[10] == a21; calc { x[10]; t[21]; a21; y[10]; } }
      else if i == 11 { assert y[11] == a20; calc { x[11]; t[20]; a20; y[11]; } }
      else if i == 12 { assert y[12] == a19; calc { x[12]; t[19]; a19; y[12]; } }
      else if i == 13 { assert y[13] == a18; calc { x[13]; t[18]; a18; y[13]; } }
      else if i == 14 { assert y[14] == a17; calc { x[14]; t[17]; a17; y[14]; } }
      else if i == 15 { assert y[15] == a16; calc { x[15]; t[16]; a16; y[15]; } }
      else if i == 16 { assert y[16] == a15; calc { x[16]; t[15]; a15; y[16]; } }
      else if i == 17 { assert y[17] == a14; calc { x[17]; t[14]; a14; y[17]; } }
      else if i == 18 { assert y[18] == a13; calc { x[18]; t[13]; a13; y[18]; } }
      else if i == 19 { assert y[19] == a12; calc { x[19]; t[12]; a12; y[19]; } }
      else if i == 20 { assert y[20] == a11; calc { x[20]; t[11]; a11; y[20]; } }
      else if i == 21 { assert y[21] == a10; calc { x[21]; t[10]; a10; y[21]; } }
      else if i == 22 { assert y[22] == a9; calc { x[22]; t[9]; a9; y[22]; } }
      else if i == 23 { assert y[23] == a8; calc { x[23]; t[8]; a8; y[23]; } }
      else if i == 24 { assert y[24] == a7; calc { x[24]; t[7]; a7; y[24]; } }
      else if i == 25 { assert y[25] == a6; calc { x[25]; t[6]; a6; y[25]; } }
      else if i == 26 { assert y[26] == a5; calc { x[26]; t[5]; a5; y[26]; } }
      else if i == 27 { assert y[27] == a4; calc { x[27]; t[4]; a4; y[27]; } }
      else if i == 28 { assert y[28] == a3; calc { x[28]; t[3]; a3; y[28]; } }
      else if i == 29 { assert y[29] == a2; calc { x[29]; t[2]; a2; y[29]; } }
      else if i == 30 { assert y[30] == a1; calc { x[30]; t[1]; a1; y[30]; } }
      else if i == 31 { assert y[31] == a0; calc { x[31]; t[0]; a0; y[31]; } }
    }
    seq_ext(x, y);
  }

  lemma {:fuel pow,0} {:fuel mod_F2_X,0} {:fuel bits_of_int,0} of_pow(n: nat,
      a0: bool, a1: bool, a2: bool, a3: bool, a4: bool, a5: bool, a6: bool, a7: bool, a8: bool, a9: bool, a10: bool, a11: bool, a12: bool, a13: bool, a14: bool, a15: bool, a16: bool, a17: bool, a18: bool, a19: bool, a20: bool, a21: bool, a22: bool, a23: bool, a24: bool, a25: bool, a26: bool, a27: bool, a28: bool, a29: bool, a30: bool, a31: bool)
  requires n >= 33
  requires pow(n-33, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31)
  ensures pow_mod_crc(n) == [
      a31, a30, a29, a28, a27, a26, a25, a24, a23, a22, a21, a20, a19, a18, a17, a16,
      a15, a14, a13, a12, a11, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, a0]
  {
    assume false; // TODO
    calc {
      pow_mod_crc(n);
      reverse(mod_F2_X(zeroes(n-33) + [true], bits_of_int(0x1_1EDC_6F41, 33)));
      {
        of_pow1(n-33, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
          a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31);
      }
      reverse([
        a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
        a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31
       ]);
      {
        var t := [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31];
        var x := reverse(t);
        var y :=         [a31, a30, a29, a28, a27, a26, a25, a24, a23, a22, a21, a20, a19, a18, a17, a16, a15, a14, a13, a12, a11, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, a0];
        assert |t| == 32;
        assert |x| == 32;
        assert |y| == 32;
        assert |x| == |y|;
        forall i | 0 <= i < |x| ensures x[i] == y[i] {
          if i == 0 { assert x[i] == y[i]; }
          else if i == 1 { assert x[i] == y[i]; }
          else if i == 2 { assert x[i] == y[i]; }
          else if i == 3 { assert x[i] == y[i]; }
          else if i == 4 { assert x[i] == y[i]; }
          else if i == 5 { assert x[i] == y[i]; }
          else if i == 6 { assert x[i] == y[i]; }
          else if i == 7 { assert x[i] == y[i]; }
          else if i == 8 { assert x[i] == y[i]; }
          else if i == 9 { assert x[i] == y[i]; }
          else if i == 10 { assert x[i] == y[i]; }
          else if i == 11 { assert x[i] == y[i]; }
          else if i == 12 { assert x[i] == y[i]; }
          else if i == 13 { assert x[i] == y[i]; }
          else if i == 14 { assert x[i] == y[i]; }
          else if i == 15 { assert x[i] == y[i]; }
          else if i == 16 { assert x[i] == y[i]; }
          else if i == 17 { assert x[i] == y[i]; }
          else if i == 18 { assert x[i] == y[i]; }
          else if i == 19 { assert x[i] == y[i]; }
          else if i == 20 { assert x[i] == y[i]; }
          else if i == 21 { assert x[i] == y[i]; }
          else if i == 22 { assert x[i] == y[i]; }
          else if i == 23 { assert x[i] == y[i]; }
          else if i == 24 { assert x[i] == y[i]; }
          else if i == 25 { assert x[i] == y[i]; }
          else if i == 26 { assert x[i] == y[i]; }
          else if i == 27 { assert x[i] == y[i]; }
          else if i == 28 { assert x[i] == y[i]; }
          else if i == 29 { assert x[i] == y[i]; }
          else if i == 30 { assert x[i] == y[i]; }
          else if i == 31 { assert x[i] == y[i]; }
        }
        seq_ext(x, y);
      }
      [
        a31, a30, a29, a28, a27, a26, a25, a24, a23, a22, a21, a20, a19, a18, a17, a16,
        a15, a14, a13, a12, a11, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, a0
      ];
    }
  }

  lemma mod_mod(x: int, a: int, b: int)
  requires x >= 0
  requires a > 0
  requires b > 0
  ensures (x % (a * b)) % b == x % b
  {
    assume false; // TODO
    var t := x % (a * b);
    var q := x / (a * b);
    assert x == q * (a * b) + t;

    var s := t % b;
    var r := t / b;
    assert t == r * b + s;

    calc {
      x % b;
      x - (x / b) * b;
      calc {
        x / b;
        calc {
          x;
          q * (a * b) + r * b + s;
          { assert q * (a * b) == (q * a) * b; }
          (q * a) * b + r * b + s;
          { assert (q * a + r) * b == (q * a) * b + r * b; }
          (q * a + r) * b + s;
        }
        ((q * a + r) * b + s) / b;
        (s + (q * a + r) * b) / b;
        (s + b * (q * a + r)) / b;
        {
          lemma_add_mul_div(s, q*a + r, b);
        }
        (q * a + r) + s / b;
      }
      x - ((q * a + r) + s / b) * b;
      x - ((q * a + r) * b + (s / b) * b);
      (q * (a * b) + r * b + s) - ((q * a + r) * b + (s / b) * b);
      {
        assert s > -(b as int);
        assert s < b;
        assert s / b == 0;
      }
      (q * (a * b) + r * b + s) - ((q * a + r) * b);
      s; 
    }
  }

  lemma div_mod(x: int, a: int, b: int)
  requires x >= 0
  requires a > 0
  requires b > 0
  ensures (x / b) % a == (x % (a * b)) / b
  {
    var q := x / b;
    var r := x % b;
    assert x == b*q + r;

    var t := q / a;
    var s := q % a;
    assert q == a*t + s;

    var u := x / (a * b);
    var p := x % (a * b);
    assert x == (a * b) * u + p;

    var v := p / b;
    var w := p % b;
    assert p == b * v + w;

    assert x
        == b*q + r
        == b*(a*t + s) + r;
    assert x
        == (a * b) * u + p
        == (a * b) * u + b * v + w;

    calc {
      0;
      x - x;
      (b*(a*t + s) + r) - ((a * b) * u + b * v + w);
      {
        lemma_div_denominator(x, b, a);
        assert u == t;
      }
      (b*(a*t + s) + r) - ((a * b) * t + b * v + w);
      b * (s - v) + (r - w);
    }

    assert b * (s - v) > -(b as int);
    assert b * (s - v) < b;
    bounded_mul_eq_0(s - v, b);

    assert s == v;
  }

  lemma lemma_bits_of_int_split(x: int, a: int, b: int)
  requires a >= 0
  requires b >= 0
  requires 0 <= x < power2(a + b)
  ensures bits_of_int(x, a + b)
      == bits_of_int(x % power2(a), a)
       + bits_of_int(x / power2(a), b)
  {
    if a == 0 {
      calc {
        bits_of_int(x, a + b);
        bits_of_int(x, b);
        {
          assert power2(0) == 1 by { reveal_power2(); }
          assert x / power2(a) == x;
        }
        bits_of_int(x / power2(a), b);
        [] + bits_of_int(x / power2(a), b);
        {
          calc {
            bits_of_int(x % power2(a), a);
            [];
          }
        }
        bits_of_int(x % power2(a), a) + bits_of_int(x / power2(a), b);
      }
    } else {
      assert x / power2(a) >= 0;
      calc {
        bits_of_int(x, a + b);
        [x % 2 == 1] + bits_of_int(x/2, a + b - 1);
        {
          assert x / 2 < power2(a - 1 + b) by { reveal_power2(); }
          lemma_bits_of_int_split(x/2, a - 1, b);
        }
        [x % 2 == 1] + (bits_of_int((x/2) % power2(a-1), a-1) + bits_of_int((x/2) / power2(a-1), b));
        {
          calc {
            bits_of_int((x/2) / power2(a-1), b);
            {
              calc {
                (x/2) / power2(a-1);
                { lemma_div_denominator(x, 2, power2(a-1)); }
                x / (2 * power2(a-1));
                {
                  assert power2(a) == 2 * power2(a-1) by { reveal_power2(); }
                }
                x / power2(a);
              }
            }
            bits_of_int(x / power2(a), b);
          }
        }
        [x % 2 == 1] + (bits_of_int((x/2) % power2(a-1), a-1) + bits_of_int(x / power2(a), b));
        ([x % 2 == 1] + bits_of_int((x/2) % power2(a-1), a-1)) + bits_of_int(x / power2(a), b);
        {
          calc {
            [x % 2 == 1] + bits_of_int((x/2) % power2(a-1), a-1);
            {
              calc {
                (x % power2(a)) % 2;
                {
                  assert power2(a) == power2(a-1) * 2 by { reveal_power2(); }
                }
                (x % (power2(a-1) * 2)) % 2;
                {
                  mod_mod(x, power2(a-1), 2);
                }
                x % 2;
              }
            }
            [(x % power2(a)) % 2 == 1] + bits_of_int((x/2) % power2(a-1), a-1);
            {
              calc {
                (x/2) % power2(a-1);
                {
                  div_mod(x, power2(a-1), 2);
                }
                (x % (power2(a-1) * 2)) / 2;
                {
                  assert (power2(a-1) * 2) == power2(a) by {reveal_power2();}
                }
                (x % power2(a)) / 2;
              }
            }
            [(x % power2(a)) % 2 == 1] + bits_of_int((x % power2(a)) / 2, a-1);
            bits_of_int(x % power2(a), a);
          }
        }
        bits_of_int(x % power2(a), a) + bits_of_int(x / power2(a), b);
      } 
    }
  }

  lemma lemma_bits_of_int_64_split(x: int)
  requires 0 <= x < 0x1_0000_0000_0000_0000
  ensures bits_of_int(x, 64)
      == bits_of_int(x % 0x1_0000_0000, 32)
       + bits_of_int(x / 0x1_0000_0000, 32)
  {
    lemma_2toX();
    lemma_bits_of_int_split(x, 32, 32);
  }
}
