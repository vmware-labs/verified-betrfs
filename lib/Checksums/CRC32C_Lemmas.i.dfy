// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

include "CRC32C.s.dfy"
include "../Lang/System/PackedInts.s.dfy"
include "CRC32C_PowDef.i.dfy"
include "F2_X_Lemmas.i.dfy"
include "BitLemmas.i.dfy"

module CRC32C_Lemmas {
  import opened Bits_s
  import opened F2_X_s
  import opened NativeTypes
  import opened NativePackedInts
  import opened CRC32_C`Internal
  import opened CRC32C_PowDef
  import opened F2_X_Lemmas
  import BitLemmas

  function {:opaque} advance(acc: Bits, data: Bits) : (acc': Bits)
  requires |acc| == 32
  ensures |acc'| == 32
  {
    reverse(mod_F2_X(
      xor(
        zeroes(32) + reverse(data),
        zeroes(|data|) + reverse(acc)
      ),
      poly()
    ))
  }

  lemma reverse_reverse(x: Bits)
  ensures reverse(reverse(x)) == x
  {
  }

  lemma reverse_xor(x: Bits, y: Bits)
  requires |x| == |y|
  ensures reverse(xor(x, y)) == xor(reverse(x), reverse(y))
  {
  }

  lemma mod_mul_distribute_4(x: Bits, a: Bits, b: Bits, c: Bits, d: Bits)
  requires |a| == |b| == |c| == |d|
  ensures mod_mul(x, xor(xor(xor(a,b),c),d))
      == xor(xor(xor(mod_mul(x,a), mod_mul(x,b)), mod_mul(x,c)), mod_mul(x,d))
  {
    calc {
      mod_mul(x, xor(xor(xor(a,b),c),d));
      {
        mod_mul_left_distributive(x, xor(xor(a,b),c), d);
      }
      xor(mod_mul(x, xor(xor(a,b),c)), mod_mul(x, d));
      {
        mod_mul_left_distributive(x, xor(a,b), c);
      }
      xor(xor(mod_mul(x, xor(a,b)), mod_mul(x, c)), mod_mul(x, d));
      {
        mod_mul_left_distributive(x, a, b);
      }
      xor(xor(xor(mod_mul(x, a), mod_mul(x, b)), mod_mul(x, c)), mod_mul(x, d));
    }
  }

  lemma xor_rearrange_5(a: Bits, b: Bits, c: Bits, d: Bits, e: Bits)
  requires |a| == |b| == |c| == |d| == |e|
  ensures xor(xor(xor(xor(a,b),c),d),e)
       == xor(xor(xor(xor(d,e),c),a),b)
  {
  }

  lemma simplify_inner_mod(a: Bits, b: Bits, c: Bits)
  requires |a| == |b| + 32
  requires |c| >= 32
  ensures mod_F2_X(xor(a, b + mod_F2_X(c, poly())), poly())
    == mod_F2_X(xor(a + zeroes(|b| + |c| - |a|), b + c), poly())
  {
    calc {
      mod_F2_X(xor(a, b + mod_F2_X(c, poly())), poly());
      {
        mod_ignores_trailing_zeroes(
            xor(a, b + mod_F2_X(c, poly())), |b|+|c|-|a|);
      }
      mod_F2_X(xor(a, b + mod_F2_X(c, poly())) + zeroes(|b| + |c| - |a|), poly());
      {
        assert xor(a, b + mod_F2_X(c, poly())) + zeroes(|b| + |c| - |a|)
            == xor(
              a + zeroes(|b| + |c| - |a|),
              b + mod_F2_X(c, poly()) + zeroes(|b| + |c| - |a|));
      }
      mod_F2_X(xor(
        a + zeroes(|b| + |c| - |a|),
        b + mod_F2_X(c, poly()) + zeroes(|b| + |c| - |a|)
      ), poly());
      {
        mod_xor(
          a + zeroes(|b| + |c| - |a|),
          b + mod_F2_X(c, poly()) + zeroes(|b| + |c| - |a|));
      }
      xor(
        mod_F2_X(a + zeroes(|b| + |c| - |a|), poly()),
        mod_F2_X(b + mod_F2_X(c, poly()) + zeroes(|b| + |c| - |a|), poly())
      );
      {
        mod_ignores_trailing_zeroes(b + mod_F2_X(c, poly()), |b| + |c| - |a|);
      }
      xor(
        mod_F2_X(a + zeroes(|b| + |c| - |a|), poly()),
        mod_F2_X(b + mod_F2_X(c, poly()), poly())
      );
      {
        mod_plus_mod(b, c);
      }
      xor(
        mod_F2_X(a + zeroes(|b| + |c| - |a|), poly()),
        mod_F2_X(b + c, poly())
      );
      {
        mod_xor(a + zeroes(|b| + |c| - |a|), b + c);
      }
      mod_F2_X(xor(a + zeroes(|b| + |c| - |a|), b + c), poly());
    }
  }

  lemma advance_assoc(acc: Bits, data1: Bits, data2: Bits)
  requires |acc| == 32
  ensures advance(advance(acc, data1), data2)
      == advance(acc, data1 + data2)
  {
    reveal_advance();
    calc {
      advance(advance(acc, data1), data2);
      reverse(mod_F2_X(
        xor(
          zeroes(32) + reverse(data2),
          zeroes(|data2|) + reverse(
            reverse(mod_F2_X(
              xor(
                zeroes(32) + reverse(data1),
                zeroes(|data1|) + reverse(acc)
              ),
              poly()
            ))
          )
        ),
        poly()
      ));

      {
        reverse_reverse(mod_F2_X( xor( zeroes(32) + reverse(data1), zeroes(|data1|) + reverse(acc)), poly()));
      }

      reverse(mod_F2_X(
        xor(
          zeroes(32) + reverse(data2),
          zeroes(|data2|) + 
            mod_F2_X(
              xor(
                zeroes(32) + reverse(data1),
                zeroes(|data1|) + reverse(acc)
              ),
              poly()
            )
        ),
        poly()
      ));

      {
        simplify_inner_mod(zeroes(32) + reverse(data2), 
            zeroes(|data2|), xor(
                zeroes(32) + reverse(data1),
                zeroes(|data1|) + reverse(acc)
              ));
      }

      reverse(mod_F2_X(
        xor(
          zeroes(32) + reverse(data2) + zeroes(|data1|),
          zeroes(|data2|) + xor(
                zeroes(32) + reverse(data1),
                zeroes(|data1|) + reverse(acc)
              )
        ),
        poly()
      ));

      {
        var a := xor(
            zeroes(32) + reverse(data2) + zeroes(|data1|),
            zeroes(|data2|) + xor(
                  zeroes(32) + reverse(data1),
                  zeroes(|data1|) + reverse(acc)
                )
          );
        var b := xor(
            zeroes(32) + reverse(data1 + data2),
            zeroes(|data1 + data2|) + reverse(acc)
          );
        forall i | 0 <= i < |a| ensures a[i] == b[i]
        {
        }
        assert a == b;
      }

      reverse(mod_F2_X(
        xor(
          zeroes(32) + reverse(data1 + data2),
          zeroes(|data1 + data2|) + reverse(acc)
        ),
        poly()
      ));

      advance(acc, data1 + data2);
    }
  }

  predicate {:opaque} advances_bytes(s: seq<byte>, i1: int, acc1: uint32, i2: int, acc2: uint32)
  requires 0 <= i1 <= i2 <= |s|
  {
    advance(bits_of_int(acc1 as int, 32), bits_of_bytes(s[i1..i2]))
        == bits_of_int(acc2 as int, 32)
  }

  lemma advances_bytes_refl(s: seq<byte>, i: int, acc: uint32)
  requires 0 <= i <= |s|
  ensures advances_bytes(s, i, acc, i, acc)
  {
    var b := bits_of_int(acc as int, 32);
    calc {
      advance(b, bits_of_bytes(s[i..i]));
      advance(b, []);
      {
        reveal_advance();
      }
      reverse(mod_F2_X(xor(zeroes(32), reverse(b)), poly()));
      reverse(mod_F2_X(reverse(b), poly()));
      reverse(reverse(b));
      b;
    }
    reveal_advances_bytes();
  }

  lemma bits_of_bytes_additive(s: seq<byte>, t: seq<byte>)
  ensures bits_of_bytes(s + t) == bits_of_bytes(s) + bits_of_bytes(t)
  {
    if |t| == 0 {
      calc {
        bits_of_bytes(s + t);
          { assert s + t == s; }
        bits_of_bytes(s);
        bits_of_bytes(s) + bits_of_bytes(t);
      }
    } else {
      calc {
        bits_of_bytes(s + t);
        bits_of_bytes((s+t)[0..|s+t|-1]) + bits_of_int((s+t)[|s+t|-1] as int, 8);
        {
          assert (s+t)[0..|s+t|-1] == s + t[0..|t|-1];
          assert (s+t)[|s+t|-1] == t[|t|-1];
        }
        bits_of_bytes(s + t[0..|t|-1]) + bits_of_int(t[|t|-1] as int, 8);
        { bits_of_bytes_additive(s, t[0..|t|-1]); }
        bits_of_bytes(s) + bits_of_bytes(t[0..|t|-1]) + bits_of_int(t[|t|-1] as int, 8);
        bits_of_bytes(s) + bits_of_bytes(t);
      }
    }
  }

  lemma bits_of_bytes_additive4(r: seq<byte>, s: seq<byte>, t: seq<byte>, u: seq<byte>)
  ensures bits_of_bytes(r + s + t + u)
      == bits_of_bytes(r) + bits_of_bytes(s) + bits_of_bytes(t) + bits_of_bytes(u)
  {
    calc {
      bits_of_bytes(r + s + t + u);
      { assert r + s + t + u == (r + s) + (t + u); }
      bits_of_bytes((r + s) + (t + u));
      { bits_of_bytes_additive(r + s, t + u); }
      bits_of_bytes(r + s) + bits_of_bytes(t + u);
      {
        bits_of_bytes_additive(r, s);
        bits_of_bytes_additive(t, u);
      }
      bits_of_bytes(r) + bits_of_bytes(s) + bits_of_bytes(t) + bits_of_bytes(u);
    }
  }

  lemma bits_of_bytes_additive4_slice(r: seq<byte>, a: int, b: int, c: int, d: int, e: int)
  requires 0 <= a <= b <= c <= d <= e <= |r|
  ensures bits_of_bytes(r[a..e])
      == bits_of_bytes(r[a..b]) + bits_of_bytes(r[b..c]) + bits_of_bytes(r[c..d]) + bits_of_bytes(r[d..e])
  {
    assert r[a..b] + r[b..c] + r[c..d] + r[d..e] == r[a..e];
    bits_of_bytes_additive4(r[a..b], r[b..c], r[c..d], r[d..e]);
  }


  lemma advances_bytes_transitive(s: seq<byte>,
      i1: int, acc1: uint32,
      i2: int, acc2: uint32,
      i3: int, acc3: uint32)
  requires 0 <= i1 <= i2 <= i3 <= |s|
  requires advances_bytes(s, i1, acc1, i2, acc2)
  requires advances_bytes(s, i2, acc2, i3, acc3)
  ensures advances_bytes(s, i1, acc1, i3, acc3)
  {
    var b1 := bits_of_int(acc1 as int, 32);
    //var b2 := bits_of_int(acc2 as int, 32);
    //var b3 := bits_of_int(acc3 as int, 32);
    reveal_advances_bytes();
    advance_assoc(b1, bits_of_bytes(s[i1..i2]), bits_of_bytes(s[i2..i3]));

    assert bits_of_bytes(s[i1..i2]) + bits_of_bytes(s[i2..i3])
        == bits_of_bytes(s[i1..i3]) by {
      bits_of_bytes_additive(s[i1..i2], s[i2..i3]);
      assert s[i1..i2] + s[i2..i3] == s[i1..i3];
    }
  }

  lemma advances_bytes_u8(s: seq<byte>, i: int, acc: uint32, acc': uint32)
  requires 0 <= i < |s|
  requires bits_of_int(acc' as int, 32) ==
      mm_crc32_u8(bits_of_int(acc as int, 32), bits_of_int(s[i] as int, 8))
  ensures advances_bytes(s,
    i, acc,
    i+1, acc')
  {
    assert bits_of_int(s[i] as int, 8)
        == bits_of_bytes(s[i..i+1]);

    calc {
      advance(bits_of_int(acc as int, 32), bits_of_bytes(s[i..i+1]));
      {
        reveal_advance();
      }
      bits_of_int(acc' as int, 32);
    }

    reveal_advances_bytes();
  }

  lemma advances_bytes_u64(s: seq<byte>, i: int, acc: uint32, acc': uint32)
  requires 0 <= i
  requires i+8 <= |s|
  requires bits_of_int(acc' as int, 32) ==
      mm_crc32_u64(
        bits_of_int(acc as int, 32),
        bits_of_int(unpack_LittleEndian_Uint64(s[i..i+8]) as int, 64)
      )
  ensures advances_bytes(s,
    i, acc,
    i+8, acc')
  {
    BitLemmas.bits_of_int_unpack64(s[i..i+8]);

    calc {
      advance(bits_of_int(acc as int, 32), bits_of_bytes(s[i..i+8]));
      {
        reveal_advance();
      }
      bits_of_int(acc' as int, 32);
    }

    reveal_advances_bytes();
  }

  /*lemma combine3(n: int, prev: Bits, r: Bits, s: Bits, t: Bits, u: Bits)
  requires 1 <= n <= 256
  requires |u| == 64
  requires |t| == 64*n - 64
  requires |s| == 64*n
  requires |prev| == 32
  ensures
    reverse(mod_F2_X(
      xor(
        zeroes(64) + reverse(reverse(mod_F2_X(zeroes(32) + reverse(t)))),
        zeroes(32) + reverse(
          xor(
            xor(
                mul_F2_X(
                  xor(
                  pow_mod_crc(2 * 64 * n as int)),
                mul_F2_X(
                  xor(zeroes(32) + reverse(s), zeroes(|s|) + zeroes(32)),
                  pow_mod_crc(64 * n as int))
                )
            ),
            bits_of_int(unpack_LittleEndian_Uint64(s[i-8 .. i]) as int, 64)
          )
        )
      )
    ))
    == reverse(mod_F2_X(
        xor(
          zeroes(|u| + |t| + |s| + |r|) + prev,
          zeroes(32) + reverse(r + s + t + u)
        )
      )*/

  lemma combine3_lemma(n: int, r: Bits, s: Bits, t: Bits, u: Bits, prev: Bits)
  requires 1 <= n <= 256
  requires |s| == 64 * n
  requires |t| == 64 * n - 64
  requires |u| == 64
  requires |prev| == 32
  ensures
      mod(
        xor(
          zeroes(32) + reverse(
            xor(
              xor(
                mul_F2_X(
                  reverse(mod(
                    xor(
                      zeroes(32) + reverse(r),
                      zeroes(|r|) + reverse(prev)
                    )
                  )),
                  pow_mod_crc(2 * 64 * n as int)
                ),
                mul_F2_X(
                  reverse(mod(
                    xor(
                      zeroes(32) + reverse(s),
                      zeroes(|s|) + reverse(zeroes(32))
                    )
                  )),
                  pow_mod_crc(    64 * n as int)
                )
              ),
              u
            )
          ),
          zeroes(64) + reverse(
            reverse(mod(
              xor(
                zeroes(32) + reverse(t),
                zeroes(|t|) + reverse(zeroes(32))
              )
            ))
          )
        )
      )
      == mod(
        xor(
          zeroes(32) + reverse(r+s+t+u),
          zeroes(|r|+|s|+|t|+|u|) + reverse(prev)
        )
      )
  {
    calc {
      mod(
        xor(
          zeroes(32) + reverse(
            xor(
              xor(
                mul_F2_X(
                  reverse(mod(
                    xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev))
                  )),
                  pow_mod_crc(2 * 64 * n as int)
                ),
                mul_F2_X(
                  reverse(mod(
                    xor(zeroes(32) + reverse(s), zeroes(|s|) + reverse(zeroes(32)))
                  )),
                  pow_mod_crc(    64 * n as int)
                )
              ),
              u
            )
          ),
          zeroes(64) + reverse(
            reverse(mod(
              xor(zeroes(32) + reverse(t), zeroes(|t|) + reverse(zeroes(32)))
            ))
          )
        )
      );
      {
        mod_xor(zeroes(32) + reverse( xor( xor( mul_F2_X( reverse(mod( xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev)))), pow_mod_crc(2 * 64 * n as int)), mul_F2_X( reverse(mod( xor(zeroes(32) + reverse(s), zeroes(|s|) + reverse(zeroes(32))))), pow_mod_crc(    64 * n as int))), u)), zeroes(64) + reverse( reverse(mod( xor(zeroes(32) + reverse(t), zeroes(|t|) + reverse(zeroes(32)))))));
      }
      xor(
        mod(
          zeroes(32) + reverse(
            xor(
              xor(
                mul_F2_X(
                  reverse(mod(
                    xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev))
                  )),
                  pow_mod_crc(2 * 64 * n as int)
                ),
                mul_F2_X(
                  reverse(mod(
                    xor(zeroes(32) + reverse(s), zeroes(|s|) + reverse(zeroes(32)))
                  )),
                  pow_mod_crc(    64 * n as int)
                )
              ),
              u
            )
          )
        ),
        mod(
          zeroes(64) + reverse(
            reverse(mod(
              xor(zeroes(32) + reverse(t), zeroes(|t|) + reverse(zeroes(32)))
            ))
          )
        )
      );
      {
        calc {
          mod(
            zeroes(64) + reverse(
              reverse(mod(xor(zeroes(32) + reverse(t), zeroes(|t|) + reverse(zeroes(32)))))
            )
          );
          { reverse_reverse(mod(xor(zeroes(32) + reverse(t), zeroes(|t|) + reverse(zeroes(32))))); }
          mod(
            zeroes(64) +
            mod(xor(zeroes(32) + reverse(t), zeroes(|t|) + reverse(zeroes(32))))
          );
          {
            assert xor(zeroes(32) + reverse(t), zeroes(|t|) + reverse(zeroes(32)))
                == zeroes(32) + reverse(t);
          }
          mod(zeroes(64) + mod(zeroes(32) + reverse(t)));
          { mod_shift(mod(zeroes(32) + reverse(t)), 64); }
          mod_mul(exp(64), mod(zeroes(32) + reverse(t)));
          { mod_shift(reverse(t), 32); }
          mod_mul(exp(64), mod_mul(exp(32), reverse(t)));
          { mod_mul_assoc(exp(64), exp(32), reverse(t)); }
          mod_mul(mod_mul(exp(64), exp(32)), reverse(t));
          { mod_mul_comm(exp(64), exp(32)); }
          mod_mul(mod_mul(exp(32), exp(64)), reverse(t));
          { mod_mul_assoc(exp(32), exp(64), reverse(t)); }
          mod_mul(exp(32), mod_mul(exp(64), reverse(t)));
        }
      }
      xor(
        mod(
          zeroes(32) + reverse(
            xor(
              xor(
                mul_F2_X(
                  reverse(mod(
                    xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev))
                  )),
                  pow_mod_crc(2 * 64 * n as int)
                ),
                mul_F2_X(
                  reverse(mod(
                    xor(zeroes(32) + reverse(s), zeroes(|s|) + reverse(zeroes(32)))
                  )),
                  pow_mod_crc(    64 * n as int)
                )
              ),
              u
            )
          )
        ),
        mod_mul(exp(32), mod_mul(exp(64), reverse(t)))
      );
      {
        var a := mul_F2_X(
                    reverse(mod(
                      xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev))
                    )),
                    pow_mod_crc(2 * 64 * n as int)
                  );
        var b := mul_F2_X(
                    reverse(mod(
                      xor(zeroes(32) + reverse(s), zeroes(|s|) + reverse(zeroes(32)))
                    )),
                    pow_mod_crc(    64 * n as int)
                  );
        calc {
          mod(zeroes(32) + reverse(xor(xor(a, b), u)));
          { mod_shift(reverse(xor(xor(a, b), u)), 32); }
          mod_mul(exp(32), reverse(xor(xor(a, b), u)));
          {
            reverse_xor(xor(a, b), u);
            reverse_xor(a, b);
          }
          mod_mul(exp(32), xor(xor(reverse(a), reverse(b)), reverse(u)));
          {
            mod_mul_mod_right(exp(32), xor(xor(reverse(a), reverse(b)), reverse(u)));
          }
          mod_mul(exp(32), mod(xor(xor(reverse(a), reverse(b)), reverse(u))));
          {
            mod_xor(xor(reverse(a), reverse(b)), reverse(u));
          }
          mod_mul(exp(32), xor(mod(xor(reverse(a), reverse(b))), mod(reverse(u))));
          {
            mod_xor(reverse(a), reverse(b));
          }
          mod_mul(exp(32), xor(xor(mod(reverse(a)), mod(reverse(b))), mod(reverse(u))));
        }

        calc {
          mod(reverse(a));
          {
            mod_reverse_mul_reverse(
              mod(xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev))),
              mod(exp(2 * 64 * n - 33)));
          }
          mod_mul(exp(1), mod_mul(
            mod(xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev))),
            mod(exp(2 * 64 * n - 33))
          ));
          {
            mod_mul_comm(mod(exp(2 * 64 * n - 33)),
              mod(xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev))));
          }
          mod_mul(exp(1), mod_mul(
            mod(exp(2 * 64 * n - 33)),
            mod(xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev)))
          ));
          {
            mod_mul_assoc(exp(1), mod(exp(2 * 64 * n - 33)),
              mod(xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev))));
          }
          mod_mul(
            mod_mul(exp(1), mod(exp(2 * 64 * n - 33))),
            mod(xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev)))
          );
          {
            mod_mul_mod_right(exp(1), exp(2 * 64 * n - 33));
          }
          mod_mul(
            mod_mul(exp(1), exp(2 * 64 * n - 33)),
            mod(xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev)))
          );
          {
            mod_mul_exp_add(1, 2 * 64 * n - 33);
          }
          mod_mul(
            mod(exp(2 * 64 * n - 32)),
            mod(xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev)))
          );
          {
            mod_mul_mod_left(exp(2 * 64 * n - 32),
                mod(xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev))));
          }
          mod_mul(
            exp(2 * 64 * n - 32),
            mod(xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev)))
          );
          {
            mod_xor(zeroes(32) + reverse(r), zeroes(|r|) + reverse(prev));
          }
          mod_mul(
            exp(2 * 64 * n - 32),
            xor(mod(zeroes(32) + reverse(r)), mod(zeroes(|r|) + reverse(prev)))
          );
          {
            mod_shift(reverse(r), 32);
            mod_shift(reverse(prev), |r|);
          }
          mod_mul(
            exp(2 * 64 * n - 32),
            xor(
              mod_mul(exp(32), reverse(r)),
              mod_mul(exp(|r|), reverse(prev))
            )
          );
          {
            mod_mul_left_distributive(
              exp(2 * 64 * n - 32),
              mod_mul(exp(32), reverse(r)),
              mod_mul(exp(|r|), reverse(prev)));
          }
          xor(
            mod_mul(exp(2 * 64 * n - 32), mod_mul(exp(32), reverse(r))),
            mod_mul(exp(2 * 64 * n - 32), mod_mul(exp(|r|), reverse(prev)))
          );
          {
            mod_mul_assoc(exp(2 * 64 * n - 32), exp(32), reverse(r));
            mod_mul_assoc(exp(2 * 64 * n - 32), exp(|r|), reverse(prev));
          }
          xor(
            mod_mul(mod_mul(exp(2 * 64 * n - 32), exp(32)), reverse(r)),
            mod_mul(mod_mul(exp(2 * 64 * n - 32), exp(|r|)), reverse(prev))
          );
          {
            mod_mul_exp_add(2 * 64 * n - 32, 32);
            mod_mul_exp_add(2 * 64 * n - 32, |r|);
          }
          xor(
            mod_mul(mod(exp(2 * 64 * n)), reverse(r)),
            mod_mul(mod(exp(2 * 64 * n - 32 + |r|)), reverse(prev))
          );
          {
            mod_mul_mod_left(exp(2 * 64 * n), reverse(r));
            mod_mul_mod_left(exp(2 * 64 * n - 32 + |r|), reverse(prev));
          }
          xor(
            mod_mul(exp(2 * 64 * n), reverse(r)),
            mod_mul(exp(2 * 64 * n - 32 + |r|), reverse(prev))
          );
        }

        calc {
          mod(reverse(b));
          {
            mod_reverse_mul_reverse(
              mod(xor(zeroes(32) + reverse(s), zeroes(|s|) + reverse(zeroes(32)))),
              mod(exp(64 * n - 33)));
          }
          mod_mul(exp(1), mod_mul(
            mod(xor(zeroes(32) + reverse(s), zeroes(|s|) + reverse(zeroes(32)))),
            mod(exp(64 * n - 33))
          ));
          {
            assert xor(zeroes(32) + reverse(s), zeroes(|s|) + reverse(zeroes(32)))
              == zeroes(32) + reverse(s);
          }
          mod_mul(exp(1), mod_mul(
            mod(zeroes(32) + reverse(s)),
            mod(exp(64 * n - 33))
          ));
          {
            mod_shift(reverse(s), 32);
          }
          mod_mul(exp(1), mod_mul(
            mod_mul(exp(32), reverse(s)),
            mod(exp(64 * n - 33))
          ));
          {
            mod_mul_comm(mod_mul(exp(32), reverse(s)), mod(exp(64 * n - 33)));
          }
          mod_mul(exp(1), mod_mul(
            mod(exp(64 * n - 33)),
            mod_mul(exp(32), reverse(s))
          ));
          {
            mod_mul_mod_left(exp(64 * n - 33), mod_mul(exp(32), reverse(s)));
          }
          mod_mul(exp(1), mod_mul(
            exp(64 * n - 33),
            mod_mul(exp(32), reverse(s))
          ));
          {
            mod_mul_assoc(exp(64 * n - 33), exp(32), reverse(s));
          }
          mod_mul(exp(1), mod_mul(
            mod_mul(exp(64 * n - 33), exp(32)),
            reverse(s)
          ));
          {
            mod_mul_exp_add(64 * n - 33, 32);
          }
          mod_mul(exp(1), mod_mul(
            mod(exp(64 * n - 1)),
            reverse(s)
          ));
          {
            mod_mul_mod_left(exp(64 * n - 1), reverse(s));
          }
          mod_mul(exp(1), mod_mul(exp(64 * n - 1), reverse(s)));
          {
            mod_mul_assoc(exp(1), exp(64 * n - 1), reverse(s));
          }
          mod_mul(mod_mul(exp(1), exp(64 * n - 1)), reverse(s));
          {
            mod_mul_exp_add(1, 64 * n - 1);
          }
          mod_mul(mod(exp(64 * n)), reverse(s));
          {
            mod_mul_mod_left(exp(64 * n), reverse(s));
          }
          mod_mul(exp(64 * n), reverse(s));
        }
      }
      xor(
        mod_mul(
          exp(32),
          xor(
            xor(
              xor(
                mod_mul(exp(2 * 64 * n), reverse(r)),
                mod_mul(exp(2 * 64 * n - 32 + |r|), reverse(prev))
              ),
              mod_mul(exp(64 * n), reverse(s))
            ),
            mod(reverse(u))
          )
        ),
        mod_mul(exp(32), mod_mul(exp(64), reverse(t)))
      );
      {
        calc {
          mod_mul(
            exp(32),
            xor(
              xor(
                xor(
                  mod_mul(exp(2 * 64 * n), reverse(r)),
                  mod_mul(exp(2 * 64 * n - 32 + |r|), reverse(prev))
                ),
                mod_mul(exp(64 * n), reverse(s))
              ),
              mod(reverse(u))
            )
          );
          {
            mod_mul_distribute_4(exp(32),
                  mod_mul(exp(2 * 64 * n), reverse(r)),
                  mod_mul(exp(2 * 64 * n - 32 + |r|), reverse(prev)),
                  mod_mul(exp(64 * n), reverse(s)),
                  mod(reverse(u)));
          }
          xor(
            xor(
              xor(
                mod_mul(exp(32), mod_mul(exp(2 * 64 * n), reverse(r))),
                mod_mul(exp(32), mod_mul(exp(2 * 64 * n - 32 + |r|), reverse(prev)))
              ),
              mod_mul(exp(32), mod_mul(exp(64 * n), reverse(s)))
            ),
            mod_mul(exp(32), mod(reverse(u)))
          );
          {
            mod_mul_assoc(exp(32), exp(2 * 64 * n), reverse(r));
            mod_mul_assoc(exp(32), exp(2 * 64 * n - 32 + |r|), reverse(prev));
            mod_mul_assoc(exp(32), exp(64 * n), reverse(s));
          }
          xor(
            xor(
              xor(
                mod_mul(mod_mul(exp(32), exp(2 * 64 * n)), reverse(r)),
                mod_mul(mod_mul(exp(32), exp(2 * 64 * n - 32 + |r|)), reverse(prev))
              ),
              mod_mul(mod_mul(exp(32), exp(64 * n)), reverse(s))
            ),
            mod_mul(exp(32), mod(reverse(u)))
          );
          {
            mod_mul_exp_add(32, 2 * 64 * n);
            mod_mul_exp_add(32, 2 * 64 * n - 32 + |r|);
            mod_mul_exp_add(32, 64 * n);
          }
          xor(
            xor(
              xor(
                mod_mul(mod(exp(2 * 64 * n + 32)), reverse(r)),
                mod_mul(mod(exp(2 * 64 * n + |r|)), reverse(prev))
              ),
              mod_mul(mod(exp(64 * n + 32)), reverse(s))
            ),
            mod_mul(exp(32), mod(reverse(u)))
          );
        }
      }
      xor( xor( xor( xor(
        mod_mul(mod(exp(2 * 64 * n + 32)), reverse(r)),
        mod_mul(mod(exp(2 * 64 * n + |r|)), reverse(prev))),
        mod_mul(mod(exp(64 * n + 32)), reverse(s))),
        mod_mul(exp(32), mod(reverse(u)))),
        mod_mul(exp(32), mod_mul(exp(64), reverse(t)))
      );
      {
        calc {
          mod_mul(exp(32), mod_mul(exp(64), reverse(t)));
          {
            mod_mul_assoc(exp(32), exp(64), reverse(t));
          }
          mod_mul(mod_mul(exp(32), exp(64)), reverse(t));
          {
            mod_mul_exp_add(32, 64);
          }
          mod_mul(mod(exp(96)), reverse(t));
          {
            mod_mul_mod_left(exp(96), reverse(t));
          }
          mod_mul(exp(96), reverse(t));
        }
      }
      xor( xor( xor( xor(
        mod_mul(mod(exp(2 * 64 * n + 32)), reverse(r)),
        mod_mul(mod(exp(2 * 64 * n + |r|)), reverse(prev))),
        mod_mul(mod(exp(64 * n + 32)), reverse(s))),
        mod_mul(exp(32), mod(reverse(u)))),
        mod_mul(exp(96), reverse(t))
      );
      {
        mod_mul_mod_left(exp(2 * 64 * n + 32), reverse(r));
        mod_mul_mod_left(exp(2 * 64 * n + |r|), reverse(prev));
        mod_mul_mod_left(exp(64 * n + 32), reverse(s));
        mod_mul_mod_right(exp(32), reverse(u));
      }
      xor( xor( xor( xor(
        mod_mul(exp(2 * 64 * n + 32), reverse(r)),
        mod_mul(exp(2 * 64 * n + |r|), reverse(prev))),
        mod_mul(exp(64 * n + 32), reverse(s))),
        mod_mul(exp(32), reverse(u))),
        mod_mul(exp(96), reverse(t))
      );
      xor( xor( xor( xor(
        mod_mul(exp(32+|u|+|t|+|s|), reverse(r)),
        mod_mul(exp(|r|+|s|+|t|+|u|), reverse(prev))),
        mod_mul(exp(32+|u|+|t|), reverse(s))),
        mod_mul(exp(32), reverse(u))),
        mod_mul(exp(32+|u|), reverse(t))
      );
      {
        var a := mod_mul(exp(32+|u|+|t|+|s|), reverse(r));
        var b := mod_mul(exp(|r|+|s|+|t|+|u|), reverse(prev));
        var c := mod_mul(exp(32+|u|+|t|), reverse(s));
        var d := mod_mul(exp(32), reverse(u));
        var e := mod_mul(exp(32+|u|), reverse(t));
        xor_rearrange_5(a, b, c, d, e);
        calc {
          xor( xor( xor( xor(
            mod_mul(exp(32+|u|+|t|+|s|), reverse(r)),
            mod_mul(exp(|r|+|s|+|t|+|u|), reverse(prev))),
            mod_mul(exp(32+|u|+|t|), reverse(s))),
            mod_mul(exp(32), reverse(u))),
            mod_mul(exp(32+|u|), reverse(t))
          );
          xor(xor(xor(xor(a,b),c),d),e);
          xor(xor(xor(xor(d,e),c),a),b);
          xor(xor(xor(xor(
            mod_mul(exp(32), reverse(u)),
            mod_mul(exp(32+|u|), reverse(t))),
            mod_mul(exp(32+|u|+|t|), reverse(s))),
            mod_mul(exp(32+|u|+|t|+|s|), reverse(r))),
            mod_mul(exp(|r|+|s|+|t|+|u|), reverse(prev))
          );
        }
      }
      xor(xor(xor(xor(
        mod_mul(exp(32), reverse(u)),
        mod_mul(exp(32+|u|), reverse(t))),
        mod_mul(exp(32+|u|+|t|), reverse(s))),
        mod_mul(exp(32+|u|+|t|+|s|), reverse(r))),
        mod_mul(exp(|r|+|s|+|t|+|u|), reverse(prev))
      );
      {
        calc {
          mod(zeroes(32) + reverse(r+s+t+u));
          {
            assert reverse(r+s+t+u)
                == reverse(u) + reverse(t) + reverse(s) + reverse(r);
          }
          mod(zeroes(32) + (reverse(u) + reverse(t) + reverse(s) + reverse(r)));
          {
            assert zeroes(32) + (reverse(u) + reverse(t) + reverse(s) + reverse(r))
                == zeroes(32) + reverse(u) + reverse(t) + reverse(s) + reverse(r);
          }
          mod(zeroes(32) + reverse(u) + reverse(t) + reverse(s) + reverse(r));
          {
            var a := zeroes(32) + reverse(u) + reverse(t) + reverse(s) + reverse(r);
            var b := xor(xor(xor(
              zeroes(32) + reverse(u) + zeroes(|t|+|s|+|r|),
              zeroes(32+|u|) + reverse(t) + zeroes(|s|+|r|)),
              zeroes(32+|u|+|t|) + reverse(s) + zeroes(|r|)),
              zeroes(32+|u|+|t|+|s|) + reverse(r));
            forall i | 0 <= i < |a| ensures a[i] == b[i]
            {
              assert a[i] == b[i];
            }
            assert a == b;
          }
          mod(xor(xor(xor(
            zeroes(32) + reverse(u) + zeroes(|t|+|s|+|r|),
            zeroes(32+|u|) + reverse(t) + zeroes(|s|+|r|)),
            zeroes(32+|u|+|t|) + reverse(s) + zeroes(|r|)),
            zeroes(32+|u|+|t|+|s|) + reverse(r))
          );
          {
            mod_xor(xor(xor(
              zeroes(32) + reverse(u) + zeroes(|t|+|s|+|r|),
              zeroes(32+|u|) + reverse(t) + zeroes(|s|+|r|)),
              zeroes(32+|u|+|t|) + reverse(s) + zeroes(|r|)),
              zeroes(32+|u|+|t|+|s|) + reverse(r));
          }
          xor(mod(xor(xor(
            zeroes(32) + reverse(u) + zeroes(|t|+|s|+|r|),
            zeroes(32+|u|) + reverse(t) + zeroes(|s|+|r|)),
            zeroes(32+|u|+|t|) + reverse(s) + zeroes(|r|))),
            mod(zeroes(32+|u|+|t|+|s|) + reverse(r))
          );
          {
            mod_xor(xor(
              zeroes(32) + reverse(u) + zeroes(|t|+|s|+|r|),
              zeroes(32+|u|) + reverse(t) + zeroes(|s|+|r|)),
              zeroes(32+|u|+|t|) + reverse(s) + zeroes(|r|));
          }
          xor(xor(mod(xor(
            zeroes(32) + reverse(u) + zeroes(|t|+|s|+|r|),
            zeroes(32+|u|) + reverse(t) + zeroes(|s|+|r|))),
            mod(zeroes(32+|u|+|t|) + reverse(s) + zeroes(|r|))),
            mod(zeroes(32+|u|+|t|+|s|) + reverse(r))
          );
          {
            mod_xor(
              zeroes(32) + reverse(u) + zeroes(|t|+|s|+|r|),
              zeroes(32+|u|) + reverse(t) + zeroes(|s|+|r|));
          }
          xor(xor(xor(
            mod(zeroes(32) + reverse(u) + zeroes(|t|+|s|+|r|)),
            mod(zeroes(32+|u|) + reverse(t) + zeroes(|s|+|r|))),
            mod(zeroes(32+|u|+|t|) + reverse(s) + zeroes(|r|))),
            mod(zeroes(32+|u|+|t|+|s|) + reverse(r)));
          {
            mod_ignores_trailing_zeroes(zeroes(32) + reverse(u), |t|+|s|+|r|);
            mod_ignores_trailing_zeroes(zeroes(32+|u|) + reverse(t), |s|+|r|);
            mod_ignores_trailing_zeroes(zeroes(32+|u|+|t|) + reverse(s), |r|);
          }
          xor(xor(xor(
            mod(zeroes(32) + reverse(u)),
            mod(zeroes(32+|u|) + reverse(t))),
            mod(zeroes(32+|u|+|t|) + reverse(s))),
            mod(zeroes(32+|u|+|t|+|s|) + reverse(r)));
          {
            mod_shift(reverse(u), 32);
            mod_shift(reverse(t), 32+|u|);
            mod_shift(reverse(s), 32+|u|+|t|);
            mod_shift(reverse(r), 32+|u|+|t|+|s|);
          }
          xor(xor(xor(
            mod_mul(exp(32), reverse(u)),
            mod_mul(exp(32+|u|), reverse(t))),
            mod_mul(exp(32+|u|+|t|), reverse(s))),
            mod_mul(exp(32+|u|+|t|+|s|), reverse(r)));
        }
      }
      xor(
        mod(zeroes(32) + reverse(r+s+t+u)),
        mod_mul(exp(|r|+|s|+|t|+|u|), reverse(prev))
      );
      {
        mod_shift(reverse(prev), |r|+|s|+|t|+|u|);
      }
      xor(
        mod(zeroes(32) + reverse(r+s+t+u)),
        mod(zeroes(|r|+|s|+|t|+|u|) + reverse(prev))
      );
      {
        mod_xor(zeroes(32) + reverse(r+s+t+u), zeroes(|r|+|s|+|t|+|u|) + reverse(prev));
      }
      mod(
        xor(
          zeroes(32) + reverse(r+s+t+u),
          zeroes(|r|+|s|+|t|+|u|) + reverse(prev)
        )
      );
    }
  }

  lemma advances_bytes_combine3(data: seq<byte>, start: int, i: int, n: int,
      p: uint32, a: uint32, b: uint32, c: uint32, q: uint32)
  requires 1 <= n <= 256
  requires 0 <= i - 24*n
  requires i <= |data|
  requires bits_of_int(q as int, 32) ==
      mm_crc32_u64(
        bits_of_int(c as int, 32),
        xor(
          xor(
              mul_F2_X(bits_of_int(a as int, 32), pow_mod_crc(2 * 64 * n as int)),
              mul_F2_X(bits_of_int(b as int, 32), pow_mod_crc(    64 * n as int))
          ),
          bits_of_int(unpack_LittleEndian_Uint64(data[i-8 .. i]) as int, 64)
        )
      )
  requires 0 <= start <= i - 16 * n
  requires advances_bytes(data, start, p, i-16*n, a)
  requires advances_bytes(data, i-16*n, 0, i-8*n, b)
  requires advances_bytes(data, i-8*n, 0, i-8, c)
  ensures advances_bytes(data, start, p, i, q)
  {
    reveal_advances_bytes();

    var r := bits_of_bytes(data[start .. i - 16 * n]);
    var s := bits_of_bytes(data[i - 16 * n .. i - 8 * n]);
    var t := bits_of_bytes(data[i - 8 * n .. i - 8]);
    var u := bits_of_bytes(data[i - 8 .. i]);

    var prev := bits_of_int(p as int, 32);

    calc {
      bits_of_int(q as int, 32);
      mm_crc32_u64(
        bits_of_int(c as int, 32),
        xor(
          xor(
              mul_F2_X(bits_of_int(a as int, 32), pow_mod_crc(2 * 64 * n as int)),
              mul_F2_X(bits_of_int(b as int, 32), pow_mod_crc(    64 * n as int))
          ),
          bits_of_int(unpack_LittleEndian_Uint64(data[i-8 .. i]) as int, 64)
        )
      );
      {
        BitLemmas.bits_of_int_unpack64(data[i-8 .. i]);
      }
      mm_crc32_u64(
        bits_of_int(c as int, 32),
        xor(
          xor(
              mul_F2_X(bits_of_int(a as int, 32), pow_mod_crc(2 * 64 * n as int)),
              mul_F2_X(bits_of_int(b as int, 32), pow_mod_crc(    64 * n as int))
          ),
          u
        )
      );
      {
        reveal_advance();
        BitLemmas.bits_of_int_0(32);
        assert bits_of_int(c as int, 32)
         == reverse(mod(
              xor(
                zeroes(32) + reverse(t),
                zeroes(|t|) + reverse(zeroes(32))
              )
            ));
        assert bits_of_int(a as int, 32)
          == reverse(mod(
                xor(
                  zeroes(32) + reverse(r),
                  zeroes(|r|) + reverse(prev)
                )
              ));
        assert bits_of_int(b as int, 32)
          == reverse(mod(
                xor(
                  zeroes(32) + reverse(s),
                  zeroes(|s|) + reverse(zeroes(32))
                )
              ));
      }
      mm_crc32_u64(
        reverse(mod(
          xor(
            zeroes(32) + reverse(t),
            zeroes(|t|) + reverse(zeroes(32))
          )
        )),
        xor(
          xor(
            mul_F2_X(
              reverse(mod(
                xor(
                  zeroes(32) + reverse(r),
                  zeroes(|r|) + reverse(prev)
                )
              )),
              pow_mod_crc(2 * 64 * n as int)
            ),
            mul_F2_X(
              reverse(mod(
                xor(
                  zeroes(32) + reverse(s),
                  zeroes(|s|) + reverse(zeroes(32))
                )
              )),
              pow_mod_crc(    64 * n as int)
            )
          ),
          u
        )
      );
      reverse(mod(
        xor(
          zeroes(32) + reverse(
            xor(
              xor(
                mul_F2_X(
                  reverse(mod(
                    xor(
                      zeroes(32) + reverse(r),
                      zeroes(|r|) + reverse(prev)
                    )
                  )),
                  pow_mod_crc(2 * 64 * n as int)
                ),
                mul_F2_X(
                  reverse(mod(
                    xor(
                      zeroes(32) + reverse(s),
                      zeroes(|s|) + reverse(zeroes(32))
                    )
                  )),
                  pow_mod_crc(    64 * n as int)
                )
              ),
              u
            )
          ),
          zeroes(64) + reverse(
            reverse(mod(
              xor(
                zeroes(32) + reverse(t),
                zeroes(|t|) + reverse(zeroes(32))
              )
            ))
          )
        )
      ));
      {
        combine3_lemma(n, r, s, t, u, prev);
      }
      reverse(mod(
        xor(
          zeroes(32) + reverse(r+s+t+u),
          zeroes(|r|+|s|+|t|+|u|) + reverse(prev)
        )
      ));
      {
        bits_of_bytes_additive4_slice(data, start, i - 16 * n, i - 8 * n, i - 8, i);
        assert r+s+t+u == bits_of_bytes(data[start..i]);
        reveal_advance();
      }
      advance(prev, bits_of_bytes(data[start..i]));
    }
  }

  lemma bits_of_int_ffffffff()
  ensures bits_of_int(0xffffffff, 32) == ones(32)
  {
  }

  lemma final_comp(data: seq<byte>, s: uint32, i: int, j: int, t: seq<byte>)
  requires 0 <= i <= j <= |data|
  requires |t| == 4
  requires advances_bytes(data, i, 0xffffffff, j, s)
  requires unpack_LittleEndian_Uint32(t) == bitxor32(s, 0xffffffff)
  ensures t == crc32_c(data[i..j])
  {
    var d := data[i..j];

    var bitstream := zeroes(32) + reverse(bits_of_bytes(d));
    var bitstream1 := xor(bitstream, zeroes(|bitstream|-32) + ones(32));
    var m := mod_F2_X(bitstream1, bits_of_int(0x1_1EDC_6F41, 33));
    var m1 := xor(reverse(m), ones(32));

    calc {
      crc32_c(data[i..j]);
      { reveal_crc32_c(); }
      [
        byte_of_bits(m1[0..8]),
        byte_of_bits(m1[8..16]),
        byte_of_bits(m1[16..24]),
        byte_of_bits(m1[24..32])
      ];
      {
        calc {
          m1;
          xor(reverse(m), ones(32));
          {
            calc {
              reverse(m);
              {
                calc {
                  m;
                  mod(bitstream1);
                  {
                    calc {
                      bitstream1;
                      xor(
                        zeroes(32) + reverse(bits_of_bytes(d)),
                        zeroes(|bits_of_bytes(d)|) + reverse(ones(32))
                      );
                    }
                  }
                  mod(xor(
                    zeroes(32) + reverse(bits_of_bytes(d)),
                    zeroes(|bits_of_bytes(d)|) + reverse(ones(32))
                  ));
                }
              }
              reverse(mod(xor(
                  zeroes(32) + reverse(bits_of_bytes(d)),
                  zeroes(|bits_of_bytes(d)|) + reverse(ones(32))
              )));
              {
                reveal_advance();
                bits_of_int_ffffffff();
              }
              advance(bits_of_int(0xffffffff, 32), bits_of_bytes(d));
              {
                reveal_advances_bytes();
              }
              bits_of_int(s as int, 32);
            }
          }
          xor(bits_of_int(s as int, 32), ones(32));
          { bits_of_int_ffffffff(); }
          xor(bits_of_int(s as int, 32), bits_of_int(0xffffffff, 32));
          bits_of_int(bitxor32(s, 0xffffffff) as int, 32);
        }
        BitLemmas.unpacked_bits(t, bitxor32(s, 0xffffffff), m1);
      }
      t;
    }
  }
}
