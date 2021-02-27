// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

linear datatype ASDF = ASDF(a: int)
linear datatype QWER = QWER(linear asdf: ASDF)

method {:extern} Assign<V>(inout v: V, newV: V)
ensures v == newV

method linlin(linear inout c: ASDF) returns (linear oo: ASDF)
ensures c.a == old_c.a + 1
ensures oo == old_c
{
  var oldA := c.a;
  oo := c;
  c := ASDF(oldA);
  assert(oldA == old_c.a);
  Assign(inout c.a, oldA + 1);
  assert(c.a == old_c.a + 1);
  if c.a == 30 {
    Assign(inout c.a, 30);
  } else {
    Assign(inout c.a, oldA + 1);
  }
  match c.a {
    case 44 => Assign(inout c.a, 44);
    case _ => Assign(inout c.a, oldA + 1);
  }
}

method asdf() {
  linear var q := QWER(ASDF(31));

  linear var c := linlin(inout q.asdf);

  assert q.asdf.a == 32;
  linear var QWER(asdf) := q;
  linear var ASDF(_) := asdf;
  linear var ASDF(_) := c;
}
