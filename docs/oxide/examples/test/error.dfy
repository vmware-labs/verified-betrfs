// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

linear datatype A = A(v: int)
linear datatype B = B(linear a: A)

method {:extern} Assign<V>(inout v: V, newV: V)
ensures v == newV

method main() {
  linear var b := B(A(32));

  ghost var b0 := b;

  var newV := b.a.v + 5;
  Assign(inout b.a.v, inout newV);

  assert b.a.v == b0.a.v + 5;

  linear var B(A(_)) := b;
}
