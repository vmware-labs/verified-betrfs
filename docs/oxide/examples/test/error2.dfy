// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

linear datatype A = A(v: int)
linear datatype B = B(linear a1: A, linear a2: A)

method {:axiom} use(linear inout a1: A, linear inout a2: A)

method main() {
  linear var b := B(A(32), A(33));

  use(inout b.a1, inout b.a2);

  linear var B(A(_), A(_)) := b;
}
