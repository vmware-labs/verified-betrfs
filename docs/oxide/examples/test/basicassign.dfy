// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

linear datatype A = A(v: nat, ghost v2: nat)
linear datatype B = B(linear a: A)

predicate Inv(b: B) {
  b.a.v == b.a.v2
}

method LoadPassengers(linear inout self: B, count: nat)
requires Inv(old_self)
ensures Inv(self)
ensures self.a.v == old_self.a.v + count
{
  inout self.a.v := self.a.v + count;
  inout ghost self.a.v2 := self.a.v2 + count;
}

