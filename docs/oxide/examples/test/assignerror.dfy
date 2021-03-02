// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

datatype A = A(v: nat)
linear datatype B = B(a: A)

method LoadPassengers(linear inout self: B, count: nat)
ensures self.a.v == old_self.a.v + count
{
  // inout self.a := A(self.a.v + count);
  inout self.a.v := self.a.v + count;
}

