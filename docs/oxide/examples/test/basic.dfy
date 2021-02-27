// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT

linear datatype Car = Car(passengers: nat)

method {:extern} Assign<V>(inout v: V, newV: V)
ensures v == newV

method {:extern} AssignGhost<V>(inout ghost v: V, newV: V)
ensures v == newV

method LoadPassengers(linear inout self: Car, count: nat) returns (a: Car)
ensures self.passengers == old(self).passengers + count
{
  var newCount := self.passengers + count;
  Assign(inout ghost self.passengers, newCount);
}
