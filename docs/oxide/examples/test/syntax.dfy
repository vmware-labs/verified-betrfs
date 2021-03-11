// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause


method {:extern} Drop<V>(linear v: V)

method {:extern} Assign<V>(inout v: V, newV: V)
ensures v == newV

// linear datatype Car = Car(passengers: nat)

// method LoadPassengers(linear c: Car, count: nat) returns (linear c': Car)
// ensures c'.passengers == c.passengers + count
// {
//   var newCount := this.passengers + count;
//   linear var Car(passengers) := c;
//   c' := Car(newCount);
// }

linear datatype Car = Car(passengers: nat) {
  linear inout method LoadPassengers(count: nat)
  ensures self.passengers == old_self.passengers + count
  {
    var newCount := self.passengers + count;
    Assign(inout self.passengers, newCount);
  }
}

// method LoadPassengers(linear inout self: Car, count: nat)
// ensures self.passengers == old(self).passengers + count
// {
//   Assign(inout self.passengers, self.passengers + count);
// }

method Passengers(shared self: Car)
returns (count: nat)
{
  return self.passengers;
}

method Main() {
  linear var c := Car(13);
  inout c.LoadPassengers(3);
  Drop(c);
}
