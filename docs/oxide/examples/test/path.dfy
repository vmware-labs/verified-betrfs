// Copyright 2018-2021 VMware, Inc.
// SPDX-License-Identifier: MIT


method {:extern} Drop<V>(linear v: V)

method {:extern} Assign<V>(inout v: V, newV: V)
ensures v == newV

// ERROR TEST datatype Car = Car(passengers: nat)
linear datatype Car = Car(passengers: nat)
linear datatype Train = Train(linear car: Car)

method LoadPassengers(linear inout self: Train, count: nat)
ensures self.car.passengers == self.car.passengers + count
{
  Assign(inout self.car.passengers, self.car.passengers + count);
}

// ERROR TEST datatype Lin = Lin(passengers: nat)
linear datatype Lin = Lin(passengers: nat)

method Main() {
  linear var t := Train(Car(13));
  LoadPassengers(inout t, 3);
  linear var l := Lin(33);
  Assign(inout l.passengers, 12);
  Drop(t);
  Drop(l);
}
