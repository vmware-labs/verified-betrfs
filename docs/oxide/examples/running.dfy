// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause


method {:extern} Assign<V>(inout v: V, newV: V)
ensures v == newV

{
  v := newV;
}

method {:extern} Replace<V>(linear inout v: V, linear newV: V)
returns (linear replaced: V)
ensures replaced == old(v)
ensures v == newV

{
  replaced := v;
  v := newV;
}

method {:extern} Swap<V>(linear inout a: V, linear inout b: V)
ensures b == old(a)
ensures a == old(b)

{
  linear var tmp := a;
  a := b;
  b := tmp;
}

linear datatype Loco = Loco(fuel: nat)
linear datatype Car = Car(passengers: nat)

method LoadPassengers(linear inout self: Car, count: nat)

method LoadPassengers(linear inout self: Car, count: nat)
ensures self.passengers == old(self).passengers + count
{
  var newCount := self.passengers + count;
  Assign(inout self.passengers, newCount);
}

method LoadPassengers(linear inout self: Car, count: nat)
ensures self.passengers == old(self).passengers + count
{
  var newCount := self.passengers + count;
  ghost var beforeLoad := self;
  Assign(inout self.passengers, newCount);
  assert beforeLoad == old(self);
  assert beforeLoad.passengers == self.passengers - count;
}

linear datatype Train = Train(linear loco: Loco, linear car1: Car, linear car2: Car)
{
  linear inout method LoadFuel(fuel: nat) {
    // `this` is `linear inout` here
    var newFuel := train.loco.fuel + fuel;
    Assign(inout train.loco.fuel, newFuel);
  }
}

linear var train: Train := ...;
LoadPassengers(linear inout train.car1);

linear datatype Loco = Loco(fuel: nat)
linear datatype Car = Car(passengers: nat)
linear datatype Train = Train(linear loco: Loco, linear car1: Car, linear car2: Car)

method Rail(linear train: Train) {
  /* valid path for an `ordinary inout` reference: */ train.car2.passengers
  /* valid path for a `linar inout` reference: */ train.car2
}
