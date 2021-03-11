// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause


linear datatype Car = Car(passengers: nat) {
  linear inout method LoadPassengers(count: nat)
  ensures self.passengers == old_self.passengers + count
  {
    inout self.passengers := self.passengers + count;
  }
}

method Main() {
  linear var c := Car(13);
  inout c.LoadPassengers(4); 
  linear var Car(_) := c;
}
