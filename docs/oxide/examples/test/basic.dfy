linear datatype Car = Car(passengers: nat)

method {:extern} Drop<V>(linear v: V)

method {:extern} Assign<V>(inout v: V, newV: V)
ensures v == newV

method LoadPassengers(linear inout self: Car, count: nat) returns (a: Car)
ensures self.passengers == old(self).passengers + count
{
  var newCount := self.passengers + count;
  // Assign(inout self.passengers, newCount);
  Drop(self);
}
