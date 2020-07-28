
method {:extern} Drop<V>(linear v: V)

method {:extern} Assign<V>(inout v: V, newV: V)
ensures v == newV

linear datatype Car = Car(passengers: nat) {
  linear inout method LoadPassengers(count: nat)
  ensures this.passengers == old(this).passengers + count
  {
    var newCount := this.passengers + count;
    Assign(inout this.passengers, newCount);
  }
}

method LoadPassengers(linear inout self: Car, shared car: Car, count: nat)
ensures self.passengers == car.passengers + count
{
  Assign(inout self.passengers, car.passengers + count);
}

method LoadPassengers2(shared car: Car, linear inout self: Car, count: nat)
ensures self.passengers == car.passengers + count
{
  Assign(inout self.passengers, car.passengers + count);
}

method Passengers(shared self: Car)
returns (count: nat)
{
  return self.passengers;
}

method Main() {
  linear var c := Car(13);
  // LoadPassengers(inout c, c, 3);
  // LoadPassengers2(c, inout c, 3);
  Drop(c);
}
