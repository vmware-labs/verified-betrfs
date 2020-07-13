
method {:extern} Drop<V>(linear v: V)

method {:extern} Assign<V>(inout v: V, newV: V)
ensures v == newV

datatype Car = Car(passengers: nat)
linear datatype Train = Train(car: Car)

method LoadPassengers(linear inout self: Train, count: nat)
ensures self.car.passengers == self.car.passengers + count
{
  Assign(inout self.car.passengers, self.car.passengers + count);
}

method Main() {
  linear var t := Train(Car(13));
  LoadPassengers(inout t, 3);
  Drop(t);
}
