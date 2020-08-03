
linear datatype Car = Car(passengers: nat)

linear datatype B = B(linear c: Car)

method Something(inout c: Car)
{
  inout passengers := passengers + 2;
}

method Main() {
  linear var c := Car(4);
  Something(inout c.passengers);
  linear var Car(_) := c;
}

// method Something(inout b: nat, b2: nat) {
//   inout b := b2;
// }
// 
// method main() {
//   var c := Car(23);
//   Something(inout c.passengers, 40);
// }
// 
// Something(
// 
// linear datatype lOption<V> = lNone | lSome(linear value: V)
// 
// linear datatype T = T(linear c: lOption<Car>) {
//   linear inout method LoadPassengers(count: nat)
//   requires old_self.c.lSome?
//   {
//     inout self.c.value.LoadPassengers(count);
//   }
// }
