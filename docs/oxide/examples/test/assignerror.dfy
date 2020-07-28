datatype A = A(v: nat)
linear datatype B = B(a: A)

method LoadPassengers(linear inout self: B, count: nat)
ensures self.a.v == old_self.a.v + count
{
  // inout self.a := A(self.a.v + count);
  inout self.a.v := self.a.v + count;
}

