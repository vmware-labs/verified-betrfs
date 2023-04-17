module LinearInout2 {

linear datatype Val0 = Leaf(x:bool) {
  linear inout method flip_inner()
  ensures self.x == !old_self.x
  {
    inout self.x := !self.x;
  }

  linear inout method flip()
  ensures self.x == !old_self.x
  {
    inout self.flip_inner();
  }
}

method Main() {
  linear var v := Leaf(true);
  inout v.flip();
  var b := v.x;
  assert !b;
  print b;
  linear var Leaf(_) := v;
}

}
