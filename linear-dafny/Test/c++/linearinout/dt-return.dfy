module LinearInout2 {

linear datatype Val0 = Leaf(x:bool) {
  linear inout method flip() returns (prev: bool)
  ensures self.x == !old_self.x
  ensures prev == old_self.x
  {
    prev := self.x;
    inout self.x := !self.x;
  }
}

method Main() {
  linear var v := Leaf(true);
  var p := inout v.flip();
  var b := v.x;
  assert p;
  assert !b;
  print b;
  linear var Leaf(_) := v;
}

}
