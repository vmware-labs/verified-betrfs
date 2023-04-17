module LinearInout2 {

linear datatype Val0 = Leaf(x:bool)

method flip(linear inout v: Val0)
ensures v.x == !old_v.x
{
  inout v.x := !v.x;
}

method Main() {
  linear var v := Leaf(false);
  flip(inout v);
  var b := v.x;
  assert b;
  print b;
  linear var Leaf(_) := v;
}

}
