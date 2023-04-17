module LinearInout2 {

linear datatype Val0 = Leaf(x:bool, ghost x2:bool)

method flip(linear inout v: Val0)
ensures v.x == !old_v.x
ensures v.x2 == v.x
{
  inout v.x := !v.x;
  inout ghost v.x2 := v.x;
}

method Main() {
  linear var v := Leaf(false, false);
  flip(inout v);
  var b := v.x;
  assert b;
  assert v.x2;
  print b;
  linear var Leaf(_, _) := v;
}

}
