module LinearInout2 {

linear datatype Val0 = Leaf(x:bool)

method flip(linear inout v: Val0) returns (prev: bool)
ensures v.x == !old_v.x
ensures prev == old_v.x
{
  prev := v.x;
  inout v.x := !v.x;
}

method Main() {
  linear var v := Leaf(false);
  var p := flip(inout v);
  var b := v.x;
  assert b;
  assert !p;
  print b;
  print "\n";
  print p;
  linear var Leaf(_) := v;
}

}
