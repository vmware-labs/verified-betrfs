class BoxedInt {
  var v: int;

  constructor (v_: int)
  ensures v == v_
  {
    v := v_;
  }
}

method Bar(x: BoxedInt, y: BoxedInt)
modifies x
{
  x.v := 5;
}

method Foo(x: BoxedInt, y: BoxedInt)
requires y.v == 20

modifies x
{
  Bar(x, y);

  // assert y.v == 20;
}

method Main()
{
  var x := new BoxedInt(10);
  var y := new BoxedInt(20);

  Foo(x, x);
}

predicate IsFive(x: BoxedInt)
reads x
{
  && x.v == 5
}
