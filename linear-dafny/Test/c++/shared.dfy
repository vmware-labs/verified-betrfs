// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

linear datatype Option<V> = Some(linear value: V) | None

method get_value_select<V>(shared x: Option<V>, shared y: Option<V>, b: bool)
returns (shared v: V)
requires x.Some?
requires y.Some?
{
  shared var res: V;
  if b {
    res := x.value;
  } else {
    res := y.value;
  }
  v := res;
}

method get_value_select2<V>(shared x: Option<V>, shared y: Option<V>, b: bool)
returns (shared v: V, shared v2: V)
requires x.Some?
requires y.Some?
{
  shared var res: V;
  if b {
    res := x.value;
  } else {
    res := y.value;
  }

  v := res;
  v2 := res;
}

function method fm_get_value_select<V>(shared x: Option<V>, shared y: Option<V>, b: bool)
 : (shared v: V)
requires x.Some?
requires y.Some?
{
  shared var res: V := 
    if b then
      x.value
    else
      y.value;
  res
}

function method fm_get_value_select2<V>(shared x: Option<V>, shared y: Option<V>, b: bool)
 : (shared v: V)
requires x.Some?
requires y.Some?
{
  fm_get_value_select(x, y, b)
}

function method identity<V>(shared x: Option<V>) : (shared y: Option<V>)
{
  x
}

function method get_value<V>(shared x: Option<V>) : (shared y: V)
requires x.Some?
{
  x.value
}

function method get_value2<V>(shared x: Option<V>) : (shared y: V)
requires x.Some?
{
  identity(x).value
}

method run<V>(shared x: Option<V>, shared y: Option<V>, b: bool)
returns (shared a': V, shared b': V, shared c': V, shared d': V, shared e': V)
requires x.Some?
requires y.Some?
{
  shared var v := get_value_select(x, y, b);
  shared var v1, v2 := get_value_select2(x, y, b);

  shared var v3 := fm_get_value_select(x, y, b);
  shared var v4 := fm_get_value_select2(x, y, b);

  a' := v;
  b' := v1;
  c' := v2;
  d' := v3;
  e' := v4;
}

newtype uint32 = i:int | 0 <= i < 0x100000000

linear datatype Foo = Foo(x: uint32)

method get_value_from_foo(shared foo: Foo)
returns (y: uint32)
{
  y := foo.x;
}

method borrow_stuff(shared x: Option<Foo>, shared y: Option<Foo>)
requires x.Some?
requires y.Some?
{
  shared var a, b, c, d, e := run(x, y, true);
  var a_x := a.x;
  var b_x := b.x;
  var c_x := c.x;
  var d_x := d.x;
  var e_x := e.x;

  print a_x, "\n";
  print b_x, "\n";
  print c_x, "\n";
  print d_x, "\n";
  print e_x, "\n";

  a, b, c, d, e := run(x, y, false);

  a_x := a.x;
  b_x := b.x;
  c_x := c.x;
  d_x := d.x;
  e_x := e.x;

  print a_x, "\n";
  print b_x, "\n";
  print c_x, "\n";
  print d_x, "\n";
  print e_x, "\n";

  shared match x {
    case Some(foo) => {
      shared match foo {
        case Foo(i) => {
          print "in case ", i, "\n";
        }
      }
    }
  }

  //var y := get_value_from_foo(
  //    ( shared match x { case Some(foo) => foo } )
  //  );
  //print "y is ", y, "\n";

  shared var gv1 := get_value(x);
  shared var gv2 := get_value2(x);
  var gv1_x := gv1.x;
  var gv2_x := gv2.x;
  print "gv1, ", gv1_x, "\n";
  print "gv2, ", gv2_x, "\n";

}

method Main() {
  linear var foo1 := Foo(1);
  linear var foo2 := Foo(2);

  linear var s1 := Some(foo1);
  linear var s2 := Some(foo2);
  borrow_stuff(s1, s2);

  print "----\n";
  linear match s1 {
    case Some(foo_1) => {
      linear match foo_1 {
        case Foo(x_1) => print x_1, "\n";
      }
    }
  }

  linear match s2 {
    case Some(foo_2) => {
      linear match foo_2 {
        case Foo(x_2) => print x_2, "\n";
      }
    }
  }
}
