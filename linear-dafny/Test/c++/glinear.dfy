// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Token = Token(ghost loc: nat, ghost val: nat)

// Ideally, all these should be compiled out:

glinear method {:extern} method_1(glinear u: Token)
returns (glinear g: Token)

function method {:extern} function_method_1(glinear u: Token) : glinear Token

glinear method method_2(glinear u: Token)
returns (glinear g: Token)
{
  g := method_1(u);
}

function method function_method_2(glinear u: Token) : glinear Token {
  function_method_1(u)
}

function method {:extern} init() : glinear Token
glinear method {:extern} dispose(glinear u: Token)

// Main method should compile:

newtype uint32 = i:int | 0 <= i < 0x100000000

method Main()
{
  // real code:
  var a: uint32 := 5;
  print a, "\n";

  // but this ghost code should be eliminated:

  glinear var t := init();
  t := method_1(t);
  t := function_method_1(t);
  t := method_2(t);
  t := function_method_2(t);
  dispose(t);
}

// glinear fields should be erased:

linear datatype Foo = Foo(
  a: uint32,
  glinear b: int,
  ghost c: int,
  linear d: uint32)

// should not be compiled at all

glinear datatype Moo = Foo(
  glinear b: int,
  ghost c: int)

method method1(a: uint32, glinear foo: Foo)
returns (b: uint32, glinear foo': Foo)
requires a < 100
{
  b := a + 1;
  foo' := foo;
}

method method2(a: uint32, glinear foo: Foo)
returns (b: uint32, glinear foo': Foo)
requires a < 100
{
  b, foo' := method1(a, foo);
}

method method3(a: uint32, glinear inout foo: Foo)
returns (b: uint32)
requires a < 100
{
  b := a + 1;
}

method method4(a: uint32, glinear inout foo: Foo)
returns (b: uint32)
requires a < 100
{
  b := method3(a, inout foo);
}
