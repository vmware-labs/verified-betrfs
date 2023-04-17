// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Foo(linear inout s: seq<int>)
method Bar(linear inout s: seq<int>) {
  Foo(inout s);
}
