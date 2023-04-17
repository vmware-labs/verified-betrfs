// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module Foo {
  method Do(linear inout s: seq<int>)
}

module Food refines Foo {
  method Do(linear inout s: seq<int>) {
  }
}
