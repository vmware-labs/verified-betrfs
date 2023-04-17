// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module ABase {
  type Key
}

abstract module P(A: ABase) {
  method Test(a:A.Key)
}

module AConsumer(b:P(ABase)) {
  method MyTest(x:b.A.Key) {
    b.Test(x);
  }
}
