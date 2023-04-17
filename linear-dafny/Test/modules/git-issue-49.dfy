// RUN: %dafny /compileTarget:cpp "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module A { }
abstract module B { }
abstract module C { }

module A1 refines A { }
module B1 refines B { }

module D(c: C) { }

module X(a: A, b: B) refines C { }

import W = D(X(A1, B1))

method Main() {
}
