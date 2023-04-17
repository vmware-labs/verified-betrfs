// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module A { }

module B(a: A) { }

abstract module C { }

module D refines C { }

module X(c: C) refines A { }

import t = B(X(D))

method Main()
{
}
