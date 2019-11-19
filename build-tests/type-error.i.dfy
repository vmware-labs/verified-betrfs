// This file produces a failure during type checking.
predicate foo(x:int) { true }

method bar() {
    foo(7, 7);
}
