// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Helpers {
  export Spec provides addOne, addOne_result
  export Body reveals addOne
  export extends Spec
  function method addOne(n: nat): nat
  {
    n + 1
  }
  lemma addOne_result(n : nat)
     ensures addOne(n) == n + 1
  { }
}

module Mod1 {
  import A = Helpers`Body
  method m() {
    assert A.addOne(5) == 6; // succeeds, we have access to addOne's body
  }
  method m2() {
    //A.addOne_result(5); // Would be an error, addOne_result is not exported from Body
    assert A.addOne(5) == 6;
  }
}
module Mod2 {
  import A = Helpers`Spec
  method m() {
    assert A.addOne(5) == 6; // fails, we don't have addOne's body
  }
  method m2() {
    A.addOne_result(5);
    assert A.addOne(5) == 6; // succeeds due to result from addOne_result
  }
}
module Mod3 {
  import A = Helpers
  method m() {
    assert A.addOne(5) == 6; // fails, we don't have addOne's body
  }
}
