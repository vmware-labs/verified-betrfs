// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module X {
}

module BaseModule(x: X) {
  function{:opaque} F(i:int):int { i + 1 }

  lemma LBase() {
    reveal F();
    assert F(10) == 11;
  }
}

module UpperModule(x1: X) {
  import A = BaseModule(x1)

  lemma LUpper() {
  //reveal A.F();
    assert A.F(10) == 11; // Passed, even though it should fail without uncommenting the reveal above
  }
}

/*
 * This morally equivalent program fails at the expected assertion.
module BaseModule {
  function{:opaque} F(i:int):int { i + 1 }

//  lemma LBase() {
//    reveal_F();
//    assert F(10) == 11;
//  }
}

module UpperModule {
  import A = BaseModule

  lemma LUpper() {
    assert A.F(10) == 11;
  }
}
*/
