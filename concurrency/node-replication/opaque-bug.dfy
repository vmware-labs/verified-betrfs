
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
 //   reveal_F();
    assert A.F(10) == 11;
  } 
}

