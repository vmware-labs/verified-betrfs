module BaseModule {
  function{:opaque} F(i:int):int { i + 1 }

  lemma LBase() {
    reveal_F();
    assert F(10) == 11;
  } 
}

module UpperModule {
  import A = BaseModule

  lemma LUpper() {
 //   reveal_F();
    assert A.F(10) == 11;
  } 
}
