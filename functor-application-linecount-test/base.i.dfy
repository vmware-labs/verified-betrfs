module Prototype {
  predicate A()
}

module BaseModule(p: Prototype) {
  predicate method B() {
    false
  }

  lemma AvsB() {
    assert p.A();
    assert !B();
  }

  method ProduceB() returns (x:bool) {
    x := B();
  }

  method BunchOfWastedBreath() {
    var x := 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
  }
}
