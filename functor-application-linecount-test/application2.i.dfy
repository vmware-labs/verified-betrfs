include "base.i.dfy"

module Instance2 refines Prototype {
  predicate A() { false }
}

module Application2 {
  import BM = BaseModule(Instance2)

  method C() {
    var x := BM.ProduceB();
  }
}
