include "base.i.dfy"

module Instance1 refines Prototype {
  predicate A() { true }
}

module Application1 {
  import BM = BaseModule(Instance1)

  method C() {
    var x := BM.ProduceB();
  }
}
