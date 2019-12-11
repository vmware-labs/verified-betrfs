

class Owner {
  var a1 : A;
  var a2 : A;
  ghost var Repr : set<object>;

  predicate Inv()
    reads this, this.Repr
  {
    && a1 in Repr
    && a2 in Repr
    && Repr == {this} + a1.Repr + a2.Repr
    && {this} !! a1.Repr !! a2.Repr
    && a1.Inv()
    && a2.Inv()
  }

  constructor()
    ensures Inv()
  {
    a1 := new A();
    a2 := new A();
    new;
    Repr := {this} + a1.Repr + a2.Repr;
  }

  method MethodUnderTest()
    requires Inv()
    modifies a1.Repr
  {
    a2.establishSomething();
    assert a2.Something();
    assert {this} !! a1.Repr !! a2.Repr;
    a1.changeSomething();
    assert {this} !! a1.Repr !! a2.Repr;
    assert a2.Something();
  }
}
