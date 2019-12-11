class A {
  ghost var Repr:set<object>

  constructor()
    ensures fresh(Repr)
    ensures Inv()
  {
    Repr := { this };
  }

  predicate Inv()
    reads this
  {
    this in Repr
  }

  predicate Something()
    reads this, Repr

  method changeSomething()
    requires Inv()
    ensures fresh(Repr - old(Repr))
    ensures Inv()
    modifies Repr

  method establishSomething()
    ensures Something()
}
