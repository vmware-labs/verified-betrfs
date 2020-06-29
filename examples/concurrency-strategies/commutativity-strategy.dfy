include "spec.s.dfy"

module TheoremProof {

  lemma Correctness(b:Behavior<Concrete.State>, I:CState->AState)
    requires Reachable(b, Concrete.Init, Concrete.Next)
    ensures var ab := Interpret(b, I); Reachable(ab, Abstract.Init, Abstract.Next)
  {
    var ab := Interpret(b, I);

    if (b is in the good TLA order) {
      call the tla refinement proof
    } else {
      pick an index very carefully:
        - terminates
        - can satisfy ind. hyp.
      var b' := swap(b, idx)
      assert Reachable(b', Concrete.Init, Concrete.Next);
 
      var ab' := Interpret(b', I);  // required by spec
      Correctness(b', I);
      assert Reachable(ab', Abstract.Init, Abstract.Next);


      assert Reachable(ab, Abstract.Init, Abstract.Next);
    }
  }
  

}
