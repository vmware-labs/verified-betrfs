include "PCM.s.dfy"

abstract module BasicPCM refines PCM {
  predicate transition(a: M, b: M) {
    forall c :: valid(dot(a, c)) ==> valid(dot(b, c))
  }
  
  lemma transition_is_refl(a: M)
  {
  }

  lemma transition_is_trans(a: M, b: M, c: M)
  {
  }

  lemma transition_is_monotonic(a: M, b: M, c: M)
  {
    forall d | valid(dot(dot(a, c), d))
    ensures valid(dot(dot(b, c), d))
    {
      associative(a, c, d);
      associative(b, c, d);
    }
  }
}
