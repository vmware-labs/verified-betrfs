include "PCMExt.s.dfy"

abstract module EasyExt refines PCMExt {
  // Fill these in
  predicate Inv(f: F)
  function Interp(f: F) : B
    requires Inv(f)
  predicate InternalStep(f: F, f': F)
  predicate CrossStep(f: F, f': F, b: B, b': B)

  lemma interp_unit()
  ensures Inv(unit()) && Interp(unit()) == Base.unit()

  lemma internal_step_preserves_valid(p: F, f: F, f': F)
  requires InternalStep(f, f')
  requires dot_defined(p, f)
  ensures dot_defined(p, f')

  lemma internal_step_preserves_interp(p: F, f: F, f': F)
  requires InternalStep(f, f')
  requires dot_defined(p, f)
  requires Inv(dot(p, f))
  ensures dot_defined(p, f')
  ensures Inv(dot(p, f'))
  ensures Interp(dot(p, f')) == Interp(dot(p, f))

  // Cool stuff you get

  function method init(glinear b: Base.Token, ghost f': F) : (glinear f_out: Token)
  requires Inv(f')
  requires Interp(f') == b.get()
  ensures f_out.loc().ExtLoc? && f_out.loc().l == b.loc()
  ensures f_out.get() == f'
  {
    ext_init(b, f')
  }

  // Justification

  predicate rep(f: F, b: B) {
    Inv(f) && Interp(f) == b
  }

  predicate transition(a: M, b: M) {
    exists x, y, z :: dot_defined(x, z) && dot_defined(y, z) && dot(x, z) == a && dot(y, z) == b && InternalStep(x, y)
  }

  lemma transition_is_monotonic(a: M, b: M, c: M)
  //requires transition(a, b)
  //requires dot_defined(a, c)
  //ensures dot_defined(b, c)
  //ensures transition(dot(a, c), dot(b, c))
  {
    var x, y, z :| dot_defined(x, z) && dot_defined(y, z) && dot(x, z) == a && dot(y, z) == b && InternalStep(x, y);
    commutative(x, z);
    commutative(dot(x, z), c);
    commutative(x, z);
    associative(c, z, x);
    commutative(dot(c, z), x);
    /*calc {
      dot(dot(x, z), c);
      dot(c, dot(x, z));
      dot(c, dot(z, x));
      dot(dot(c, z), x);
      dot(x, dot(c, z));
    }*/
    internal_step_preserves_valid(dot(c, z), x, y);
    commutative(dot(c, z), y);
    commutative(c, z);
    associative(y, z, c);
    /*calc {
      dot(dot(c, z), y);
      dot(y, dot(c, z));
      dot(y, dot(z, c));
      dot(dot(y, z), c);
    }*/
  }

  lemma rep_unit()
  //ensures rep(unit(), Base.unit())
  {
    interp_unit();
  }

  lemma rep_equiv(f: F, b: B, b': B)
  //requires rep(f, b)
  //requires rep(f, b')
  //ensures Base.reachable(b, b')
  {
  }

  lemma rep_trans(f: F, f': F, p: F, b: B)
  returns (b': B)
  //requires dot_defined(f, p) && rep(dot(f, p), b)
  //requires transition(f, f')
  //ensures Base.reachable(b, b')
  //ensures dot_defined(f', p) && rep(dot(f', p), b')
  {
    transition_is_monotonic(f, f', p);

    var x, y, z :| dot_defined(x, z) && dot_defined(y, z) && dot(x, z) == dot(f,p) && dot(y, z) == dot(f',p) && InternalStep(x, y);

    commutative(f,p);
    commutative(f',p);
    commutative(y, z);
    commutative(x, z);

    internal_step_preserves_interp(z, x, y);

    b' := b;
  }

}
