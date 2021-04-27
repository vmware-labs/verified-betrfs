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

  lemma cross_step_preserves_valid(p: F, f: F, f': F, b: B, b': B)
  requires CrossStep(f, f', b, b')
  requires dot_defined(p, f)
  ensures dot_defined(p, f')

  lemma cross_step_preserves_interp(p: F, f: F, f': F, b: B, b': B)
  requires CrossStep(f, f', b, b')
  requires dot_defined(p, f)
  requires Inv(dot(p, f))
  requires Base.dot_defined(Interp(dot(p, f)), b)
  ensures dot_defined(p, f')
  ensures Inv(dot(p, f'))
  ensures Base.dot_defined(Interp(dot(p, f')), b')
  ensures Base.dot(Interp(dot(p, f')), b')
       == Base.dot(Interp(dot(p, f)), b)

  // Cool stuff you get

  function method init(glinear b: Base.Token, ghost f': F) : (glinear f_out: Token)
  requires Inv(f')
  requires Interp(f') == b.get()
  ensures f_out.loc().ExtLoc? && f_out.loc().base_loc == b.loc()
  ensures f_out.get() == f'
  {
    ext_init(b, f')
  }

  glinear method do_internal_step(glinear f: Token, ghost f': F)
  returns (glinear f_out: Token)
  requires InternalStep(f.get(), f')
  ensures f_out.loc() == f.loc()
  ensures f_out.get() == f'
  {
    gshared var u := get_unit_shared(f.loc());
    dot_unit(f.get());
    dot_unit(f');
    commutative(f', u.get());
    commutative(f.get(), u.get());
    assert dot_defined(u.get(), f');
    assert transition(f.get(), f');
    assert transition(
        dot(u.get(), f.get()),
        dot(u.get(), f'));
    f_out := transition_update(u, f, f');
  }

  glinear method do_cross_step(
      glinear f: Token, ghost f': F,
      glinear b: Base.Token, ghost b': B)
  returns (glinear f_out: Token, glinear b_out: Base.Token)
  requires CrossStep(f.get(), f', b.get(), b')
  requires f.loc().ExtLoc? && f.loc().base_loc == b.loc()
  ensures f_out.loc() == f.loc()
  ensures b_out.loc() == b.loc()
  ensures f_out.get() == f'
  ensures b_out.get() == b'
  {
    forall p, q | dot_defined(f.get(), p) && rep(dot(f.get(), p), q) && Base.dot_defined(b.get(), q)
    ensures exists q' ::
      dot_defined(f', p) &&
      rep(dot(f', p), q') &&
      Base.dot_defined(b', q') &&
      Base.reachable(Base.dot(b.get(), q), Base.dot(b', q'))
    {
      assert q == Interp(dot(f.get(), p));
      cross_step_preserves_valid(p, f.get(), f', b.get(), b');
      cross_step_preserves_interp(p, f.get(), f', b.get(), b');
      var q' := q;
      assert dot_defined(f', p);
      assert rep(dot(f', p), q');
      assert Base.dot_defined(b', q');
      assert Base.reachable(Base.dot(b.get(), q), Base.dot(b', q'));
    }

    f_out, b_out := ext_transfer(f, b, f', b');
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

  lemma internal_rep_equiv(f: F, b: B, b': B)
  //requires rep(f, b)
  //requires rep(f, b')
  //ensures Base.reachable(b, b')
  {
  }

  lemma cross_rep_conserves(f: F, f': F, p: F, b: B)
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
