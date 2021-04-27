include "../framework/PCMExt.s.dfy"

abstract module SimpleExt {
  import Base : PCM

  type F(!new,==)

  function unit() : F
  predicate dot_defined(a: F, b: F)
  function dot(a: F, b: F) : F
    requires dot_defined(a, b)

  lemma dot_unit(x: F)
  ensures dot_defined(x, unit())
  ensures dot(x, unit()) == x

  lemma commutative(x: F, y: F)
  requires dot_defined(x, y)
  ensures dot_defined(y, x)
  ensures dot(x, y) == dot(y, x)

  lemma associative(x: F, y: F, z: F)
  requires dot_defined(y, z)
  requires dot_defined(x, dot(y, z))
  ensures dot_defined(x, y)
  ensures dot_defined(dot(x, y), z)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)

  predicate Inv(a: F)

  function Interp(a: F) : Base.M
    requires Inv(a)

  predicate InternalNext(f: F, f': F)
  predicate CrossNext(f: F, f': F, b: Base.M, b': Base.M)

  lemma interp_unit()
  ensures Inv(unit()) && Interp(unit()) == Base.unit()

  lemma internal_step_preserves_interp(p: F, f: F, f': F)
  requires InternalNext(f, f')
  requires dot_defined(f, p)
  requires Inv(dot(f, p))
  ensures dot_defined(f', p)
  ensures Inv(dot(f', p))
  ensures Interp(dot(f', p)) == Interp(dot(f, p))

  lemma cross_step_preserves_interp(p: F, f: F, f': F, b: Base.M, b': Base.M)
  requires CrossNext(f, f', b, b')
  requires dot_defined(f, p)
  requires Inv(dot(f, p))
  requires Base.dot_defined(Interp(dot(f, p)), b)
  ensures dot_defined(f', p)
  ensures Inv(dot(f', p))
  ensures Base.dot_defined(Interp(dot(f', p)), b')
  ensures Base.dot(Interp(dot(f', p)), b')
       == Base.dot(Interp(dot(f, p)), b)

  /*lemma interp_monotonic(a: F, b: F)
  requires Inv(a)
  requires dot_defined(a, b) && Inv(dot(a, b))
  ensures Base.le(Interp(a), Interp(dot(a, b)))*/
}

abstract module SimpleExtPCM refines PCMExt {
  import SE = SimpleExt
  import Base = SimpleExt.Base

  predicate Valid(f: SE.F) {
    exists a :: SE.dot_defined(f, a) && SE.Inv(SE.dot(f, a))
  }

  type M = f: SE.F | Valid(f)
    witness *

  function unit() : M {
    assert Valid(SE.unit()) by {
      SE.dot_unit(SE.unit());
      SE.interp_unit();
    }
    SE.unit()
  }

  predicate dot_defined(x: M, y: M)
  {
    && SE.dot_defined(x, y)
    && Valid(SE.dot(x, y))
  }

  function dot(x: M, y: M) : M
  //requires dot_defined(x, y)
  {
    SE.dot(x, y)
  }

  lemma dot_unit(x: M)
  //ensures dot_defined(x, unit())
  //ensures dot(x, unit()) == x
  {
    SE.dot_unit(x);
  }

  lemma commutative(x: M, y: M)
  //requires dot_defined(x, y)
  //ensures dot_defined(y, x)
  //ensures dot(x, y) == dot(y, x)
  {
    SE.commutative(x, y);
  }

  lemma SE_assoc_general(x: SE.F, y: SE.F, z: SE.F)
  ensures SE.dot_defined(y, z) && SE.dot_defined(x, SE.dot(y, z)) ==>
    && SE.dot_defined(x, y)
    && SE.dot_defined(SE.dot(x, y), z)
    && SE.dot(x, SE.dot(y, z)) == SE.dot(SE.dot(x, y), z)
  ensures SE.dot_defined(x, y) && SE.dot_defined(SE.dot(x, y), z) ==>
    && SE.dot_defined(y, z) && SE.dot_defined(x, SE.dot(y, z))
    && SE.dot(x, SE.dot(y, z)) == SE.dot(SE.dot(x, y), z)
  {
    if SE.dot_defined(y, z) && SE.dot_defined(x, SE.dot(y, z)) {
      SE.associative(x, y, z);
    }
    if SE.dot_defined(x, y) && SE.dot_defined(SE.dot(x, y), z) {
      SE.commutative(x, y);
      SE.commutative(SE.dot(x, y), z);
      SE.associative(z, y, x);
      SE.commutative(z, y);
      SE.commutative(SE.dot(y, z), x);
    }
  }

  lemma associative(x: M, y: M, z: M)
  //requires dot_defined(y, z)
  //requires dot_defined(x, dot(y, z))
  //ensures dot_defined(x, y)
  //ensures dot_defined(dot(x, y), z)
  //ensures dot(x, dot(y, z)) == dot(dot(x, y), z)
  {
    SE.associative(x, y, z);
    assert Valid(SE.dot(x, y)) by {
      var w :|
           SE.dot_defined(SE.dot(SE.dot(x, y), z), w)
        && SE.Inv(SE.dot(SE.dot(SE.dot(x, y), z), w));
      SE_assoc_general(SE.dot(x, y), z, w);
      assert SE.dot_defined(z, w);
      assert SE.dot_defined(SE.dot(x, y), SE.dot(z, w));
      assert SE.Inv(SE.dot(SE.dot(x, y), SE.dot(z, w)));
    }
  }

  predicate transition(a: M, b: M)
  {
    exists x, y, z ::
      && SE.dot_defined(x, z)
      && SE.dot_defined(y, z)
      && a == SE.dot(x, z)
      && b == SE.dot(y, z)
      && SE.InternalNext(x, y)
  }

  lemma transition_is_monotonic(a: M, b: M, c: M)
  //requires transition(a, b)
  //requires dot_defined(a, c)
  //ensures dot_defined(b, c)
  //ensures transition(dot(a, c), dot(b, c))
  {
    var x, y, z :|
      && SE.dot_defined(x, z)
      && SE.dot_defined(y, z)
      && a == SE.dot(x, z)
      && b == SE.dot(y, z)
      && SE.InternalNext(x, y);

    var w :| SE.dot_defined(SE.dot(a, c), w) && SE.Inv(SE.dot(SE.dot(a, c), w));

    // SE.Inv( ((x . z) . c) . w )
    // need
    // SE.Inv( (x . (z . c . w)))

    SE_assoc_general(x, z, c);
    SE_assoc_general(x, SE.dot(z, c), w);
    SE_assoc_general(y, z, c);
    SE_assoc_general(y, SE.dot(z, c), w);

    /*assert SE.dot_defined(z, c);
    assert SE.dot_defined(x, SE.dot(z, c));
    assert SE.dot_defined(a, c);
    assert dot(a, c) == SE.dot(x, SE.dot(z, c));*/

    SE.internal_step_preserves_interp(SE.dot(SE.dot(z, c), w), x, y);

    //assert dot_defined(b, c);
    //assert transition(dot(a, c), dot(b, c));
  }

  predicate rep(f: F, b: B) {
    SE.Inv(f) && SE.Interp(f) == b
  }

  lemma rep_unit()
  //ensures rep(unit(), Base.unit())
  {
    SE.interp_unit();
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
    b' := b;

    var x, y, z :|
      && SE.dot_defined(x, z)
      && SE.dot_defined(y, z)
      && f == SE.dot(x, z)
      && f' == SE.dot(y, z)
      && SE.InternalNext(x, y);

    SE_assoc_general(x, z, p);
    SE_assoc_general(y, z, p);

    SE.internal_step_preserves_interp(SE.dot(z, p), x, y);
    assert Base.reachable(b, b);
    transition_is_monotonic(f, f', p);
    assert dot_defined(f', p);
    assert rep(dot(f', p), b);
  }
}

abstract module SimpleExtToken {
  import SEPCM = SimpleExtPCM

  type Token = SEPCM.Token
  import SE = SEPCM.SE
  import Base = SE.Base

  type F = SEPCM.SE.F

  function method {:opaque} init(glinear b: Base.Token, ghost f': F) : (glinear f_out: Token)
  requires SE.Inv(f')
  requires SE.Interp(f') == b.get()
  ensures f_out.loc().ExtLoc? && f_out.loc().base_loc == b.loc()
  ensures f_out.get() == f'
  {
    SE.dot_unit(f');
    SEPCM.ext_init(b, f')
  }

  glinear method do_internal_step(glinear f: Token, ghost f': F)
  returns (glinear f_out: Token)
  requires SE.InternalNext(f.get(), f')
  ensures f_out.loc() == f.loc()
  ensures f_out.get() == f'
  {
    gshared var u := SEPCM.get_unit_shared(f.loc());
    SE.dot_unit(f');
    SE.dot_unit(f.get());
    SE.commutative(f', u.get());
    SE.commutative(f.get(), u.get());

    ghost var a :| SE.dot_defined(f.get(), a) && SE.Inv(SE.dot(f.get(), a));
    SE.internal_step_preserves_interp(a, f.get(), f');

    f_out := SEPCM.transition_update(u, f, f');
  }

  glinear method do_cross_step(
      glinear f: Token, ghost f': F,
      glinear b: Base.Token, ghost b': Base.M)
  returns (glinear f_out: Token, glinear b_out: Base.Token)
  requires SE.CrossNext(f.get(), f', b.get(), b')
  requires f.loc().ExtLoc? && f.loc().base_loc == b.loc()
  ensures f_out.loc() == f.loc()
  ensures b_out.loc() == b.loc()
  ensures f_out.get() == f'
  ensures b_out.get() == b'
  {
    forall p: SEPCM.M, q: Base.M | SEPCM.dot_defined(f.get(), p)
        && SEPCM.rep(SEPCM.dot(f.get(), p), q) && Base.dot_defined(q, b.get())
    ensures exists q' ::
      SEPCM.dot_defined(f', p) &&
      SEPCM.rep(SEPCM.dot(f', p), q') &&
      Base.dot_defined(q', b') &&
      Base.reachable(Base.dot(q, b.get()), Base.dot(q', b'))
    {
      SE.cross_step_preserves_interp(p, f.get(), f', b.get(), b');

      //SEPCM.SE_assoc_general(f.get(), p, b.get());
      //SEPCM.SE_assoc_general(f', p, b');

      SE.dot_unit(SE.dot(f', p));
      assert SE.Inv(SE.dot(SE.dot(f', p), SE.unit()));
      assert SEPCM.Valid(SE.dot(f', p));

      var q' := SE.Interp(SEPCM.dot(f', p));

      assert SEPCM.dot_defined(f', p);
      assert SEPCM.rep(SEPCM.dot(f', p), q');
      assert Base.dot_defined(q', b');
      assert Base.reachable(Base.dot(q, b.get()), Base.dot(q', b'));
    }

    /*assert SEPCM.Valid(f.get());
    ghost var a :| SE.dot_defined(f.get(), a) && SE.Inv(SE.dot(f.get(), a));*/
    gshared var u := SEPCM.get_unit_shared(f.loc());
    SE.dot_unit(f.get());
    SE.commutative(f.get(), u.get());
    glinear var f1 := f;
    glinear var b1 := b;
    ghost var a, interp := SEPCM.exists_whole(u, inout f1, inout b1);
    SE.cross_step_preserves_interp(a, f.get(), f', b.get(), b');

    f_out, b_out := SEPCM.ext_transfer(f1, f', b1, b');
  }
}
