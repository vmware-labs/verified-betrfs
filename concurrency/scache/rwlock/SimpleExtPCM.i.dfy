include "Ext.i.dfy"

abstract module SimpleExtPCM refines PCMExt {
  import SE : SimpleExt
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
      assert SE.dot_defined(SE.unit(), SE.unit());
      assert SE.Inv(SE.dot(SE.unit(), SE.unit()));
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
