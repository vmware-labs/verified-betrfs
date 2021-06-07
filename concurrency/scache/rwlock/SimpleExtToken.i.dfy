include "SimpleExtPCM.i.dfy"

abstract module SimpleExtToken {
  import SEPCM : SimpleExtPCM

  type Token = SEPCM.Token
  //import SE = SEPCM.SE
  import Base = RWLockBase

  type F = SEPCM.SE.F

  function method {:opaque} init(glinear b: Base.Token, ghost f': F) : (glinear f_out: Token)
  requires SEPCM.SE.Inv(f')
  requires SEPCM.SE.Interp(f') == b.get()
  ensures f_out.loc().ExtLoc? && f_out.loc().base_loc == b.loc()
  ensures f_out.get() == f'
  {
    SEPCM.SE.dot_unit(f');
    SEPCM.ext_init(b, f')
  }

  glinear method do_internal_step(glinear f: Token, ghost f': F)
  returns (glinear f_out: Token)
  requires SEPCM.SE.InternalNext(f.get(), f')
  ensures f_out.loc() == f.loc()
  ensures f_out.get() == f'
  {
    gshared var u := SEPCM.get_unit_shared(f.loc());
    SEPCM.SE.dot_unit(f');
    SEPCM.SE.dot_unit(f.get());
    SEPCM.SE.commutative(f', u.get());
    SEPCM.SE.commutative(f.get(), u.get());

    ghost var a :| SEPCM.SE.dot_defined(f.get(), a) && SEPCM.SE.Inv(SEPCM.SE.dot(f.get(), a));
    SEPCM.SE.internal_step_preserves_interp(a, f.get(), f');

    f_out := SEPCM.transition_update(u, f, f');
  }

  glinear method do_cross_step(
      glinear f: Token, ghost f': F,
      glinear b: Base.Token, ghost b': Base.M)
  returns (glinear f_out: Token, glinear b_out: Base.Token)
  requires SEPCM.SE.CrossNext(f.get(), f', b.get(), b')
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
      SEPCM.SE.cross_step_preserves_interp(p, f.get(), f', b.get(), b');

      //SEPCM.SE_assoc_general(f.get(), p, b.get());
      //SEPCM.SE_assoc_general(f', p, b');

      SEPCM.SE.dot_unit(SEPCM.SE.dot(f', p));
      assert SEPCM.SE.Inv(SEPCM.SE.dot(SEPCM.SE.dot(f', p), SEPCM.SE.unit()));
      assert SEPCM.Valid(SEPCM.SE.dot(f', p));

      var q' := SEPCM.SE.Interp(SEPCM.dot(f', p));

      assert SEPCM.dot_defined(f', p);
      assert SEPCM.rep(SEPCM.dot(f', p), q');
      assert Base.dot_defined(q', b');
      assert Base.reachable(Base.dot(q, b.get()), Base.dot(q', b'));
    }

    /*assert SEPCM.Valid(f.get());
    ghost var a :| SEPCM.SE.dot_defined(f.get(), a) && SEPCM.SE.Inv(SEPCM.SE.dot(f.get(), a));*/
    gshared var u := SEPCM.get_unit_shared(f.loc());
    SEPCM.SE.dot_unit(f.get());
    SEPCM.SE.commutative(f.get(), u.get());
    glinear var f1 := f;
    glinear var b1 := b;
    ghost var a, interp := SEPCM.exists_whole(u, inout f1, inout b1);
    SEPCM.SE.cross_step_preserves_interp(a, f.get(), f', b.get(), b');

    f_out, b_out := SEPCM.ext_transfer(f1, f', b1, b');
  }

  glinear method {:extern} split(glinear sum: Token, ghost a: F, ghost b: F)
  returns (glinear a': Token, glinear b': Token)
  requires SEPCM.SE.dot_defined(a, b)
  requires sum.get() == SEPCM.SE.dot(a, b)
  ensures a'.get() == a && a'.loc() == sum.loc()
  ensures b'.get() == b && b'.loc() == sum.loc()
  {
    assert SEPCM.Valid(sum.get());
    assert SEPCM.Valid(SEPCM.SE.dot(a, b));

    ghost var x :| SEPCM.SE.dot_defined(SEPCM.SE.dot(a, b), x)
        && SEPCM.SE.Inv(SEPCM.SE.dot(SEPCM.SE.dot(a, b), x));
    SEPCM.SE.commutative(a, b);
    SEPCM.SE_assoc_general(a, b, x);
    SEPCM.SE_assoc_general(b, a, x);

    assert SEPCM.dot_defined(a, b);
    a', b' := SEPCM.split(sum, a, b);
  }

  glinear method get_completion(glinear inout t: Token)
  returns (ghost a: F, ghost complete: F)
  ensures t == old_t
  ensures SEPCM.SE.dot_defined(t.get(), a)
  ensures SEPCM.SE.dot(t.get(), a) == complete
  ensures SEPCM.SE.Inv(complete)
  {
    assert SEPCM.Valid(t.get());
    ghost var x :| SEPCM.SE.dot_defined(t.get(), x) && SEPCM.SE.Inv(SEPCM.SE.dot(t.get(), x));
    a := x;
    complete := SEPCM.SE.dot(t.get(), a);
  }

  function method {:opaque} borrow_back(gshared f: Token, ghost b: Base.M)
        : (gshared b_out: Base.Token)
  requires f.loc().ExtLoc?
  requires forall p ::
      SEPCM.SE.dot_defined(f.get(), p) && SEPCM.SE.Inv(SEPCM.SE.dot(f.get(), p))
          ==> Base.le(b, SEPCM.SE.Interp(SEPCM.SE.dot(f.get(), p)))
  ensures b_out.get() == b
  ensures b_out.loc() == f.loc().base_loc
  {
    assert forall p, b1 ::
      SEPCM.dot_defined(f.get(), p) && SEPCM.rep(SEPCM.dot(f.get(), p), b1) ==> Base.le(b, b1) by {
      /*forall p, b1
        | SEPCM.dot_defined(f.get(), p) && SEPCM.rep(SEPCM.dot(f.get(), p), b1)
      ensures Base.le(b, b1)
      {
      }*/
    }
    SEPCM.borrow_back(f, b)
  }

  function method {:opaque} borrow_back_interp_exact(gshared f: Token, ghost b: Base.M)
        : (gshared b_out: Base.Token)
  requires f.loc().ExtLoc?
  requires forall p ::
      SEPCM.SE.dot_defined(f.get(), p) && SEPCM.SE.Inv(SEPCM.SE.dot(f.get(), p))
          ==> b == SEPCM.SE.Interp(SEPCM.SE.dot(f.get(), p))
  ensures b_out.get() == b
  ensures b_out.loc() == f.loc().base_loc
  {
    assert forall p ::
      SEPCM.SE.dot_defined(f.get(), p) && SEPCM.SE.Inv(SEPCM.SE.dot(f.get(), p))
          ==> Base.le(b, SEPCM.SE.Interp(SEPCM.SE.dot(f.get(), p))) by {
      forall p |
        SEPCM.SE.dot_defined(f.get(), p) && SEPCM.SE.Inv(SEPCM.SE.dot(f.get(), p))
      ensures Base.le(b, SEPCM.SE.Interp(SEPCM.SE.dot(f.get(), p)))
      {
        Base.dot_unit(SEPCM.SE.Interp(SEPCM.SE.dot(f.get(), p)));
        Base.commutative(SEPCM.SE.Interp(SEPCM.SE.dot(f.get(), p)), Base.unit());
      }
    }
    borrow_back(f, b)
  }
}
