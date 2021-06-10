include "SimpleExtPCM.i.dfy"

abstract module SimpleExtToken {
  import SEPCM : SimpleExtPCM

  type Token = SEPCM.Token
  //import SE = SEPCM.SE
  import Base = RWLockBase

  type F = SEPCM.SE.F

  function method {:opaque} init(glinear b: Base.Token, ghost f': F) : (glinear f_out: Token)
  requires SEPCM.SE.Inv(f')
  requires SEPCM.SE.Interp(f') == b.val
  ensures f_out.loc.ExtLoc? && f_out.loc.base_loc == b.loc
  ensures f_out.val == f'
  {
    SEPCM.SE.dot_unit(f');
    SEPCM.ext_init(b, f')
  }

  glinear method do_internal_step(glinear f: Token, ghost f': F)
  returns (glinear f_out: Token)
  requires SEPCM.SE.InternalNext(f.val, f')
  ensures f_out.loc == f.loc
  ensures f_out.val == f'
  {
    gshared var u := SEPCM.get_unit_shared(f.loc);
    SEPCM.SE.dot_unit(f');
    SEPCM.SE.dot_unit(f.val);
    SEPCM.SE.commutative(f', u.val);
    SEPCM.SE.commutative(f.val, u.val);

    ghost var a :| SEPCM.SE.dot_defined(f.val, a) && SEPCM.SE.Inv(SEPCM.SE.dot(f.val, a));
    SEPCM.SE.internal_step_preserves_interp(a, f.val, f');

    f_out := SEPCM.transition_update(u, f, f');
  }

  glinear method do_cross_step(
      glinear f: Token, ghost f': F,
      glinear b: Base.Token, ghost b': Base.M)
  returns (glinear f_out: Token, glinear b_out: Base.Token)
  requires SEPCM.SE.CrossNext(f.val, f', b.val, b')
  requires f.loc.ExtLoc? && f.loc.base_loc == b.loc
  ensures f_out.loc == f.loc
  ensures b_out.loc == b.loc
  ensures f_out.val == f'
  ensures b_out.val == b'
  {
    forall p: SEPCM.M, q: Base.M | SEPCM.dot_defined(f.val, p)
        && SEPCM.rep(SEPCM.dot(f.val, p), q) && Base.dot_defined(q, b.val)
    ensures exists q' ::
      SEPCM.dot_defined(f', p) &&
      SEPCM.rep(SEPCM.dot(f', p), q') &&
      Base.dot_defined(q', b') &&
      Base.reachable(Base.dot(q, b.val), Base.dot(q', b'))
    {
      SEPCM.SE.cross_step_preserves_interp(p, f.val, f', b.val, b');

      //SEPCM.SE_assoc_general(f.val, p, b.val);
      //SEPCM.SE_assoc_general(f', p, b');

      SEPCM.SE.dot_unit(SEPCM.SE.dot(f', p));
      assert SEPCM.SE.Inv(SEPCM.SE.dot(SEPCM.SE.dot(f', p), SEPCM.SE.unit()));
      assert SEPCM.Valid(SEPCM.SE.dot(f', p));

      var q' := SEPCM.SE.Interp(SEPCM.dot(f', p));

      assert SEPCM.dot_defined(f', p);
      assert SEPCM.rep(SEPCM.dot(f', p), q');
      assert Base.dot_defined(q', b');
      assert Base.reachable(Base.dot(q, b.val), Base.dot(q', b'));
    }

    /*assert SEPCM.Valid(f.val);
    ghost var a :| SEPCM.SE.dot_defined(f.val, a) && SEPCM.SE.Inv(SEPCM.SE.dot(f.val, a));*/
    gshared var u := SEPCM.get_unit_shared(f.loc);
    SEPCM.SE.dot_unit(f.val);
    SEPCM.SE.commutative(f.val, u.val);
    glinear var f1 := f;
    glinear var b1 := b;
    ghost var a, interp := SEPCM.exists_whole(u, inout f1, inout b1);
    SEPCM.SE.cross_step_preserves_interp(a, f.val, f', b.val, b');

    f_out, b_out := SEPCM.ext_transfer(f1, f', b1, b');
  }

  glinear method {:extern} split(glinear sum: Token, ghost a: F, ghost b: F)
  returns (glinear a': Token, glinear b': Token)
  requires SEPCM.SE.dot_defined(a, b)
  requires sum.val == SEPCM.SE.dot(a, b)
  ensures a'.val == a && a'.loc == sum.loc
  ensures b'.val == b && b'.loc == sum.loc
  {
    assert SEPCM.Valid(sum.val);
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
  ensures SEPCM.SE.dot_defined(t.val, a)
  ensures SEPCM.SE.dot(t.val, a) == complete
  ensures SEPCM.SE.Inv(complete)
  {
    assert SEPCM.Valid(t.val);
    ghost var x :| SEPCM.SE.dot_defined(t.val, x) && SEPCM.SE.Inv(SEPCM.SE.dot(t.val, x));
    a := x;
    complete := SEPCM.SE.dot(t.val, a);
  }

  function method {:opaque} borrow_back(gshared f: Token, ghost b: Base.M)
        : (gshared b_out: Base.Token)
  requires f.loc.ExtLoc?
  requires forall p ::
      SEPCM.SE.dot_defined(f.val, p) && SEPCM.SE.Inv(SEPCM.SE.dot(f.val, p))
          ==> Base.le(b, SEPCM.SE.Interp(SEPCM.SE.dot(f.val, p)))
  ensures b_out.val == b
  ensures b_out.loc == f.loc.base_loc
  {
    assert forall p, b1 ::
      SEPCM.dot_defined(f.val, p) && SEPCM.rep(SEPCM.dot(f.val, p), b1) ==> Base.le(b, b1) by {
      /*forall p, b1
        | SEPCM.dot_defined(f.val, p) && SEPCM.rep(SEPCM.dot(f.val, p), b1)
      ensures Base.le(b, b1)
      {
      }*/
    }
    SEPCM.borrow_back(f, b)
  }

  function method {:opaque} borrow_back_interp_exact(gshared f: Token, ghost b: Base.M)
        : (gshared b_out: Base.Token)
  requires f.loc.ExtLoc?
  requires forall p ::
      SEPCM.SE.dot_defined(f.val, p) && SEPCM.SE.Inv(SEPCM.SE.dot(f.val, p))
          ==> b == SEPCM.SE.Interp(SEPCM.SE.dot(f.val, p))
  ensures b_out.val == b
  ensures b_out.loc == f.loc.base_loc
  {
    assert forall p ::
      SEPCM.SE.dot_defined(f.val, p) && SEPCM.SE.Inv(SEPCM.SE.dot(f.val, p))
          ==> Base.le(b, SEPCM.SE.Interp(SEPCM.SE.dot(f.val, p))) by {
      forall p |
        SEPCM.SE.dot_defined(f.val, p) && SEPCM.SE.Inv(SEPCM.SE.dot(f.val, p))
      ensures Base.le(b, SEPCM.SE.Interp(SEPCM.SE.dot(f.val, p)))
      {
        Base.dot_unit(SEPCM.SE.Interp(SEPCM.SE.dot(f.val, p)));
        Base.commutative(SEPCM.SE.Interp(SEPCM.SE.dot(f.val, p)), Base.unit());
      }
    }
    borrow_back(f, b)
  }
}
