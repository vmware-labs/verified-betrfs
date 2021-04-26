include "PCM.s.dfy"

abstract module PCMExt refines PCM {
  import Base : PCM

  type B = Base.M
  type F = M

  predicate rep(f: F, b: B)

  lemma rep_unit()
  ensures rep(unit(), Base.unit())

  lemma rep_equiv(f: F, b: B, b': B)
  requires rep(f, b)
  requires rep(f, b')
  ensures Base.reachable(b, b')

  lemma rep_trans(f: F, f': F, p: F, b: B)
  returns (b': B)
  requires dot_defined(f, p) && rep(dot(f, p), b)
  requires transition(f, f')
  ensures Base.reachable(b, b')
  ensures dot_defined(f', p) && rep(dot(f', p), b')

  function method {:extern} ext_init(
      glinear b: Base.Token,
      ghost f': F)
   : (glinear f_out: Token)
  requires rep(f', b.get())
  ensures f_out.loc().ExtLoc? && f_out.loc().l == b.loc()
  ensures f_out.get() == f'

  // TODO version that could accept a `gshared f`
  // (Remember there is NO SOUND VERSION that accepts a `gshared b`)

  glinear method {:extern} ext_transfer(
      glinear f: Token,
      glinear b: Base.Token,
      ghost f': F,
      ghost b': B)
  returns (glinear f_out: Token, glinear b_out: Base.Token)
  requires f.loc().ExtLoc? && f.loc().l == b.loc()
  requires forall p, q :: dot_defined(f.get(), p) && rep(dot(f.get(), p), q) && Base.dot_defined(b.get(), q) ==>
    exists q' ::
      dot_defined(f', p) &&
      rep(dot(f', p), q') &&
      Base.dot_defined(b', q') &&
      Base.reachable(Base.dot(b.get(), q), Base.dot(b', q'))
  ensures f_out.loc() == f.loc()
  ensures b_out.loc() == b.loc()
  ensures f_out.get() == f'
  ensures b_out.get() == b'
}
