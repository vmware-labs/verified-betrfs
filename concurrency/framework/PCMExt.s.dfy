include "PCM.s.dfy"

abstract module PCMExt(Base: PCM) refines PCM {
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
}

module PCMExtMethods(Base: PCM, Ext: PCMExt(Base)) {
  type B = Base.M
  type F = Ext.M

  import BaseTokens = Tokens(Base)
  import ExtTokens = Tokens(Ext)

  function method {:extern} ext_init(
      glinear b: BaseTokens.Token,
      ghost f': F)
   : (glinear f_out: ExtTokens.Token)
  requires Ext.rep(f', b.get())
  ensures f_out.loc().ExtLoc? && f_out.loc().base_loc == b.loc()
  ensures f_out.get() == f'

  // TODO version that could accept a `gshared f`
  // (Remember there is NO SOUND VERSION that accepts a `gshared b`)

  glinear method {:extern} ext_transfer(
      glinear f: ExtTokens.Token,
      ghost f': F,
      glinear b: BaseTokens.Token,
      ghost b': B)
  returns (glinear f_out: ExtTokens.Token, glinear b_out: BaseTokens.Token)
  requires f.loc().ExtLoc? && f.loc().base_loc == b.loc()
  requires forall p, q :: Ext.dot_defined(f.get(), p) && Ext.rep(Ext.dot(f.get(), p), q) && Base.dot_defined(q, b.get()) ==>
    exists q' ::
      Ext.dot_defined(f', p) &&
      Ext.rep(Ext.dot(f', p), q') &&
      Base.dot_defined(q', b') &&
      Base.reachable(Base.dot(q, b.get()), Base.dot(q', b'))
  ensures f_out.loc() == f.loc()
  ensures b_out.loc() == b.loc()
  ensures f_out.get() == f'
  ensures b_out.get() == b'

  function method {:extern} borrow_back(gshared f: ExtTokens.Token, ghost b: B)
    : (gshared b_out: BaseTokens.Token)
  requires f.loc().ExtLoc?
  requires forall p, b1 ::
      Ext.dot_defined(f.get(), p) && Ext.rep(Ext.dot(f.get(), p), b1) ==> Base.le(b, b1)
  ensures b_out.get() == b
  ensures b_out.loc() == f.loc().base_loc

  glinear method {:extern} exists_whole(
      gshared s: ExtTokens.Token,
      glinear inout f: ExtTokens.Token,
      glinear inout b: BaseTokens.Token)
  returns (ghost res: F, ghost b': Base.M)
  requires s.loc() == old_f.loc()
  requires s.loc().ExtLoc? && s.loc().base_loc == old_b.loc()
  ensures f == old_f
  ensures b == old_b
  ensures Ext.dot_defined(s.get(), f.get())
  ensures Ext.dot_defined(Ext.dot(s.get(), f.get()), res)
  ensures Ext.rep(Ext.dot(Ext.dot(s.get(), f.get()), res), b')
  ensures Base.dot_defined(b', b.get())
}
