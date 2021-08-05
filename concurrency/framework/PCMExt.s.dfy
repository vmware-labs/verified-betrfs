include "PCM.s.dfy"
include "../../lib/Base/Option.s.dfy"

abstract module PCMExt(base: PCM) refines PCM {
  import opened Options

  type B = base.M
  type F = M

  function I(f: F) : Option<B>

  lemma I_unit()
  ensures I(unit()) == Some(base.unit())

  lemma I_respects_transitions(f: F, f': F)
  requires transition(f, f')
  requires I(f).Some?
  ensures I(f').Some?
  ensures base.transition(I(f).value, I(f').value)

  lemma I_valid(f: F)
  requires I(f).Some?
  ensures valid(f)
}

module ExtTokens(base: PCM, ext: PCMExt(base)) {
  import opened Options

  import ExtTokens = Tokens(ext)
  import BaseTokens = Tokens(base)

  // TODO version that could accept `gshared f`
  // (Remember there is NO SOUND VERSION that accepts `gshared b`)

  function method {:extern} ext_init(
      glinear b: BaseTokens.Token,
      ghost f': ext.F)
   : (glinear f_out: ExtTokens.Token)
  requires ext.I(f') == Some(b.val)
  ensures f_out.loc.ExtLoc? && f_out.loc.base_loc == b.loc
  ensures f_out.val == f'

  glinear method {:extern} ext_transfer(
      glinear f: ExtTokens.Token,
      ghost f': ext.F,
      glinear m: BaseTokens.Token,
      ghost m': base.M)
  returns (glinear f_out: ExtTokens.Token, glinear m_out: BaseTokens.Token)
  requires f.loc.ExtLoc? && f.loc.base_loc == m.loc
  requires forall p ::
          ext.I(ext.dot(f.val, p)).Some?
            && base.valid(base.dot(m.val, ext.I(ext.dot(f.val, p)).value))
      ==> ext.I(ext.dot(f', p)).Some?
          && base.transition(
              base.dot(m.val, ext.I(ext.dot(f.val, p)).value),
              base.dot(m', ext.I(ext.dot(f', p)).value))
  ensures f_out == ExtTokens.Token(f.loc, f')
  ensures m_out == BaseTokens.Token(m.loc, m')

  function method {:extern} borrow_back(gshared f: ExtTokens.Token, ghost b: base.M)
    : (gshared b_out: BaseTokens.Token)
  requires f.loc.ExtLoc?
  requires forall p ::
      ext.I(ext.dot(f.val, p)).Some? ==> base.le(b, ext.I(ext.dot(f.val, p)).value)

  ensures b_out == BaseTokens.Token(f.loc.base_loc, b)

  glinear method {:extern} exists_whole(
      gshared s: ExtTokens.Token,
      glinear inout f: ExtTokens.Token,
      glinear inout b: BaseTokens.Token)
  returns (ghost res: ext.M, ghost b': ext.M)
  requires s.loc == old_f.loc
  requires s.loc.ExtLoc? && s.loc.base_loc == old_b.loc
  ensures f == old_f
  ensures b == old_b
  ensures ext.I(ext.dot(ext.dot(s.val, f.val), res)).Some?
  ensures base.valid(base.dot(
    ext.I(ext.dot(ext.dot(s.val, f.val), res)).value,
    b.val))
}
