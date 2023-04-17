// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module GhostLoc {
  datatype Loc =
    | BaseLoc(ghost t: nat)
    | ExtLoc(ghost s: nat, ghost base_loc: Loc)
}
abstract module PCM {
  import opened GhostLoc
  type M(!new)
}
module Tokens(pcm: PCM) {
  import opened GhostLoc
  datatype Token = Token(loc: Loc, val: pcm.M)
}
abstract module PCMExt(Base: PCM) refines PCM {
  type B = Base.M
  type F = M
}
module PCMExtMethods(Base: PCM, Ext: PCMExt(Base)) {
  type B = Base.M
  type F = Ext.M
  import BaseTokens = Tokens(Base)
  import ExtTokens = Tokens(Ext)
  function method {:extern} ext_init(
      linear b: BaseTokens.Token,
      ghost f': F)
   : (linear f_out: ExtTokens.Token)
  ensures f_out.loc.ExtLoc? && f_out.loc.base_loc == b.loc
  ensures f_out.val == f'
}
