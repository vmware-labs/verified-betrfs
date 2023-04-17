// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module PCM {
}

abstract module BasicPCM refines PCM {
}

module Tokens(pcm: PCM) {
  datatype Token = Token()

  function method get_unit() : Token
}

abstract module PCMExt(base: PCM) refines PCM {
}

abstract module PCMWrap refines PCM {
}

module PCMWrapTokens(pcm: PCMWrap) {
  import T = Tokens(pcm)
}

module ExtTokens(base: PCM, ext: PCMExt(base)) {
  import ExtTokens = Tokens(ext)
  import BaseTokens = Tokens(base) // = Tokens(Wrap) == Tokens(RW_PCMWrap(rw))

  function method ext_init(b: BaseTokens.Token) : (f_out: ExtTokens.Token)
}

abstract module RW {
}

module RW_PCMWrap(rw: RW) refines PCMWrap {
}

module RW_PCMExt(rw: RW) refines PCMExt(RW_PCMWrap(rw)) {
}

module RWTokens(rw: RW) {
  import Wrap = RW_PCMWrap(rw)
  import MyBaseTokens = Tokens(RW_PCMWrap(rw))

  import T = Tokens(RW_PCMExt(rw))
  import ET = ExtTokens(Wrap, RW_PCMExt(rw))

  method init() returns (t: T.Token) {
    var r := ET.ext_init(MyBaseTokens.get_unit());
    t := r;
  }
}
