// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module PCM {
  type M
}

module Tokens(pcm: PCM) {
  datatype Token = Token(loc: nat, val: pcm.M)
}

abstract module PCMExt(base: PCM) refines PCM {
}

abstract module PCMWrap refines PCM {
}

abstract module RW {
  type M
}

module RW_PCMWrap(rw: RW) refines PCMWrap {
}

module RW_PCMExt(rw: RW) refines PCMExt(RW_PCMWrap(rw)) {
  type M = rw.M
}

module RWTokens(rw: RW) {
  import T1 = Tokens(RW_PCMExt(rw))

  method init(x: rw.M)
  returns (t: T1.Token)
  ensures t.val == x // type error is on this line
}

module Y refines RW {
}

module X {
  import T2 = RWTokens(Y)  // but type error only occurs if this import exists
}
