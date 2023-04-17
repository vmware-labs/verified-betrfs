// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module SSM {  }
abstract module PCM {  }

module Tokens(pcm: PCM) { }

module SSM_PCM(ssm: SSM) refines PCM {  }

module SSMTokens(ssm: SSM) {
  import Tokens = Tokens(SSM_PCM) // ERROR: SSM_PCM requires an argument
}
