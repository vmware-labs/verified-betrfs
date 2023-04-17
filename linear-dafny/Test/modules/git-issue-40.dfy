// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module PCM {
  type M
}
abstract module TicketStubSSM {
  type M(!new)
  predicate Internal(shard: M)
}
module TicketStubPCM(ssm: TicketStubSSM) refines PCM {
  type M = ssm.M
}
module Tokens(pcm: PCM) {
    datatype Token = Token(ghost val: pcm.M)
}
module TicketStubToken(ssm: TicketStubSSM) {
  import pcm = TicketStubPCM(ssm)
  import Tokens = Tokens(pcm)
  //import Tokens = Tokens(TicketStubPCM(ssm))    // Worked when done this way
  type Token = Tokens.Token
  function method {:opaque} update_next(a: Token) : int
    requires ssm.Internal(a.val)
}
module SSM refines TicketStubSSM {
}
module test {
  import Token = TicketStubToken(SSM)
}
