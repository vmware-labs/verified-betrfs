// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module Rw { }

module RwTokens(rw: Rw) {
  datatype Token = Tok
}

abstract module StoredTypeModule { }

module RwLock(stm: StoredTypeModule) refines Rw { }

module RwLockTokens(stm: StoredTypeModule) {
  import rwlock = RwLock(stm)
  import T1 = RwTokens(RwLock(stm))

  type Token = T1.Token
}

module RwLockImpl(stm: StoredTypeModule) {
  import rwlock = RwLock(stm)
  import T2 = RwLockTokens(stm)

  type Token = T2.Token
}
