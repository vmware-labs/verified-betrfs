include "Init.i.dfy"
include "ConcreteReplica.i.dfy"

import M = Init(CounterIfc)

// Create an extra RwLock just for C++ microbenchmarks.
module BoolContentsTypeMod refines ContentsTypeMod {
  type ContentsType = bool
}

import RwLockImplBool = RwLockImpl(BoolContentsTypeMod)
