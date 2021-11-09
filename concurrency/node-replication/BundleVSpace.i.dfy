include "Init.i.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"

include "ConcreteVSpaceReplica.i.dfy"
import M = Init(VSpaceIfc)


// Create an extra RwLock just for C++ microbenchmarks.
module Uint64ContentsTypeMod refines ContentsTypeMod {
  import opened NativeTypes
  type ContentsType = uint64
}

import RwLockImplBool = RwLockImpl(Uint64ContentsTypeMod)
