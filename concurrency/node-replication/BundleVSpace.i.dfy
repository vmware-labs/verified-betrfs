include "Init.i.dfy"
include "../../lib/Lang/NativeTypes.s.dfy"
include "Linearize.i.dfy"
include "InfiniteLog_Refines_NRSimple.i.dfy"

include "ConcreteVSpaceReplica.i.dfy"
import M = Init(VSpaceIfc)


// Create an extra RwLock just for C++ microbenchmarks.
module VSpaceContentsTypeMod refines ContentsTypeMod {
  import opened VSpaceStruct
  type ContentsType = VSpacePtr
}

import RwLockImplBool = RwLockImpl(VSpaceContentsTypeMod)
