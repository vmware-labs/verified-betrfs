include "../../../lib/Lang/NativeTypes.s.dfy"
include "../../../lib/Base/Option.s.dfy"
include "ConcurrencyModel.s.dfy"
include "AppSpec.s.dfy"

module Limits {
  import opened NativeTypes

  function method FixedSize() : (n: nat)
    ensures 1 < n < 0x100000000

  function Capacity() : (n: nat)
  {
    FixedSize() - 1
  }

  function method FixedSizeImpl() : (n: uint32)
    ensures n as int == FixedSize()

  function method CapacityImpl(): (s: uint32)
    ensures s as nat == Capacity()
}

